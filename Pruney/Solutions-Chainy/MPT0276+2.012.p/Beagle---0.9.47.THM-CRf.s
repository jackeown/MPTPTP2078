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
% DateTime   : Thu Dec  3 09:53:19 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   28 (  40 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k4_xboole_0(k2_tarski(A,B),C) != k1_xboole_0
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(A)
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(B)
          & k4_xboole_0(k2_tarski(A,B),C) != k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_20,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [B_16,C_17,A_18] :
      ( k2_tarski(B_16,C_17) = A_18
      | k1_tarski(C_17) = A_18
      | k1_tarski(B_16) = A_18
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k2_tarski(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [B_19,C_20,B_21] :
      ( k4_xboole_0(k2_tarski(B_19,C_20),B_21) = k2_tarski(B_19,C_20)
      | k4_xboole_0(k2_tarski(B_19,C_20),B_21) = k1_tarski(C_20)
      | k4_xboole_0(k2_tarski(B_19,C_20),B_21) = k1_tarski(B_19)
      | k4_xboole_0(k2_tarski(B_19,C_20),B_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_14,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_2')
    | k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:22:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  %$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.20  
% 1.83/1.20  %Foreground sorts:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Background operators:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Foreground operators:
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.20  
% 1.83/1.21  tff(f_56, negated_conjecture, ~(![A, B, C]: ~(((~(k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(B))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 1.83/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.83/1.21  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 1.83/1.21  tff(c_20, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.21  tff(c_18, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.21  tff(c_16, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.21  tff(c_26, plain, (![B_16, C_17, A_18]: (k2_tarski(B_16, C_17)=A_18 | k1_tarski(C_17)=A_18 | k1_tarski(B_16)=A_18 | k1_xboole_0=A_18 | ~r1_tarski(A_18, k2_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.83/1.21  tff(c_64, plain, (![B_19, C_20, B_21]: (k4_xboole_0(k2_tarski(B_19, C_20), B_21)=k2_tarski(B_19, C_20) | k4_xboole_0(k2_tarski(B_19, C_20), B_21)=k1_tarski(C_20) | k4_xboole_0(k2_tarski(B_19, C_20), B_21)=k1_tarski(B_19) | k4_xboole_0(k2_tarski(B_19, C_20), B_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.83/1.21  tff(c_14, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.21  tff(c_70, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_2') | k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_64, c_14])).
% 1.83/1.21  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_16, c_70])).
% 1.83/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  Inference rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Ref     : 0
% 1.83/1.21  #Sup     : 12
% 1.83/1.21  #Fact    : 3
% 1.83/1.21  #Define  : 0
% 1.83/1.21  #Split   : 0
% 1.83/1.21  #Chain   : 0
% 1.83/1.21  #Close   : 0
% 1.83/1.21  
% 1.83/1.21  Ordering : KBO
% 1.83/1.21  
% 1.83/1.21  Simplification rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Subsume      : 0
% 1.83/1.21  #Demod        : 0
% 1.83/1.21  #Tautology    : 5
% 1.83/1.21  #SimpNegUnit  : 1
% 1.83/1.21  #BackRed      : 0
% 1.83/1.21  
% 1.83/1.21  #Partial instantiations: 0
% 1.83/1.21  #Strategies tried      : 1
% 1.83/1.21  
% 1.83/1.21  Timing (in seconds)
% 1.83/1.21  ----------------------
% 1.83/1.21  Preprocessing        : 0.27
% 1.83/1.21  Parsing              : 0.14
% 1.83/1.21  CNF conversion       : 0.02
% 1.83/1.21  Main loop            : 0.17
% 1.83/1.21  Inferencing          : 0.07
% 1.83/1.21  Reduction            : 0.04
% 1.83/1.21  Demodulation         : 0.03
% 1.83/1.21  BG Simplification    : 0.01
% 1.83/1.21  Subsumption          : 0.03
% 1.83/1.21  Abstraction          : 0.01
% 1.83/1.21  MUC search           : 0.00
% 1.83/1.21  Cooper               : 0.00
% 1.83/1.21  Total                : 0.47
% 1.83/1.22  Index Insertion      : 0.00
% 1.83/1.22  Index Deletion       : 0.00
% 1.83/1.22  Index Matching       : 0.00
% 1.83/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
