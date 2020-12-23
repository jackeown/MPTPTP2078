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

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k4_xboole_0(k2_tarski(A,B),C) != k1_xboole_0
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(A)
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(B)
          & k4_xboole_0(k2_tarski(A,B),C) != k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(c_22,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [B_20,C_21,A_22] :
      ( k2_tarski(B_20,C_21) = A_22
      | k1_tarski(C_21) = A_22
      | k1_tarski(B_20) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k2_tarski(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [B_27,C_28,B_29] :
      ( k4_xboole_0(k2_tarski(B_27,C_28),B_29) = k2_tarski(B_27,C_28)
      | k4_xboole_0(k2_tarski(B_27,C_28),B_29) = k1_tarski(C_28)
      | k4_xboole_0(k2_tarski(B_27,C_28),B_29) = k1_tarski(B_27)
      | k4_xboole_0(k2_tarski(B_27,C_28),B_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_56])).

tff(c_16,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_137,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_2')
    | k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_tarski('#skF_1')
    | k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_16])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_18,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:09:40 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  %$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.17  
% 1.64/1.17  %Foreground sorts:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Background operators:
% 1.64/1.17  
% 1.64/1.17  
% 1.64/1.17  %Foreground operators:
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.17  
% 1.64/1.17  tff(f_58, negated_conjecture, ~(![A, B, C]: ~(((~(k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(B))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 1.64/1.17  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.64/1.17  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 1.64/1.17  tff(c_22, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.17  tff(c_20, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.17  tff(c_18, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.17  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.17  tff(c_56, plain, (![B_20, C_21, A_22]: (k2_tarski(B_20, C_21)=A_22 | k1_tarski(C_21)=A_22 | k1_tarski(B_20)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k2_tarski(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.17  tff(c_131, plain, (![B_27, C_28, B_29]: (k4_xboole_0(k2_tarski(B_27, C_28), B_29)=k2_tarski(B_27, C_28) | k4_xboole_0(k2_tarski(B_27, C_28), B_29)=k1_tarski(C_28) | k4_xboole_0(k2_tarski(B_27, C_28), B_29)=k1_tarski(B_27) | k4_xboole_0(k2_tarski(B_27, C_28), B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_56])).
% 1.64/1.17  tff(c_16, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.17  tff(c_137, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_2') | k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_tarski('#skF_1') | k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_131, c_16])).
% 1.64/1.17  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_18, c_137])).
% 1.64/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  Inference rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Ref     : 0
% 1.64/1.17  #Sup     : 27
% 1.64/1.17  #Fact    : 4
% 1.64/1.18  #Define  : 0
% 1.64/1.18  #Split   : 0
% 1.64/1.18  #Chain   : 0
% 1.64/1.18  #Close   : 0
% 1.64/1.18  
% 1.64/1.18  Ordering : KBO
% 1.64/1.18  
% 1.64/1.18  Simplification rules
% 1.64/1.18  ----------------------
% 1.64/1.18  #Subsume      : 0
% 1.64/1.18  #Demod        : 7
% 1.64/1.18  #Tautology    : 15
% 1.64/1.18  #SimpNegUnit  : 1
% 1.64/1.18  #BackRed      : 0
% 1.64/1.18  
% 1.64/1.18  #Partial instantiations: 0
% 1.64/1.18  #Strategies tried      : 1
% 1.64/1.18  
% 1.64/1.18  Timing (in seconds)
% 1.64/1.18  ----------------------
% 1.64/1.18  Preprocessing        : 0.27
% 1.64/1.18  Parsing              : 0.14
% 1.64/1.18  CNF conversion       : 0.02
% 1.64/1.18  Main loop            : 0.13
% 1.64/1.18  Inferencing          : 0.05
% 1.64/1.18  Reduction            : 0.04
% 1.64/1.18  Demodulation         : 0.03
% 1.64/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.02
% 1.85/1.18  Abstraction          : 0.01
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.43
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
