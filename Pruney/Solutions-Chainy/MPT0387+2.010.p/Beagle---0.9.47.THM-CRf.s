%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(c_10,plain,(
    k1_setfam_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    r2_hidden(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_setfam_1(B_5),A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [B_13,A_14] :
      ( k4_xboole_0(k1_setfam_1(B_13),A_14) = k1_xboole_0
      | ~ r2_hidden(A_14,B_13) ) ),
    inference(resolution,[status(thm)],[c_8,c_24])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_15] :
      ( k1_setfam_1(B_15) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_6])).

tff(c_53,plain,(
    k1_setfam_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:07:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.61/1.11  
% 1.61/1.11  %Foreground sorts:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Background operators:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Foreground operators:
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.61/1.11  
% 1.61/1.12  tff(f_40, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.61/1.12  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.61/1.12  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.61/1.12  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.61/1.12  tff(c_10, plain, (k1_setfam_1('#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.12  tff(c_12, plain, (r2_hidden(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.12  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k1_setfam_1(B_5), A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.12  tff(c_24, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.12  tff(c_33, plain, (![B_13, A_14]: (k4_xboole_0(k1_setfam_1(B_13), A_14)=k1_xboole_0 | ~r2_hidden(A_14, B_13))), inference(resolution, [status(thm)], [c_8, c_24])).
% 1.61/1.12  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.12  tff(c_50, plain, (![B_15]: (k1_setfam_1(B_15)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_15))), inference(superposition, [status(thm), theory('equality')], [c_33, c_6])).
% 1.61/1.12  tff(c_53, plain, (k1_setfam_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_50])).
% 1.61/1.12  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_53])).
% 1.61/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  Inference rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Ref     : 0
% 1.61/1.12  #Sup     : 9
% 1.61/1.12  #Fact    : 0
% 1.61/1.12  #Define  : 0
% 1.61/1.12  #Split   : 0
% 1.61/1.12  #Chain   : 0
% 1.61/1.12  #Close   : 0
% 1.61/1.12  
% 1.61/1.12  Ordering : KBO
% 1.61/1.12  
% 1.61/1.12  Simplification rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Subsume      : 0
% 1.61/1.12  #Demod        : 0
% 1.61/1.12  #Tautology    : 5
% 1.61/1.12  #SimpNegUnit  : 1
% 1.61/1.12  #BackRed      : 0
% 1.61/1.12  
% 1.61/1.12  #Partial instantiations: 0
% 1.61/1.12  #Strategies tried      : 1
% 1.61/1.12  
% 1.61/1.12  Timing (in seconds)
% 1.61/1.12  ----------------------
% 1.61/1.12  Preprocessing        : 0.25
% 1.61/1.12  Parsing              : 0.14
% 1.61/1.12  CNF conversion       : 0.01
% 1.61/1.12  Main loop            : 0.09
% 1.61/1.12  Inferencing          : 0.04
% 1.61/1.12  Reduction            : 0.02
% 1.61/1.12  Demodulation         : 0.01
% 1.61/1.12  BG Simplification    : 0.01
% 1.61/1.12  Subsumption          : 0.01
% 1.61/1.12  Abstraction          : 0.00
% 1.61/1.12  MUC search           : 0.00
% 1.61/1.12  Cooper               : 0.00
% 1.61/1.12  Total                : 0.36
% 1.61/1.12  Index Insertion      : 0.00
% 1.61/1.12  Index Deletion       : 0.00
% 1.61/1.12  Index Matching       : 0.00
% 1.61/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
