%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_38,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_6,plain,(
    k1_setfam_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    r2_hidden(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [B_5,A_6] :
      ( r1_tarski(k1_setfam_1(B_5),A_6)
      | ~ r2_hidden(A_6,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [B_7] :
      ( k1_setfam_1(B_7) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_2])).

tff(c_19,plain,(
    k1_setfam_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_16])).

tff(c_23,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.56/1.14  
% 1.56/1.14  %Foreground sorts:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Background operators:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Foreground operators:
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.56/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.56/1.14  
% 1.56/1.14  tff(f_38, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.56/1.14  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.56/1.14  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.56/1.14  tff(c_6, plain, (k1_setfam_1('#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.14  tff(c_8, plain, (r2_hidden(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.14  tff(c_10, plain, (![B_5, A_6]: (r1_tarski(k1_setfam_1(B_5), A_6) | ~r2_hidden(A_6, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.14  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.14  tff(c_16, plain, (![B_7]: (k1_setfam_1(B_7)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_7))), inference(resolution, [status(thm)], [c_10, c_2])).
% 1.56/1.14  tff(c_19, plain, (k1_setfam_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_16])).
% 1.56/1.14  tff(c_23, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_19])).
% 1.56/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  Inference rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Ref     : 0
% 1.56/1.14  #Sup     : 2
% 1.56/1.14  #Fact    : 0
% 1.56/1.14  #Define  : 0
% 1.56/1.14  #Split   : 0
% 1.56/1.14  #Chain   : 0
% 1.56/1.14  #Close   : 0
% 1.56/1.14  
% 1.56/1.14  Ordering : KBO
% 1.56/1.14  
% 1.56/1.14  Simplification rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Subsume      : 0
% 1.56/1.14  #Demod        : 0
% 1.56/1.14  #Tautology    : 0
% 1.56/1.14  #SimpNegUnit  : 1
% 1.56/1.14  #BackRed      : 0
% 1.56/1.14  
% 1.56/1.14  #Partial instantiations: 0
% 1.56/1.14  #Strategies tried      : 1
% 1.56/1.14  
% 1.56/1.14  Timing (in seconds)
% 1.56/1.14  ----------------------
% 1.56/1.15  Preprocessing        : 0.26
% 1.56/1.15  Parsing              : 0.14
% 1.56/1.15  CNF conversion       : 0.02
% 1.56/1.15  Main loop            : 0.07
% 1.56/1.15  Inferencing          : 0.04
% 1.56/1.15  Reduction            : 0.01
% 1.56/1.15  Demodulation         : 0.01
% 1.56/1.15  BG Simplification    : 0.01
% 1.56/1.15  Subsumption          : 0.00
% 1.56/1.15  Abstraction          : 0.00
% 1.56/1.15  MUC search           : 0.00
% 1.56/1.15  Cooper               : 0.00
% 1.56/1.15  Total                : 0.34
% 1.56/1.15  Index Insertion      : 0.00
% 1.56/1.15  Index Deletion       : 0.00
% 1.56/1.15  Index Matching       : 0.00
% 1.56/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
