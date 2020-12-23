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
% DateTime   : Thu Dec  3 09:52:12 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_30,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [B_35,C_36] : r1_tarski(k1_tarski(B_35),k2_tarski(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_xboole_0(A_55,C_56)
      | ~ r1_xboole_0(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_58] :
      ( r1_xboole_0(A_58,'#skF_3')
      | ~ r1_tarski(A_58,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_107,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden(A_32,B_33)
      | ~ r1_xboole_0(k1_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_18])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.19  
% 1.89/1.20  tff(f_71, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.89/1.20  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 1.89/1.20  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.89/1.20  tff(f_50, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.89/1.20  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.20  tff(c_26, plain, (![B_35, C_36]: (r1_tarski(k1_tarski(B_35), k2_tarski(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_32, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.20  tff(c_84, plain, (![A_55, C_56, B_57]: (r1_xboole_0(A_55, C_56) | ~r1_xboole_0(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.20  tff(c_88, plain, (![A_58]: (r1_xboole_0(A_58, '#skF_3') | ~r1_tarski(A_58, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_32, c_84])).
% 1.89/1.20  tff(c_107, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_26, c_88])).
% 1.89/1.20  tff(c_18, plain, (![A_32, B_33]: (~r2_hidden(A_32, B_33) | ~r1_xboole_0(k1_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.20  tff(c_126, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_107, c_18])).
% 1.89/1.20  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_126])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 21
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 0
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 0
% 1.89/1.20  #Demod        : 7
% 1.89/1.20  #Tautology    : 12
% 1.89/1.20  #SimpNegUnit  : 0
% 1.89/1.20  #BackRed      : 0
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.31
% 1.89/1.20  Parsing              : 0.16
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.11
% 1.89/1.20  Inferencing          : 0.04
% 1.89/1.20  Reduction            : 0.04
% 1.89/1.20  Demodulation         : 0.03
% 1.89/1.20  BG Simplification    : 0.02
% 1.89/1.20  Subsumption          : 0.02
% 1.89/1.20  Abstraction          : 0.01
% 1.89/1.20  MUC search           : 0.00
% 1.89/1.20  Cooper               : 0.00
% 1.89/1.20  Total                : 0.44
% 1.89/1.20  Index Insertion      : 0.00
% 1.89/1.20  Index Deletion       : 0.00
% 1.89/1.20  Index Matching       : 0.00
% 1.89/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
