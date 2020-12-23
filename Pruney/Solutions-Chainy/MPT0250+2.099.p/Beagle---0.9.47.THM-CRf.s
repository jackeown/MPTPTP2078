%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:44 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   36 (  37 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [B_52,C_53,A_54] :
      ( r2_hidden(B_52,C_53)
      | ~ r1_tarski(k2_tarski(A_54,B_52),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_121,plain,(
    ! [B_58,A_59,B_60] : r2_hidden(B_58,k2_xboole_0(k2_tarski(A_59,B_58),B_60)) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_128,plain,(
    ! [A_10,B_60] : r2_hidden(A_10,k2_xboole_0(k1_tarski(A_10),B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_221,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_95,B_96,B_97] :
      ( r2_hidden(A_95,B_96)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_95),B_97),B_96) ) ),
    inference(resolution,[status(thm)],[c_128,c_221])).

tff(c_276,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_261])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.25  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.02/1.25  
% 2.02/1.25  %Foreground sorts:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Background operators:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Foreground operators:
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.25  
% 2.02/1.26  tff(f_63, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.02/1.26  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.02/1.26  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.02/1.26  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.02/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.26  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.26  tff(c_36, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.26  tff(c_12, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.26  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.26  tff(c_93, plain, (![B_52, C_53, A_54]: (r2_hidden(B_52, C_53) | ~r1_tarski(k2_tarski(A_54, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.26  tff(c_121, plain, (![B_58, A_59, B_60]: (r2_hidden(B_58, k2_xboole_0(k2_tarski(A_59, B_58), B_60)))), inference(resolution, [status(thm)], [c_8, c_93])).
% 2.02/1.26  tff(c_128, plain, (![A_10, B_60]: (r2_hidden(A_10, k2_xboole_0(k1_tarski(A_10), B_60)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 2.02/1.26  tff(c_221, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.26  tff(c_261, plain, (![A_95, B_96, B_97]: (r2_hidden(A_95, B_96) | ~r1_tarski(k2_xboole_0(k1_tarski(A_95), B_97), B_96))), inference(resolution, [status(thm)], [c_128, c_221])).
% 2.02/1.26  tff(c_276, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_261])).
% 2.02/1.26  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_276])).
% 2.02/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  Inference rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Ref     : 0
% 2.02/1.26  #Sup     : 55
% 2.02/1.26  #Fact    : 0
% 2.02/1.26  #Define  : 0
% 2.02/1.26  #Split   : 0
% 2.02/1.26  #Chain   : 0
% 2.02/1.26  #Close   : 0
% 2.02/1.26  
% 2.02/1.26  Ordering : KBO
% 2.02/1.26  
% 2.02/1.26  Simplification rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Subsume      : 4
% 2.02/1.26  #Demod        : 11
% 2.02/1.26  #Tautology    : 27
% 2.02/1.26  #SimpNegUnit  : 1
% 2.02/1.26  #BackRed      : 0
% 2.02/1.26  
% 2.02/1.26  #Partial instantiations: 0
% 2.02/1.26  #Strategies tried      : 1
% 2.02/1.26  
% 2.02/1.26  Timing (in seconds)
% 2.02/1.26  ----------------------
% 2.02/1.26  Preprocessing        : 0.31
% 2.02/1.26  Parsing              : 0.17
% 2.02/1.26  CNF conversion       : 0.02
% 2.02/1.26  Main loop            : 0.19
% 2.02/1.26  Inferencing          : 0.07
% 2.02/1.26  Reduction            : 0.06
% 2.02/1.26  Demodulation         : 0.05
% 2.02/1.26  BG Simplification    : 0.01
% 2.02/1.26  Subsumption          : 0.03
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.52
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
