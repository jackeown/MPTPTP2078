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
% DateTime   : Thu Dec  3 09:51:01 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_24,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(k2_tarski(A_45,B_46),C_47)
      | ~ r2_hidden(B_46,C_47)
      | ~ r2_hidden(A_45,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_125,plain,(
    ! [A_48,C_49] :
      ( r1_tarski(k1_tarski(A_48),C_49)
      | ~ r2_hidden(A_48,C_49)
      | ~ r2_hidden(A_48,C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_53,C_54] :
      ( k2_xboole_0(k1_tarski(A_53),C_54) = C_54
      | ~ r2_hidden(A_53,C_54) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_22,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_164,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_22])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.70/1.17  
% 1.70/1.17  %Foreground sorts:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Background operators:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Foreground operators:
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.70/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.17  
% 1.90/1.18  tff(f_52, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.90/1.18  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.18  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.90/1.18  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.90/1.18  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.18  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.18  tff(c_109, plain, (![A_45, B_46, C_47]: (r1_tarski(k2_tarski(A_45, B_46), C_47) | ~r2_hidden(B_46, C_47) | ~r2_hidden(A_45, C_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.18  tff(c_125, plain, (![A_48, C_49]: (r1_tarski(k1_tarski(A_48), C_49) | ~r2_hidden(A_48, C_49) | ~r2_hidden(A_48, C_49))), inference(superposition, [status(thm), theory('equality')], [c_6, c_109])).
% 1.90/1.18  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.18  tff(c_154, plain, (![A_53, C_54]: (k2_xboole_0(k1_tarski(A_53), C_54)=C_54 | ~r2_hidden(A_53, C_54))), inference(resolution, [status(thm)], [c_125, c_2])).
% 1.90/1.18  tff(c_22, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.18  tff(c_164, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_22])).
% 1.90/1.18  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_164])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 35
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 1
% 1.90/1.18  #Demod        : 1
% 1.90/1.18  #Tautology    : 22
% 1.90/1.18  #SimpNegUnit  : 0
% 1.90/1.18  #BackRed      : 0
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.91/1.18  Preprocessing        : 0.29
% 1.91/1.18  Parsing              : 0.16
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.13
% 1.91/1.18  Inferencing          : 0.06
% 1.91/1.18  Reduction            : 0.04
% 1.91/1.18  Demodulation         : 0.03
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.02
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.44
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.18  Index Matching       : 0.00
% 1.91/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
