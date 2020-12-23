%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   28 (  47 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  70 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_25,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(k1_tarski(A_23),B_24) = B_24
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_10,c_25])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(k1_tarski(A_25),C_26)
      | ~ r1_tarski(B_27,C_26)
      | ~ r2_hidden(A_25,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_70,plain,(
    ! [A_28] :
      ( r1_tarski(k1_tarski(A_28),'#skF_1')
      | ~ r2_hidden(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_29] :
      ( r2_hidden(A_29,'#skF_1')
      | ~ r2_hidden(A_29,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_70,c_8])).

tff(c_86,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.48  
% 2.17/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.48  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.17/1.48  
% 2.17/1.48  %Foreground sorts:
% 2.17/1.48  
% 2.17/1.48  
% 2.17/1.48  %Background operators:
% 2.17/1.48  
% 2.17/1.48  
% 2.17/1.48  %Foreground operators:
% 2.17/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.48  
% 2.17/1.50  tff(f_48, negated_conjecture, ~(![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.17/1.50  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.17/1.50  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.17/1.50  tff(f_34, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.17/1.50  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.17/1.50  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.50  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.50  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.50  tff(c_25, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.50  tff(c_48, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), B_24)=B_24 | ~r2_hidden(A_23, B_24))), inference(resolution, [status(thm)], [c_10, c_25])).
% 2.17/1.50  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.50  tff(c_60, plain, (![A_25, C_26, B_27]: (r1_tarski(k1_tarski(A_25), C_26) | ~r1_tarski(B_27, C_26) | ~r2_hidden(A_25, B_27))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4])).
% 2.17/1.50  tff(c_70, plain, (![A_28]: (r1_tarski(k1_tarski(A_28), '#skF_1') | ~r2_hidden(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_60])).
% 2.17/1.50  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.50  tff(c_82, plain, (![A_29]: (r2_hidden(A_29, '#skF_1') | ~r2_hidden(A_29, '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_8])).
% 2.17/1.50  tff(c_86, plain, (r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_82])).
% 2.17/1.50  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.17/1.50  tff(c_100, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_2])).
% 2.17/1.50  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_100])).
% 2.17/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.50  
% 2.17/1.50  Inference rules
% 2.17/1.50  ----------------------
% 2.17/1.50  #Ref     : 0
% 2.17/1.50  #Sup     : 22
% 2.17/1.50  #Fact    : 0
% 2.17/1.50  #Define  : 0
% 2.17/1.50  #Split   : 0
% 2.17/1.50  #Chain   : 0
% 2.17/1.50  #Close   : 0
% 2.17/1.50  
% 2.17/1.50  Ordering : KBO
% 2.17/1.50  
% 2.17/1.50  Simplification rules
% 2.17/1.50  ----------------------
% 2.17/1.50  #Subsume      : 0
% 2.23/1.50  #Demod        : 1
% 2.23/1.50  #Tautology    : 5
% 2.23/1.50  #SimpNegUnit  : 0
% 2.23/1.50  #BackRed      : 0
% 2.23/1.50  
% 2.23/1.50  #Partial instantiations: 0
% 2.23/1.50  #Strategies tried      : 1
% 2.23/1.50  
% 2.23/1.50  Timing (in seconds)
% 2.23/1.50  ----------------------
% 2.23/1.51  Preprocessing        : 0.41
% 2.23/1.51  Parsing              : 0.22
% 2.23/1.51  CNF conversion       : 0.03
% 2.23/1.51  Main loop            : 0.22
% 2.23/1.51  Inferencing          : 0.09
% 2.23/1.51  Reduction            : 0.05
% 2.23/1.51  Demodulation         : 0.04
% 2.23/1.51  BG Simplification    : 0.02
% 2.23/1.51  Subsumption          : 0.05
% 2.23/1.51  Abstraction          : 0.01
% 2.23/1.51  MUC search           : 0.00
% 2.23/1.51  Cooper               : 0.00
% 2.23/1.51  Total                : 0.68
% 2.23/1.51  Index Insertion      : 0.00
% 2.23/1.51  Index Deletion       : 0.00
% 2.23/1.51  Index Matching       : 0.00
% 2.23/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
