%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:12 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k1_tarski(A_6),k2_tarski(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_xboole_0(A_16,C_17)
      | ~ r1_xboole_0(B_18,C_17)
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_19] :
      ( r1_xboole_0(A_19,'#skF_3')
      | ~ r1_tarski(A_19,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_33,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden(A_8,B_9)
      | ~ r1_xboole_0(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_8])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:16:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.61/1.10  
% 1.61/1.10  %Foreground sorts:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Background operators:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Foreground operators:
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.10  
% 1.61/1.11  tff(f_46, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.61/1.11  tff(f_35, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.61/1.11  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.61/1.11  tff(f_40, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 1.61/1.11  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.11  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), k2_tarski(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.11  tff(c_12, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.11  tff(c_24, plain, (![A_16, C_17, B_18]: (r1_xboole_0(A_16, C_17) | ~r1_xboole_0(B_18, C_17) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.11  tff(c_28, plain, (![A_19]: (r1_xboole_0(A_19, '#skF_3') | ~r1_tarski(A_19, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_12, c_24])).
% 1.61/1.11  tff(c_33, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_28])).
% 1.61/1.11  tff(c_8, plain, (![A_8, B_9]: (~r2_hidden(A_8, B_9) | ~r1_xboole_0(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.11  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_33, c_8])).
% 1.61/1.11  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 1.61/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  Inference rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Ref     : 0
% 1.61/1.11  #Sup     : 6
% 1.61/1.11  #Fact    : 0
% 1.61/1.11  #Define  : 0
% 1.61/1.11  #Split   : 0
% 1.61/1.11  #Chain   : 0
% 1.61/1.11  #Close   : 0
% 1.61/1.11  
% 1.61/1.11  Ordering : KBO
% 1.61/1.11  
% 1.61/1.11  Simplification rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Subsume      : 0
% 1.61/1.11  #Demod        : 1
% 1.61/1.11  #Tautology    : 2
% 1.61/1.11  #SimpNegUnit  : 0
% 1.61/1.11  #BackRed      : 0
% 1.61/1.11  
% 1.61/1.11  #Partial instantiations: 0
% 1.61/1.11  #Strategies tried      : 1
% 1.61/1.11  
% 1.61/1.11  Timing (in seconds)
% 1.61/1.11  ----------------------
% 1.61/1.11  Preprocessing        : 0.27
% 1.61/1.11  Parsing              : 0.15
% 1.61/1.11  CNF conversion       : 0.02
% 1.61/1.11  Main loop            : 0.09
% 1.61/1.11  Inferencing          : 0.04
% 1.61/1.11  Reduction            : 0.02
% 1.61/1.11  Demodulation         : 0.02
% 1.61/1.11  BG Simplification    : 0.01
% 1.61/1.11  Subsumption          : 0.01
% 1.61/1.11  Abstraction          : 0.00
% 1.61/1.11  MUC search           : 0.00
% 1.61/1.11  Cooper               : 0.00
% 1.61/1.11  Total                : 0.39
% 1.61/1.11  Index Insertion      : 0.00
% 1.61/1.11  Index Deletion       : 0.00
% 1.61/1.11  Index Matching       : 0.00
% 1.61/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
