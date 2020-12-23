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
% DateTime   : Thu Dec  3 09:53:24 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  32 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_70,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(k2_tarski(A_45,B_46),C_47)
      | ~ r2_hidden(B_46,C_47)
      | ~ r2_hidden(A_45,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_142,plain,(
    ! [A_53,C_54] :
      ( r1_tarski(k1_tarski(A_53),C_54)
      | ~ r2_hidden(A_53,C_54)
      | ~ r2_hidden(A_53,C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_124])).

tff(c_30,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_142,c_30])).

tff(c_153,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.92/1.25  
% 1.92/1.25  %Foreground sorts:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Background operators:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Foreground operators:
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.25  
% 1.92/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.92/1.26  tff(f_43, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.92/1.26  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.26  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.92/1.26  tff(f_52, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.92/1.26  tff(c_70, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.26  tff(c_79, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_70, c_4])).
% 1.92/1.26  tff(c_14, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.26  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.26  tff(c_124, plain, (![A_45, B_46, C_47]: (r1_tarski(k2_tarski(A_45, B_46), C_47) | ~r2_hidden(B_46, C_47) | ~r2_hidden(A_45, C_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.26  tff(c_142, plain, (![A_53, C_54]: (r1_tarski(k1_tarski(A_53), C_54) | ~r2_hidden(A_53, C_54) | ~r2_hidden(A_53, C_54))), inference(superposition, [status(thm), theory('equality')], [c_8, c_124])).
% 1.92/1.26  tff(c_30, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.26  tff(c_150, plain, (~r2_hidden('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_142, c_30])).
% 1.92/1.26  tff(c_153, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_150])).
% 1.92/1.26  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_153])).
% 1.92/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  Inference rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Ref     : 0
% 1.92/1.26  #Sup     : 27
% 1.92/1.26  #Fact    : 0
% 1.92/1.26  #Define  : 0
% 1.92/1.26  #Split   : 0
% 1.92/1.26  #Chain   : 0
% 1.92/1.26  #Close   : 0
% 1.92/1.26  
% 1.92/1.26  Ordering : KBO
% 1.92/1.26  
% 1.92/1.26  Simplification rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Subsume      : 5
% 1.92/1.26  #Demod        : 3
% 1.92/1.26  #Tautology    : 10
% 1.92/1.26  #SimpNegUnit  : 0
% 1.92/1.26  #BackRed      : 0
% 1.92/1.26  
% 1.92/1.26  #Partial instantiations: 0
% 1.92/1.26  #Strategies tried      : 1
% 1.92/1.26  
% 1.92/1.26  Timing (in seconds)
% 1.92/1.26  ----------------------
% 1.92/1.26  Preprocessing        : 0.32
% 1.92/1.26  Parsing              : 0.17
% 1.92/1.26  CNF conversion       : 0.02
% 1.92/1.26  Main loop            : 0.13
% 1.92/1.26  Inferencing          : 0.05
% 1.92/1.26  Reduction            : 0.04
% 1.92/1.26  Demodulation         : 0.03
% 1.92/1.26  BG Simplification    : 0.01
% 1.92/1.26  Subsumption          : 0.02
% 1.92/1.26  Abstraction          : 0.01
% 1.92/1.26  MUC search           : 0.00
% 1.92/1.26  Cooper               : 0.00
% 1.92/1.26  Total                : 0.48
% 1.92/1.26  Index Insertion      : 0.00
% 1.92/1.26  Index Deletion       : 0.00
% 1.92/1.26  Index Matching       : 0.00
% 1.92/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
