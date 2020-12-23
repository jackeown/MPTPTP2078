%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:14 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_setfam_1(B_5),A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_8,C_9,B_10] :
      ( r1_tarski(A_8,C_9)
      | ~ r1_tarski(B_10,C_9)
      | ~ r1_tarski(A_8,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,'#skF_3')
      | ~ r1_tarski(A_11,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_16])).

tff(c_6,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_23,c_6])).

tff(c_33,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.06  
% 1.50/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.06  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.50/1.06  
% 1.50/1.06  %Foreground sorts:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Background operators:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Foreground operators:
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.50/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.50/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.50/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.50/1.06  
% 1.50/1.07  tff(f_42, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.50/1.07  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.50/1.07  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.50/1.07  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.50/1.07  tff(c_4, plain, (![B_5, A_4]: (r1_tarski(k1_setfam_1(B_5), A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.50/1.07  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.50/1.07  tff(c_16, plain, (![A_8, C_9, B_10]: (r1_tarski(A_8, C_9) | ~r1_tarski(B_10, C_9) | ~r1_tarski(A_8, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.50/1.07  tff(c_23, plain, (![A_11]: (r1_tarski(A_11, '#skF_3') | ~r1_tarski(A_11, '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_16])).
% 1.50/1.07  tff(c_6, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.50/1.07  tff(c_30, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_23, c_6])).
% 1.50/1.07  tff(c_33, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_30])).
% 1.50/1.07  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_33])).
% 1.50/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.07  
% 1.50/1.07  Inference rules
% 1.50/1.07  ----------------------
% 1.50/1.07  #Ref     : 0
% 1.62/1.07  #Sup     : 6
% 1.62/1.07  #Fact    : 0
% 1.62/1.07  #Define  : 0
% 1.62/1.07  #Split   : 0
% 1.62/1.07  #Chain   : 0
% 1.62/1.07  #Close   : 0
% 1.62/1.07  
% 1.62/1.07  Ordering : KBO
% 1.62/1.07  
% 1.62/1.07  Simplification rules
% 1.62/1.07  ----------------------
% 1.62/1.07  #Subsume      : 0
% 1.62/1.07  #Demod        : 1
% 1.62/1.07  #Tautology    : 0
% 1.62/1.07  #SimpNegUnit  : 0
% 1.62/1.07  #BackRed      : 0
% 1.62/1.07  
% 1.62/1.07  #Partial instantiations: 0
% 1.62/1.07  #Strategies tried      : 1
% 1.62/1.07  
% 1.62/1.07  Timing (in seconds)
% 1.62/1.07  ----------------------
% 1.62/1.07  Preprocessing        : 0.24
% 1.62/1.07  Parsing              : 0.13
% 1.62/1.07  CNF conversion       : 0.01
% 1.62/1.07  Main loop            : 0.08
% 1.62/1.07  Inferencing          : 0.04
% 1.62/1.07  Reduction            : 0.02
% 1.62/1.07  Demodulation         : 0.01
% 1.62/1.07  BG Simplification    : 0.01
% 1.62/1.08  Subsumption          : 0.01
% 1.62/1.08  Abstraction          : 0.00
% 1.62/1.08  MUC search           : 0.00
% 1.62/1.08  Cooper               : 0.00
% 1.62/1.08  Total                : 0.33
% 1.62/1.08  Index Insertion      : 0.00
% 1.62/1.08  Index Deletion       : 0.00
% 1.62/1.08  Index Matching       : 0.00
% 1.62/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
