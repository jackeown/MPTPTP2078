%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:14 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  54 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_setfam_1(B_7),A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [C_15,B_16,A_17] :
      ( r2_hidden(C_15,B_16)
      | ~ r2_hidden(C_15,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_23,B_24,B_25] :
      ( r2_hidden('#skF_1'(A_23,B_24),B_25)
      | ~ r1_tarski(A_23,B_25)
      | r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_26,B_27,B_28,B_29] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_28)
      | ~ r1_tarski(B_29,B_28)
      | ~ r1_tarski(A_26,B_29)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_70,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),'#skF_4')
      | ~ r1_tarski(A_30,'#skF_2')
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_32] :
      ( ~ r1_tarski(A_32,'#skF_2')
      | r1_tarski(A_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_91,plain,(
    ! [B_33] :
      ( r1_tarski(k1_setfam_1(B_33),'#skF_4')
      | ~ r2_hidden('#skF_2',B_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_10,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_10])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.28  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.96/1.28  
% 1.96/1.28  %Foreground sorts:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Background operators:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Foreground operators:
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.28  
% 1.96/1.29  tff(f_43, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.96/1.29  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.96/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.96/1.29  tff(c_14, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.29  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_setfam_1(B_7), A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.29  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_28, plain, (![C_15, B_16, A_17]: (r2_hidden(C_15, B_16) | ~r2_hidden(C_15, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_51, plain, (![A_23, B_24, B_25]: (r2_hidden('#skF_1'(A_23, B_24), B_25) | ~r1_tarski(A_23, B_25) | r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_6, c_28])).
% 1.96/1.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_60, plain, (![A_26, B_27, B_28, B_29]: (r2_hidden('#skF_1'(A_26, B_27), B_28) | ~r1_tarski(B_29, B_28) | ~r1_tarski(A_26, B_29) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_51, c_2])).
% 1.96/1.29  tff(c_70, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), '#skF_4') | ~r1_tarski(A_30, '#skF_2') | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_12, c_60])).
% 1.96/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_79, plain, (![A_32]: (~r1_tarski(A_32, '#skF_2') | r1_tarski(A_32, '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_4])).
% 1.96/1.29  tff(c_91, plain, (![B_33]: (r1_tarski(k1_setfam_1(B_33), '#skF_4') | ~r2_hidden('#skF_2', B_33))), inference(resolution, [status(thm)], [c_8, c_79])).
% 1.96/1.29  tff(c_10, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.29  tff(c_98, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_91, c_10])).
% 1.96/1.29  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_98])).
% 1.96/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  Inference rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Ref     : 0
% 1.96/1.29  #Sup     : 20
% 1.96/1.29  #Fact    : 0
% 1.96/1.29  #Define  : 0
% 1.96/1.29  #Split   : 1
% 1.96/1.29  #Chain   : 0
% 1.96/1.29  #Close   : 0
% 1.96/1.29  
% 1.96/1.29  Ordering : KBO
% 1.96/1.29  
% 1.96/1.29  Simplification rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Subsume      : 2
% 1.96/1.29  #Demod        : 2
% 1.96/1.29  #Tautology    : 2
% 1.96/1.29  #SimpNegUnit  : 0
% 1.96/1.29  #BackRed      : 0
% 1.96/1.29  
% 1.96/1.29  #Partial instantiations: 0
% 1.96/1.29  #Strategies tried      : 1
% 1.96/1.29  
% 1.96/1.29  Timing (in seconds)
% 1.96/1.29  ----------------------
% 1.96/1.29  Preprocessing        : 0.29
% 1.96/1.29  Parsing              : 0.15
% 1.96/1.29  CNF conversion       : 0.02
% 1.96/1.29  Main loop            : 0.16
% 1.96/1.29  Inferencing          : 0.06
% 1.96/1.29  Reduction            : 0.03
% 1.96/1.29  Demodulation         : 0.03
% 1.96/1.29  BG Simplification    : 0.01
% 1.96/1.29  Subsumption          : 0.04
% 1.96/1.29  Abstraction          : 0.01
% 1.96/1.29  MUC search           : 0.00
% 1.96/1.29  Cooper               : 0.00
% 1.96/1.29  Total                : 0.48
% 1.96/1.29  Index Insertion      : 0.00
% 1.96/1.29  Index Deletion       : 0.00
% 1.96/1.29  Index Matching       : 0.00
% 1.96/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
