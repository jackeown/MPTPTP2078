%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  42 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  75 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k3_tarski(A),B)
          & r2_hidden(C,A) )
       => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_1'(A_12,B_13),B_13)
      | r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_17])).

tff(c_12,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [C_15,B_16,A_17] :
      ( r2_hidden(C_15,B_16)
      | ~ r2_hidden(C_15,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_4',B_16)
      | ~ r1_tarski('#skF_2',B_16) ) ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    r1_tarski(k3_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_23,B_24,B_25] :
      ( r2_hidden('#skF_1'(A_23,B_24),B_25)
      | ~ r1_tarski(A_23,B_25)
      | r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_31,B_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(B_34,B_33)
      | ~ r1_tarski(A_31,B_34)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_85,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),'#skF_3')
      | ~ r1_tarski(A_35,k3_tarski('#skF_2'))
      | r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_37] :
      ( ~ r1_tarski(A_37,k3_tarski('#skF_2'))
      | r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_109,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r2_hidden(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_117,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_128,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.13  
% 1.81/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.14  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.81/1.14  
% 1.81/1.14  %Foreground sorts:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Background operators:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Foreground operators:
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.81/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.14  
% 1.81/1.15  tff(f_43, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 1.81/1.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.15  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.81/1.15  tff(c_10, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.15  tff(c_17, plain, (![A_12, B_13]: (~r2_hidden('#skF_1'(A_12, B_13), B_13) | r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.15  tff(c_22, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_17])).
% 1.81/1.15  tff(c_12, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.15  tff(c_24, plain, (![C_15, B_16, A_17]: (r2_hidden(C_15, B_16) | ~r2_hidden(C_15, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.15  tff(c_30, plain, (![B_16]: (r2_hidden('#skF_4', B_16) | ~r1_tarski('#skF_2', B_16))), inference(resolution, [status(thm)], [c_12, c_24])).
% 1.81/1.15  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.15  tff(c_14, plain, (r1_tarski(k3_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.15  tff(c_61, plain, (![A_23, B_24, B_25]: (r2_hidden('#skF_1'(A_23, B_24), B_25) | ~r1_tarski(A_23, B_25) | r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_6, c_24])).
% 1.81/1.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.15  tff(c_75, plain, (![A_31, B_32, B_33, B_34]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(B_34, B_33) | ~r1_tarski(A_31, B_34) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.81/1.15  tff(c_85, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), '#skF_3') | ~r1_tarski(A_35, k3_tarski('#skF_2')) | r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_14, c_75])).
% 1.81/1.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.15  tff(c_97, plain, (![A_37]: (~r1_tarski(A_37, k3_tarski('#skF_2')) | r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_85, c_4])).
% 1.81/1.15  tff(c_109, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r2_hidden(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_97])).
% 1.81/1.15  tff(c_117, plain, (r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_109])).
% 1.81/1.15  tff(c_128, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 1.81/1.15  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_128])).
% 1.81/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.15  
% 1.81/1.15  Inference rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Ref     : 0
% 1.81/1.15  #Sup     : 26
% 1.81/1.15  #Fact    : 0
% 1.81/1.15  #Define  : 0
% 1.81/1.15  #Split   : 2
% 1.81/1.15  #Chain   : 0
% 1.81/1.15  #Close   : 0
% 1.81/1.15  
% 1.81/1.15  Ordering : KBO
% 1.81/1.15  
% 1.81/1.15  Simplification rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Subsume      : 3
% 1.81/1.15  #Demod        : 2
% 1.81/1.15  #Tautology    : 2
% 1.81/1.15  #SimpNegUnit  : 1
% 1.81/1.15  #BackRed      : 0
% 1.81/1.15  
% 1.81/1.15  #Partial instantiations: 0
% 1.81/1.15  #Strategies tried      : 1
% 1.81/1.15  
% 1.81/1.15  Timing (in seconds)
% 1.81/1.15  ----------------------
% 1.81/1.15  Preprocessing        : 0.24
% 1.81/1.15  Parsing              : 0.14
% 1.81/1.15  CNF conversion       : 0.02
% 1.81/1.15  Main loop            : 0.16
% 1.81/1.15  Inferencing          : 0.07
% 1.81/1.15  Reduction            : 0.04
% 1.81/1.15  Demodulation         : 0.03
% 1.81/1.15  BG Simplification    : 0.01
% 1.81/1.15  Subsumption          : 0.05
% 1.81/1.15  Abstraction          : 0.01
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.43
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
