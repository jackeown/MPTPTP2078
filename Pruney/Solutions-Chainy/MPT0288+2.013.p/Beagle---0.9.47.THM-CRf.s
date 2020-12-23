%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:32 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_14,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(k3_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,C_20)
      | ~ r1_tarski(B_21,C_20)
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_22] :
      ( r1_tarski(A_22,'#skF_3')
      | ~ r1_tarski(A_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_34])).

tff(c_50,plain,(
    ! [A_23] :
      ( r1_tarski(k1_tarski(A_23),'#skF_3')
      | ~ r2_hidden(A_23,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_23] :
      ( r2_hidden(A_23,'#skF_3')
      | ~ r2_hidden(A_23,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_69,plain,(
    ! [B_28] :
      ( r2_hidden('#skF_1'('#skF_2',B_28),'#skF_3')
      | r1_tarski(k3_tarski('#skF_2'),B_28) ) ),
    inference(resolution,[status(thm)],[c_64,c_57])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( ~ r1_tarski('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(k3_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k3_tarski(A_41),k3_tarski(B_42))
      | ~ r2_hidden('#skF_1'(A_41,k3_tarski(B_42)),B_42) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_127,plain,(
    r1_tarski(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_69,c_123])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_14,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
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
% 1.70/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.17  
% 1.70/1.18  tff(f_51, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.70/1.18  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.70/1.18  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.70/1.18  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.70/1.18  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.70/1.18  tff(c_14, plain, (~r1_tarski(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.18  tff(c_64, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(k3_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.18  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.18  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.18  tff(c_34, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, C_20) | ~r1_tarski(B_21, C_20) | ~r1_tarski(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.18  tff(c_44, plain, (![A_22]: (r1_tarski(A_22, '#skF_3') | ~r1_tarski(A_22, '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_34])).
% 1.70/1.18  tff(c_50, plain, (![A_23]: (r1_tarski(k1_tarski(A_23), '#skF_3') | ~r2_hidden(A_23, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_44])).
% 1.70/1.18  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.18  tff(c_57, plain, (![A_23]: (r2_hidden(A_23, '#skF_3') | ~r2_hidden(A_23, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_4])).
% 1.70/1.18  tff(c_69, plain, (![B_28]: (r2_hidden('#skF_1'('#skF_2', B_28), '#skF_3') | r1_tarski(k3_tarski('#skF_2'), B_28))), inference(resolution, [status(thm)], [c_64, c_57])).
% 1.70/1.18  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.18  tff(c_59, plain, (![A_25, B_26]: (~r1_tarski('#skF_1'(A_25, B_26), B_26) | r1_tarski(k3_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.18  tff(c_123, plain, (![A_41, B_42]: (r1_tarski(k3_tarski(A_41), k3_tarski(B_42)) | ~r2_hidden('#skF_1'(A_41, k3_tarski(B_42)), B_42))), inference(resolution, [status(thm)], [c_8, c_59])).
% 1.70/1.18  tff(c_127, plain, (r1_tarski(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_69, c_123])).
% 1.70/1.18  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_14, c_127])).
% 1.70/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.18  
% 1.70/1.18  Inference rules
% 1.70/1.18  ----------------------
% 1.70/1.18  #Ref     : 0
% 1.70/1.18  #Sup     : 26
% 1.70/1.18  #Fact    : 0
% 1.70/1.18  #Define  : 0
% 1.70/1.18  #Split   : 1
% 1.70/1.18  #Chain   : 0
% 1.70/1.18  #Close   : 0
% 1.70/1.18  
% 1.70/1.18  Ordering : KBO
% 1.70/1.18  
% 1.70/1.18  Simplification rules
% 1.70/1.18  ----------------------
% 1.70/1.18  #Subsume      : 0
% 1.70/1.18  #Demod        : 0
% 1.70/1.18  #Tautology    : 1
% 1.93/1.18  #SimpNegUnit  : 1
% 1.93/1.18  #BackRed      : 0
% 1.93/1.18  
% 1.93/1.18  #Partial instantiations: 0
% 1.93/1.18  #Strategies tried      : 1
% 1.93/1.18  
% 1.93/1.18  Timing (in seconds)
% 1.93/1.18  ----------------------
% 1.93/1.18  Preprocessing        : 0.25
% 1.93/1.18  Parsing              : 0.15
% 1.93/1.18  CNF conversion       : 0.02
% 1.93/1.18  Main loop            : 0.17
% 1.93/1.18  Inferencing          : 0.07
% 1.93/1.18  Reduction            : 0.03
% 1.93/1.18  Demodulation         : 0.02
% 1.93/1.18  BG Simplification    : 0.01
% 1.93/1.18  Subsumption          : 0.05
% 1.93/1.18  Abstraction          : 0.01
% 1.93/1.18  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.93/1.18  Total                : 0.45
% 1.93/1.18  Index Insertion      : 0.00
% 1.93/1.18  Index Deletion       : 0.00
% 1.93/1.18  Index Matching       : 0.00
% 1.93/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
