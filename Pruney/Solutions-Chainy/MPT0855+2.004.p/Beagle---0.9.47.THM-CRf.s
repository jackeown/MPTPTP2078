%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   30 (  38 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   28 (  52 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) )
       => ( ! [D,E] : A != k4_tarski(D,E)
          | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_14,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [A_11,B_12] : k1_mcart_1(k4_tarski(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    k1_mcart_1('#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_35])).

tff(c_18,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_23,plain,(
    ! [A_9,B_10] : k2_mcart_1(k4_tarski(A_9,B_10)) = B_10 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    k2_mcart_1('#skF_1') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_23])).

tff(c_16,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_67,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( r2_hidden(k4_tarski(A_25,B_26),k2_zfmisc_1(C_27,D_28))
      | ~ r2_hidden(B_26,D_28)
      | ~ r2_hidden(A_25,C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [C_29,D_30] :
      ( r2_hidden('#skF_1',k2_zfmisc_1(C_29,D_30))
      | ~ r2_hidden('#skF_5',D_30)
      | ~ r2_hidden('#skF_4',C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_12,plain,(
    ~ r2_hidden('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_12])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_47,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.11  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.69/1.11  
% 1.69/1.11  %Foreground sorts:
% 1.69/1.11  
% 1.69/1.11  
% 1.69/1.11  %Background operators:
% 1.69/1.11  
% 1.69/1.11  
% 1.69/1.11  %Foreground operators:
% 1.69/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.69/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.69/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.11  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.69/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.69/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.11  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.69/1.11  
% 1.69/1.12  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 1.69/1.12  tff(f_35, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.69/1.12  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 1.69/1.12  tff(c_14, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.12  tff(c_35, plain, (![A_11, B_12]: (k1_mcart_1(k4_tarski(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.12  tff(c_44, plain, (k1_mcart_1('#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14, c_35])).
% 1.69/1.12  tff(c_18, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.12  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 1.69/1.12  tff(c_23, plain, (![A_9, B_10]: (k2_mcart_1(k4_tarski(A_9, B_10))=B_10)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.12  tff(c_32, plain, (k2_mcart_1('#skF_1')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_14, c_23])).
% 1.69/1.12  tff(c_16, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.12  tff(c_47, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 1.69/1.12  tff(c_67, plain, (![A_25, B_26, C_27, D_28]: (r2_hidden(k4_tarski(A_25, B_26), k2_zfmisc_1(C_27, D_28)) | ~r2_hidden(B_26, D_28) | ~r2_hidden(A_25, C_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.12  tff(c_79, plain, (![C_29, D_30]: (r2_hidden('#skF_1', k2_zfmisc_1(C_29, D_30)) | ~r2_hidden('#skF_5', D_30) | ~r2_hidden('#skF_4', C_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 1.69/1.12  tff(c_12, plain, (~r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.12  tff(c_88, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_79, c_12])).
% 1.69/1.12  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_47, c_88])).
% 1.69/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.12  
% 1.69/1.12  Inference rules
% 1.69/1.12  ----------------------
% 1.69/1.12  #Ref     : 0
% 1.69/1.12  #Sup     : 20
% 1.69/1.12  #Fact    : 0
% 1.69/1.12  #Define  : 0
% 1.69/1.12  #Split   : 0
% 1.69/1.12  #Chain   : 0
% 1.69/1.12  #Close   : 0
% 1.69/1.12  
% 1.69/1.12  Ordering : KBO
% 1.69/1.12  
% 1.69/1.12  Simplification rules
% 1.69/1.12  ----------------------
% 1.69/1.12  #Subsume      : 0
% 1.69/1.12  #Demod        : 4
% 1.69/1.12  #Tautology    : 14
% 1.69/1.12  #SimpNegUnit  : 0
% 1.69/1.12  #BackRed      : 2
% 1.69/1.12  
% 1.69/1.12  #Partial instantiations: 0
% 1.69/1.12  #Strategies tried      : 1
% 1.69/1.12  
% 1.69/1.12  Timing (in seconds)
% 1.69/1.12  ----------------------
% 1.69/1.12  Preprocessing        : 0.26
% 1.69/1.12  Parsing              : 0.15
% 1.69/1.12  CNF conversion       : 0.02
% 1.69/1.12  Main loop            : 0.11
% 1.69/1.12  Inferencing          : 0.04
% 1.69/1.12  Reduction            : 0.03
% 1.69/1.12  Demodulation         : 0.02
% 1.69/1.12  BG Simplification    : 0.01
% 1.69/1.12  Subsumption          : 0.02
% 1.69/1.12  Abstraction          : 0.00
% 1.69/1.12  MUC search           : 0.00
% 1.69/1.12  Cooper               : 0.00
% 1.69/1.12  Total                : 0.40
% 1.69/1.12  Index Insertion      : 0.00
% 1.69/1.12  Index Deletion       : 0.00
% 1.69/1.13  Index Matching       : 0.00
% 1.69/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
