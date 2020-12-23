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
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  80 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_40,B_41,C_42] : k2_zfmisc_1(k2_tarski(A_40,B_41),k1_tarski(C_42)) = k2_tarski(k4_tarski(A_40,C_42),k4_tarski(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [B_41,C_42] : k2_zfmisc_1(k2_tarski(B_41,B_41),k1_tarski(C_42)) = k1_tarski(k4_tarski(B_41,C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_117,plain,(
    ! [B_41,C_42] : k2_zfmisc_1(k1_tarski(B_41),k1_tarski(C_42)) = k1_tarski(k4_tarski(B_41,C_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_131,plain,(
    ! [A_45,C_46,B_47,D_48] :
      ( r1_tarski(k2_zfmisc_1(A_45,C_46),k2_zfmisc_1(B_47,D_48))
      | ~ r1_tarski(C_46,D_48)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_215,plain,(
    ! [B_56,C_57,B_58,D_59] :
      ( r1_tarski(k1_tarski(k4_tarski(B_56,C_57)),k2_zfmisc_1(B_58,D_59))
      | ~ r1_tarski(k1_tarski(C_57),D_59)
      | ~ r1_tarski(k1_tarski(B_56),B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_131])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_24])).

tff(c_231,plain,
    ( ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_215,c_71])).

tff(c_233,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_236,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_233])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_236])).

tff(c_241,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_245,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_241])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:11:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.96/1.19  
% 1.96/1.19  %Foreground sorts:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Background operators:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Foreground operators:
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.19  
% 1.96/1.20  tff(f_58, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 1.96/1.20  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.96/1.20  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.20  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.96/1.20  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.96/1.20  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.96/1.20  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.20  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.20  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.20  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.20  tff(c_85, plain, (![A_40, B_41, C_42]: (k2_zfmisc_1(k2_tarski(A_40, B_41), k1_tarski(C_42))=k2_tarski(k4_tarski(A_40, C_42), k4_tarski(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.20  tff(c_98, plain, (![B_41, C_42]: (k2_zfmisc_1(k2_tarski(B_41, B_41), k1_tarski(C_42))=k1_tarski(k4_tarski(B_41, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 1.96/1.20  tff(c_117, plain, (![B_41, C_42]: (k2_zfmisc_1(k1_tarski(B_41), k1_tarski(C_42))=k1_tarski(k4_tarski(B_41, C_42)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_98])).
% 1.96/1.20  tff(c_131, plain, (![A_45, C_46, B_47, D_48]: (r1_tarski(k2_zfmisc_1(A_45, C_46), k2_zfmisc_1(B_47, D_48)) | ~r1_tarski(C_46, D_48) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.20  tff(c_215, plain, (![B_56, C_57, B_58, D_59]: (r1_tarski(k1_tarski(k4_tarski(B_56, C_57)), k2_zfmisc_1(B_58, D_59)) | ~r1_tarski(k1_tarski(C_57), D_59) | ~r1_tarski(k1_tarski(B_56), B_58))), inference(superposition, [status(thm), theory('equality')], [c_117, c_131])).
% 1.96/1.20  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.20  tff(c_24, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.20  tff(c_71, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_24])).
% 1.96/1.20  tff(c_231, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_215, c_71])).
% 1.96/1.20  tff(c_233, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_231])).
% 1.96/1.20  tff(c_236, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_233])).
% 1.96/1.20  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_236])).
% 1.96/1.20  tff(c_241, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_231])).
% 1.96/1.20  tff(c_245, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_241])).
% 1.96/1.20  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_245])).
% 1.96/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  Inference rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Ref     : 0
% 1.96/1.20  #Sup     : 52
% 1.96/1.20  #Fact    : 0
% 1.96/1.20  #Define  : 0
% 1.96/1.20  #Split   : 1
% 1.96/1.20  #Chain   : 0
% 1.96/1.20  #Close   : 0
% 1.96/1.20  
% 1.96/1.20  Ordering : KBO
% 1.96/1.20  
% 1.96/1.20  Simplification rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Subsume      : 0
% 1.96/1.20  #Demod        : 17
% 1.96/1.20  #Tautology    : 27
% 1.96/1.20  #SimpNegUnit  : 0
% 1.96/1.20  #BackRed      : 0
% 1.96/1.20  
% 1.96/1.20  #Partial instantiations: 0
% 1.96/1.20  #Strategies tried      : 1
% 1.96/1.20  
% 1.96/1.20  Timing (in seconds)
% 1.96/1.20  ----------------------
% 1.96/1.20  Preprocessing        : 0.28
% 1.96/1.20  Parsing              : 0.15
% 1.96/1.20  CNF conversion       : 0.02
% 1.96/1.20  Main loop            : 0.17
% 1.96/1.20  Inferencing          : 0.07
% 1.96/1.20  Reduction            : 0.05
% 1.96/1.20  Demodulation         : 0.04
% 1.96/1.20  BG Simplification    : 0.01
% 1.96/1.20  Subsumption          : 0.02
% 1.96/1.20  Abstraction          : 0.01
% 1.96/1.20  MUC search           : 0.00
% 1.96/1.20  Cooper               : 0.00
% 1.96/1.20  Total                : 0.48
% 1.96/1.20  Index Insertion      : 0.00
% 1.96/1.20  Index Deletion       : 0.00
% 1.96/1.20  Index Matching       : 0.00
% 1.96/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
