%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  80 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_58,B_59,C_60] : k2_zfmisc_1(k2_tarski(A_58,B_59),k1_tarski(C_60)) = k2_tarski(k4_tarski(A_58,C_60),k4_tarski(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [B_59,C_60] : k2_zfmisc_1(k2_tarski(B_59,B_59),k1_tarski(C_60)) = k1_tarski(k4_tarski(B_59,C_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_123,plain,(
    ! [B_59,C_60] : k2_zfmisc_1(k1_tarski(B_59),k1_tarski(C_60)) = k1_tarski(k4_tarski(B_59,C_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_137,plain,(
    ! [A_63,C_64,B_65,D_66] :
      ( r1_tarski(k2_zfmisc_1(A_63,C_64),k2_zfmisc_1(B_65,D_66))
      | ~ r1_tarski(C_64,D_66)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_239,plain,(
    ! [B_85,C_86,B_87,D_88] :
      ( r1_tarski(k1_tarski(k4_tarski(B_85,C_86)),k2_zfmisc_1(B_87,D_88))
      | ~ r1_tarski(k1_tarski(C_86),D_88)
      | ~ r1_tarski(k1_tarski(B_85),B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_137])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_255,plain,
    ( ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_239,c_77])).

tff(c_257,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_260,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_257])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_260])).

tff(c_265,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_278,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_265])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:06:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.29  
% 2.10/1.30  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_relset_1)).
% 2.10/1.30  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.10/1.30  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.30  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.10/1.30  tff(f_45, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.10/1.30  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.10/1.30  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_24, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.30  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.30  tff(c_91, plain, (![A_58, B_59, C_60]: (k2_zfmisc_1(k2_tarski(A_58, B_59), k1_tarski(C_60))=k2_tarski(k4_tarski(A_58, C_60), k4_tarski(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.30  tff(c_104, plain, (![B_59, C_60]: (k2_zfmisc_1(k2_tarski(B_59, B_59), k1_tarski(C_60))=k1_tarski(k4_tarski(B_59, C_60)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 2.10/1.30  tff(c_123, plain, (![B_59, C_60]: (k2_zfmisc_1(k1_tarski(B_59), k1_tarski(C_60))=k1_tarski(k4_tarski(B_59, C_60)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_104])).
% 2.10/1.30  tff(c_137, plain, (![A_63, C_64, B_65, D_66]: (r1_tarski(k2_zfmisc_1(A_63, C_64), k2_zfmisc_1(B_65, D_66)) | ~r1_tarski(C_64, D_66) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.30  tff(c_239, plain, (![B_85, C_86, B_87, D_88]: (r1_tarski(k1_tarski(k4_tarski(B_85, C_86)), k2_zfmisc_1(B_87, D_88)) | ~r1_tarski(k1_tarski(C_86), D_88) | ~r1_tarski(k1_tarski(B_85), B_87))), inference(superposition, [status(thm), theory('equality')], [c_123, c_137])).
% 2.10/1.30  tff(c_28, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.30  tff(c_30, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_77, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.10/1.30  tff(c_255, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_239, c_77])).
% 2.10/1.30  tff(c_257, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_255])).
% 2.10/1.30  tff(c_260, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_257])).
% 2.10/1.30  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_260])).
% 2.10/1.30  tff(c_265, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_255])).
% 2.10/1.30  tff(c_278, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_265])).
% 2.10/1.30  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_278])).
% 2.10/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  Inference rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Ref     : 0
% 2.10/1.30  #Sup     : 58
% 2.10/1.30  #Fact    : 0
% 2.10/1.30  #Define  : 0
% 2.10/1.30  #Split   : 1
% 2.10/1.30  #Chain   : 0
% 2.10/1.30  #Close   : 0
% 2.10/1.30  
% 2.10/1.30  Ordering : KBO
% 2.10/1.30  
% 2.10/1.30  Simplification rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Subsume      : 0
% 2.10/1.30  #Demod        : 17
% 2.10/1.30  #Tautology    : 33
% 2.10/1.30  #SimpNegUnit  : 0
% 2.10/1.30  #BackRed      : 0
% 2.10/1.30  
% 2.10/1.30  #Partial instantiations: 0
% 2.10/1.30  #Strategies tried      : 1
% 2.10/1.30  
% 2.10/1.30  Timing (in seconds)
% 2.10/1.30  ----------------------
% 2.10/1.30  Preprocessing        : 0.33
% 2.10/1.30  Parsing              : 0.18
% 2.10/1.30  CNF conversion       : 0.02
% 2.10/1.30  Main loop            : 0.20
% 2.10/1.30  Inferencing          : 0.08
% 2.10/1.30  Reduction            : 0.06
% 2.10/1.30  Demodulation         : 0.05
% 2.10/1.30  BG Simplification    : 0.02
% 2.10/1.30  Subsumption          : 0.02
% 2.10/1.30  Abstraction          : 0.02
% 2.10/1.30  MUC search           : 0.00
% 2.10/1.30  Cooper               : 0.00
% 2.10/1.30  Total                : 0.55
% 2.10/1.30  Index Insertion      : 0.00
% 2.10/1.30  Index Deletion       : 0.00
% 2.10/1.30  Index Matching       : 0.00
% 2.10/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
