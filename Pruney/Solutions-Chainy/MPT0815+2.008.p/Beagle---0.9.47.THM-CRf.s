%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  38 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_36,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( r2_hidden(k4_tarski(A_73,B_74),k2_zfmisc_1(C_75,D_76))
      | ~ r2_hidden(B_74,D_76)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(k2_tarski(A_64,B_65),C_66)
      | ~ r2_hidden(B_65,C_66)
      | ~ r2_hidden(A_64,C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,(
    ! [A_71,C_72] :
      ( r1_tarski(k1_tarski(A_71),C_72)
      | ~ r2_hidden(A_71,C_72)
      | ~ r2_hidden(A_71,C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_30,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_73,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_32])).

tff(c_113,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_106,c_73])).

tff(c_118,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_113])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  
% 1.87/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.15  
% 1.87/1.15  %Foreground sorts:
% 1.87/1.15  
% 1.87/1.15  
% 1.87/1.15  %Background operators:
% 1.87/1.15  
% 1.87/1.15  
% 1.87/1.15  %Foreground operators:
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.15  
% 1.87/1.16  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 1.87/1.16  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.87/1.16  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.87/1.16  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.87/1.16  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.87/1.16  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.16  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.16  tff(c_115, plain, (![A_73, B_74, C_75, D_76]: (r2_hidden(k4_tarski(A_73, B_74), k2_zfmisc_1(C_75, D_76)) | ~r2_hidden(B_74, D_76) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.16  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.16  tff(c_85, plain, (![A_64, B_65, C_66]: (r1_tarski(k2_tarski(A_64, B_65), C_66) | ~r2_hidden(B_65, C_66) | ~r2_hidden(A_64, C_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.16  tff(c_106, plain, (![A_71, C_72]: (r1_tarski(k1_tarski(A_71), C_72) | ~r2_hidden(A_71, C_72) | ~r2_hidden(A_71, C_72))), inference(superposition, [status(thm), theory('equality')], [c_2, c_85])).
% 1.87/1.16  tff(c_30, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.16  tff(c_32, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.16  tff(c_73, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_32])).
% 1.87/1.16  tff(c_113, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_106, c_73])).
% 1.87/1.16  tff(c_118, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_115, c_113])).
% 1.87/1.16  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_118])).
% 1.87/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  Inference rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Ref     : 0
% 1.87/1.16  #Sup     : 20
% 1.87/1.16  #Fact    : 0
% 1.87/1.16  #Define  : 0
% 1.87/1.16  #Split   : 0
% 1.87/1.16  #Chain   : 0
% 1.87/1.16  #Close   : 0
% 1.87/1.16  
% 1.87/1.16  Ordering : KBO
% 1.87/1.16  
% 1.87/1.16  Simplification rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Subsume      : 1
% 1.87/1.16  #Demod        : 2
% 1.87/1.16  #Tautology    : 12
% 1.87/1.16  #SimpNegUnit  : 0
% 1.87/1.16  #BackRed      : 0
% 1.87/1.16  
% 1.87/1.16  #Partial instantiations: 0
% 1.87/1.16  #Strategies tried      : 1
% 1.87/1.16  
% 1.87/1.16  Timing (in seconds)
% 1.87/1.16  ----------------------
% 1.87/1.16  Preprocessing        : 0.30
% 1.87/1.16  Parsing              : 0.16
% 1.87/1.16  CNF conversion       : 0.02
% 1.87/1.16  Main loop            : 0.11
% 1.87/1.16  Inferencing          : 0.05
% 1.87/1.16  Reduction            : 0.03
% 1.87/1.16  Demodulation         : 0.03
% 1.87/1.16  BG Simplification    : 0.01
% 1.87/1.16  Subsumption          : 0.02
% 1.87/1.16  Abstraction          : 0.01
% 1.87/1.16  MUC search           : 0.00
% 1.87/1.16  Cooper               : 0.00
% 1.87/1.16  Total                : 0.43
% 1.87/1.16  Index Insertion      : 0.00
% 1.87/1.16  Index Deletion       : 0.00
% 1.87/1.16  Index Matching       : 0.00
% 1.87/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
