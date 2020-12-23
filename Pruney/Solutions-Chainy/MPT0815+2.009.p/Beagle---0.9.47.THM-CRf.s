%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  26 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

tff(c_31,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_19])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  %$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.61/1.11  
% 1.61/1.11  %Foreground sorts:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Background operators:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Foreground operators:
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.11  
% 1.61/1.11  tff(f_42, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 1.61/1.11  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.61/1.11  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.61/1.11  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.11  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.11  tff(c_22, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.11  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.12  tff(c_10, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.12  tff(c_19, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_10])).
% 1.61/1.12  tff(c_31, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_19])).
% 1.61/1.12  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_31])).
% 1.61/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  Inference rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Ref     : 0
% 1.61/1.12  #Sup     : 4
% 1.61/1.12  #Fact    : 0
% 1.61/1.12  #Define  : 0
% 1.61/1.12  #Split   : 0
% 1.61/1.12  #Chain   : 0
% 1.61/1.12  #Close   : 0
% 1.61/1.12  
% 1.61/1.12  Ordering : KBO
% 1.61/1.12  
% 1.61/1.12  Simplification rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Subsume      : 0
% 1.61/1.12  #Demod        : 2
% 1.61/1.12  #Tautology    : 2
% 1.61/1.12  #SimpNegUnit  : 0
% 1.61/1.12  #BackRed      : 0
% 1.61/1.12  
% 1.61/1.12  #Partial instantiations: 0
% 1.61/1.12  #Strategies tried      : 1
% 1.61/1.12  
% 1.61/1.12  Timing (in seconds)
% 1.61/1.12  ----------------------
% 1.61/1.12  Preprocessing        : 0.25
% 1.61/1.12  Parsing              : 0.14
% 1.61/1.12  CNF conversion       : 0.01
% 1.61/1.12  Main loop            : 0.07
% 1.61/1.12  Inferencing          : 0.03
% 1.61/1.12  Reduction            : 0.02
% 1.61/1.12  Demodulation         : 0.02
% 1.61/1.12  BG Simplification    : 0.01
% 1.61/1.12  Subsumption          : 0.01
% 1.61/1.12  Abstraction          : 0.00
% 1.61/1.12  MUC search           : 0.00
% 1.61/1.12  Cooper               : 0.00
% 1.61/1.12  Total                : 0.35
% 1.61/1.12  Index Insertion      : 0.00
% 1.61/1.12  Index Deletion       : 0.00
% 1.61/1.12  Index Matching       : 0.00
% 1.61/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
