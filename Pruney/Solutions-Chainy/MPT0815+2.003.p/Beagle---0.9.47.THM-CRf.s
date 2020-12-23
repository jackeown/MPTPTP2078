%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:53 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [E_39,F_40,A_41,B_42] :
      ( r2_hidden(k4_tarski(E_39,F_40),k2_zfmisc_1(A_41,B_42))
      | ~ r2_hidden(F_40,B_42)
      | ~ r2_hidden(E_39,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k1_tarski(A_35),k1_zfmisc_1(B_36))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_7','#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_9'),k2_zfmisc_1('#skF_8','#skF_10')) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_41,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_37])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  %$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.64/1.11  tff('#skF_7', type, '#skF_7': $i).
% 1.64/1.11  tff('#skF_10', type, '#skF_10': $i).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.11  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.64/1.11  tff('#skF_9', type, '#skF_9': $i).
% 1.64/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.11  tff('#skF_8', type, '#skF_8': $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.64/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.11  
% 1.64/1.12  tff(f_48, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_relset_1)).
% 1.64/1.12  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 1.64/1.12  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.64/1.12  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.12  tff(c_30, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.12  tff(c_38, plain, (![E_39, F_40, A_41, B_42]: (r2_hidden(k4_tarski(E_39, F_40), k2_zfmisc_1(A_41, B_42)) | ~r2_hidden(F_40, B_42) | ~r2_hidden(E_39, A_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.12  tff(c_26, plain, (![A_35, B_36]: (m1_subset_1(k1_tarski(A_35), k1_zfmisc_1(B_36)) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.12  tff(c_28, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_7', '#skF_9')), k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.12  tff(c_37, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_9'), k2_zfmisc_1('#skF_8', '#skF_10'))), inference(resolution, [status(thm)], [c_26, c_28])).
% 1.64/1.12  tff(c_41, plain, (~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_38, c_37])).
% 1.64/1.12  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_41])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 2
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 0
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Subsume      : 0
% 1.64/1.12  #Demod        : 2
% 1.64/1.12  #Tautology    : 0
% 1.64/1.12  #SimpNegUnit  : 0
% 1.64/1.12  #BackRed      : 0
% 1.64/1.12  
% 1.64/1.12  #Partial instantiations: 0
% 1.64/1.12  #Strategies tried      : 1
% 1.64/1.12  
% 1.64/1.12  Timing (in seconds)
% 1.64/1.12  ----------------------
% 1.72/1.13  Preprocessing        : 0.28
% 1.72/1.13  Parsing              : 0.14
% 1.72/1.13  CNF conversion       : 0.03
% 1.72/1.13  Main loop            : 0.08
% 1.72/1.13  Inferencing          : 0.02
% 1.72/1.13  Reduction            : 0.03
% 1.72/1.13  Demodulation         : 0.02
% 1.72/1.13  BG Simplification    : 0.01
% 1.72/1.13  Subsumption          : 0.02
% 1.72/1.13  Abstraction          : 0.01
% 1.72/1.13  MUC search           : 0.00
% 1.72/1.13  Cooper               : 0.00
% 1.72/1.13  Total                : 0.39
% 1.72/1.13  Index Insertion      : 0.00
% 1.72/1.13  Index Deletion       : 0.00
% 1.72/1.13  Index Matching       : 0.00
% 1.72/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
