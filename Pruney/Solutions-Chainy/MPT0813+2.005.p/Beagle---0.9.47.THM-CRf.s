%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ( r1_tarski(A,D)
         => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [C_16,B_17,A_18] :
      ( r2_hidden(C_16,B_17)
      | ~ r2_hidden(C_16,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_20,B_21,B_22] :
      ( r2_hidden('#skF_1'(A_20,B_21),B_22)
      | ~ r1_tarski(A_20,B_22)
      | r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_23,B_24,B_25,B_26] :
      ( r2_hidden('#skF_1'(A_23,B_24),B_25)
      | ~ r1_tarski(B_26,B_25)
      | ~ r1_tarski(A_23,B_26)
      | r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_75,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_30,'#skF_5')
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_32] :
      ( ~ r1_tarski(A_32,'#skF_5')
      | r1_tarski(A_32,k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_17,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_21,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_17,c_12])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_21])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:15:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.19  
% 1.68/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.68/1.20  
% 1.68/1.20  %Foreground sorts:
% 1.68/1.20  
% 1.68/1.20  
% 1.68/1.20  %Background operators:
% 1.68/1.20  
% 1.68/1.20  
% 1.68/1.20  %Foreground operators:
% 1.68/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.20  
% 1.68/1.21  tff(f_43, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 1.68/1.21  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.68/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.68/1.21  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.21  tff(c_16, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.21  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.21  tff(c_30, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_22])).
% 1.68/1.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.21  tff(c_38, plain, (![C_16, B_17, A_18]: (r2_hidden(C_16, B_17) | ~r2_hidden(C_16, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.21  tff(c_43, plain, (![A_20, B_21, B_22]: (r2_hidden('#skF_1'(A_20, B_21), B_22) | ~r1_tarski(A_20, B_22) | r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.68/1.21  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.21  tff(c_52, plain, (![A_23, B_24, B_25, B_26]: (r2_hidden('#skF_1'(A_23, B_24), B_25) | ~r1_tarski(B_26, B_25) | ~r1_tarski(A_23, B_26) | r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_43, c_2])).
% 1.68/1.21  tff(c_75, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r1_tarski(A_30, '#skF_5') | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_30, c_52])).
% 1.68/1.21  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.21  tff(c_84, plain, (![A_32]: (~r1_tarski(A_32, '#skF_5') | r1_tarski(A_32, k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_75, c_4])).
% 1.68/1.21  tff(c_17, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.21  tff(c_12, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.21  tff(c_21, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_17, c_12])).
% 1.68/1.21  tff(c_89, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_21])).
% 1.68/1.21  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_89])).
% 1.68/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.21  
% 1.68/1.21  Inference rules
% 1.68/1.21  ----------------------
% 1.68/1.21  #Ref     : 0
% 1.68/1.21  #Sup     : 17
% 1.68/1.21  #Fact    : 0
% 1.68/1.21  #Define  : 0
% 1.68/1.21  #Split   : 0
% 1.68/1.21  #Chain   : 0
% 1.68/1.21  #Close   : 0
% 1.68/1.21  
% 1.68/1.21  Ordering : KBO
% 1.68/1.21  
% 1.68/1.21  Simplification rules
% 1.68/1.21  ----------------------
% 1.68/1.21  #Subsume      : 1
% 1.68/1.21  #Demod        : 1
% 1.68/1.21  #Tautology    : 2
% 1.68/1.21  #SimpNegUnit  : 0
% 1.68/1.21  #BackRed      : 0
% 1.68/1.21  
% 1.68/1.21  #Partial instantiations: 0
% 1.68/1.21  #Strategies tried      : 1
% 1.68/1.21  
% 1.68/1.21  Timing (in seconds)
% 1.68/1.21  ----------------------
% 1.68/1.21  Preprocessing        : 0.26
% 1.68/1.21  Parsing              : 0.15
% 1.68/1.21  CNF conversion       : 0.02
% 1.68/1.21  Main loop            : 0.14
% 1.68/1.21  Inferencing          : 0.06
% 1.68/1.21  Reduction            : 0.03
% 1.68/1.21  Demodulation         : 0.03
% 1.68/1.21  BG Simplification    : 0.01
% 1.68/1.21  Subsumption          : 0.03
% 1.68/1.21  Abstraction          : 0.00
% 1.68/1.21  MUC search           : 0.00
% 1.68/1.21  Cooper               : 0.00
% 1.68/1.21  Total                : 0.42
% 1.68/1.21  Index Insertion      : 0.00
% 1.68/1.21  Index Deletion       : 0.00
% 1.68/1.21  Index Matching       : 0.00
% 1.68/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
