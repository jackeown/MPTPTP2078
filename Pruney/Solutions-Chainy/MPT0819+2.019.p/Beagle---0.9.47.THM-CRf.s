%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  66 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_78,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(k2_zfmisc_1(A_24,C_25),k2_zfmisc_1(B_26,C_25))
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_29,B_30,C_31,A_32] :
      ( r1_tarski(A_29,k2_zfmisc_1(B_30,C_31))
      | ~ r1_tarski(A_29,k2_zfmisc_1(A_32,C_31))
      | ~ r1_tarski(A_32,B_30) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_122,plain,(
    ! [B_30] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_30,'#skF_3'))
      | ~ r1_tarski('#skF_1',B_30) ) ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_70,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_tarski(k2_zfmisc_1(C_21,A_22),k2_zfmisc_1(C_21,B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_38,C_39,B_40,A_41] :
      ( r1_tarski(A_38,k2_zfmisc_1(C_39,B_40))
      | ~ r1_tarski(A_38,k2_zfmisc_1(C_39,A_41))
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_281,plain,(
    ! [B_51,B_52] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_51,B_52))
      | ~ r1_tarski('#skF_3',B_52)
      | ~ r1_tarski('#skF_1',B_51) ) ),
    inference(resolution,[status(thm)],[c_122,c_181])).

tff(c_19,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_19,c_12])).

tff(c_296,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_281,c_23])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.38  
% 2.51/1.39  tff(f_50, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 2.51/1.39  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.51/1.39  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.51/1.39  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.51/1.39  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.39  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.39  tff(c_18, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.39  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.39  tff(c_32, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_24])).
% 2.51/1.39  tff(c_78, plain, (![A_24, C_25, B_26]: (r1_tarski(k2_zfmisc_1(A_24, C_25), k2_zfmisc_1(B_26, C_25)) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.39  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.39  tff(c_110, plain, (![A_29, B_30, C_31, A_32]: (r1_tarski(A_29, k2_zfmisc_1(B_30, C_31)) | ~r1_tarski(A_29, k2_zfmisc_1(A_32, C_31)) | ~r1_tarski(A_32, B_30))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.51/1.39  tff(c_122, plain, (![B_30]: (r1_tarski('#skF_5', k2_zfmisc_1(B_30, '#skF_3')) | ~r1_tarski('#skF_1', B_30))), inference(resolution, [status(thm)], [c_32, c_110])).
% 2.51/1.39  tff(c_70, plain, (![C_21, A_22, B_23]: (r1_tarski(k2_zfmisc_1(C_21, A_22), k2_zfmisc_1(C_21, B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.39  tff(c_181, plain, (![A_38, C_39, B_40, A_41]: (r1_tarski(A_38, k2_zfmisc_1(C_39, B_40)) | ~r1_tarski(A_38, k2_zfmisc_1(C_39, A_41)) | ~r1_tarski(A_41, B_40))), inference(resolution, [status(thm)], [c_70, c_2])).
% 2.51/1.39  tff(c_281, plain, (![B_51, B_52]: (r1_tarski('#skF_5', k2_zfmisc_1(B_51, B_52)) | ~r1_tarski('#skF_3', B_52) | ~r1_tarski('#skF_1', B_51))), inference(resolution, [status(thm)], [c_122, c_181])).
% 2.51/1.39  tff(c_19, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.39  tff(c_12, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.39  tff(c_23, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_19, c_12])).
% 2.51/1.39  tff(c_296, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_281, c_23])).
% 2.51/1.39  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_296])).
% 2.51/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.39  
% 2.51/1.39  Inference rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Ref     : 0
% 2.51/1.39  #Sup     : 81
% 2.51/1.39  #Fact    : 0
% 2.51/1.39  #Define  : 0
% 2.51/1.39  #Split   : 9
% 2.51/1.39  #Chain   : 0
% 2.51/1.39  #Close   : 0
% 2.51/1.39  
% 2.51/1.39  Ordering : KBO
% 2.51/1.39  
% 2.51/1.39  Simplification rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Subsume      : 13
% 2.51/1.39  #Demod        : 7
% 2.51/1.39  #Tautology    : 6
% 2.51/1.39  #SimpNegUnit  : 0
% 2.51/1.39  #BackRed      : 0
% 2.51/1.39  
% 2.51/1.39  #Partial instantiations: 0
% 2.51/1.39  #Strategies tried      : 1
% 2.51/1.39  
% 2.51/1.39  Timing (in seconds)
% 2.51/1.40  ----------------------
% 2.51/1.40  Preprocessing        : 0.29
% 2.51/1.40  Parsing              : 0.16
% 2.51/1.40  CNF conversion       : 0.02
% 2.51/1.40  Main loop            : 0.33
% 2.51/1.40  Inferencing          : 0.11
% 2.51/1.40  Reduction            : 0.08
% 2.51/1.40  Demodulation         : 0.06
% 2.51/1.40  BG Simplification    : 0.02
% 2.51/1.40  Subsumption          : 0.10
% 2.51/1.40  Abstraction          : 0.01
% 2.51/1.40  MUC search           : 0.00
% 2.51/1.40  Cooper               : 0.00
% 2.51/1.40  Total                : 0.65
% 2.51/1.40  Index Insertion      : 0.00
% 2.51/1.40  Index Deletion       : 0.00
% 2.51/1.40  Index Matching       : 0.00
% 2.51/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
