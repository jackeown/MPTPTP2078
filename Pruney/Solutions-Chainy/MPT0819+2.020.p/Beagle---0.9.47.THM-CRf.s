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
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   38 (  52 expanded)
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
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_68,plain,(
    ! [A_22,C_23,B_24,D_25] :
      ( r1_tarski(k2_zfmisc_1(A_22,C_23),k2_zfmisc_1(B_24,D_25))
      | ~ r1_tarski(C_23,D_25)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [C_30,D_31,B_29,A_28,A_32] :
      ( r1_tarski(A_32,k2_zfmisc_1(B_29,D_31))
      | ~ r1_tarski(A_32,k2_zfmisc_1(A_28,C_30))
      | ~ r1_tarski(C_30,D_31)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_108,plain,(
    ! [B_33,D_34] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_33,D_34))
      | ~ r1_tarski('#skF_3',D_34)
      | ~ r1_tarski('#skF_1',B_33) ) ),
    inference(resolution,[status(thm)],[c_30,c_98])).

tff(c_17,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_17,c_10])).

tff(c_119,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_21])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.17  
% 1.86/1.18  tff(f_50, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 1.86/1.18  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.86/1.18  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.86/1.18  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.86/1.18  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.86/1.18  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.86/1.18  tff(c_16, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.86/1.18  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.18  tff(c_30, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_22])).
% 1.86/1.18  tff(c_68, plain, (![A_22, C_23, B_24, D_25]: (r1_tarski(k2_zfmisc_1(A_22, C_23), k2_zfmisc_1(B_24, D_25)) | ~r1_tarski(C_23, D_25) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.18  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.18  tff(c_98, plain, (![C_30, D_31, B_29, A_28, A_32]: (r1_tarski(A_32, k2_zfmisc_1(B_29, D_31)) | ~r1_tarski(A_32, k2_zfmisc_1(A_28, C_30)) | ~r1_tarski(C_30, D_31) | ~r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_68, c_2])).
% 1.86/1.18  tff(c_108, plain, (![B_33, D_34]: (r1_tarski('#skF_5', k2_zfmisc_1(B_33, D_34)) | ~r1_tarski('#skF_3', D_34) | ~r1_tarski('#skF_1', B_33))), inference(resolution, [status(thm)], [c_30, c_98])).
% 1.95/1.18  tff(c_17, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.18  tff(c_10, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.18  tff(c_21, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_17, c_10])).
% 1.95/1.18  tff(c_119, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_108, c_21])).
% 1.95/1.18  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_119])).
% 1.95/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  Inference rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Ref     : 0
% 1.95/1.18  #Sup     : 29
% 1.95/1.18  #Fact    : 0
% 1.95/1.18  #Define  : 0
% 1.95/1.18  #Split   : 4
% 1.95/1.18  #Chain   : 0
% 1.95/1.18  #Close   : 0
% 1.95/1.18  
% 1.95/1.18  Ordering : KBO
% 1.95/1.18  
% 1.95/1.18  Simplification rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Subsume      : 4
% 1.95/1.18  #Demod        : 5
% 1.95/1.18  #Tautology    : 4
% 1.95/1.18  #SimpNegUnit  : 0
% 1.95/1.18  #BackRed      : 0
% 1.95/1.18  
% 1.95/1.18  #Partial instantiations: 0
% 1.95/1.18  #Strategies tried      : 1
% 1.95/1.18  
% 1.95/1.18  Timing (in seconds)
% 1.95/1.18  ----------------------
% 1.95/1.18  Preprocessing        : 0.26
% 1.95/1.18  Parsing              : 0.15
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.17
% 1.95/1.18  Inferencing          : 0.06
% 1.95/1.18  Reduction            : 0.04
% 1.95/1.18  Demodulation         : 0.03
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.05
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.46
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
