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
% DateTime   : Thu Dec  3 10:23:08 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  68 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_34,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_4',k5_setfam_1(u1_struct_0('#skF_3'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    r1_tarski('#skF_4',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_4')),k1_tops_2('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_41,B_42)),k1_tops_2(A_41,B_42,C_43)),k5_setfam_1(u1_struct_0(A_41),C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_6] : k3_tarski(k1_zfmisc_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [C_26,B_27,A_28] :
      ( r1_tarski(C_26,B_27)
      | ~ r2_hidden(C_26,A_28)
      | ~ r1_tarski(k3_tarski(A_28),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [C_5,B_27,A_1] :
      ( r1_tarski(C_5,B_27)
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_1)),B_27)
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_44])).

tff(c_48,plain,(
    ! [C_5,B_27,A_1] :
      ( r1_tarski(C_5,B_27)
      | ~ r1_tarski(A_1,B_27)
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_493,plain,(
    ! [C_96,A_97,C_98,B_99] :
      ( r1_tarski(C_96,k5_setfam_1(u1_struct_0(A_97),C_98))
      | ~ r1_tarski(C_96,k5_setfam_1(u1_struct_0(k1_pre_topc(A_97,B_99)),k1_tops_2(A_97,B_99,C_98)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97))))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_89,c_48])).

tff(c_538,plain,
    ( r1_tarski('#skF_4',k5_setfam_1(u1_struct_0('#skF_3'),'#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_493])).

tff(c_556,plain,(
    r1_tarski('#skF_4',k5_setfam_1(u1_struct_0('#skF_3'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_538])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.50  
% 2.94/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.94/1.50  
% 2.94/1.50  %Foreground sorts:
% 2.94/1.50  
% 2.94/1.50  
% 2.94/1.50  %Background operators:
% 2.94/1.50  
% 2.94/1.50  
% 2.94/1.50  %Foreground operators:
% 2.94/1.50  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.94/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.50  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.94/1.50  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.94/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.94/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.94/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.50  
% 2.94/1.51  tff(f_63, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 2.94/1.51  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 2.94/1.51  tff(f_34, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.94/1.51  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.94/1.51  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.94/1.51  tff(c_20, plain, (~r1_tarski('#skF_4', k5_setfam_1(u1_struct_0('#skF_3'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.51  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.51  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.51  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.51  tff(c_22, plain, (r1_tarski('#skF_4', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_4')), k1_tops_2('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.51  tff(c_89, plain, (![A_41, B_42, C_43]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_41, B_42)), k1_tops_2(A_41, B_42, C_43)), k5_setfam_1(u1_struct_0(A_41), C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.94/1.51  tff(c_14, plain, (![A_6]: (k3_tarski(k1_zfmisc_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.94/1.51  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.94/1.51  tff(c_44, plain, (![C_26, B_27, A_28]: (r1_tarski(C_26, B_27) | ~r2_hidden(C_26, A_28) | ~r1_tarski(k3_tarski(A_28), B_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.94/1.51  tff(c_46, plain, (![C_5, B_27, A_1]: (r1_tarski(C_5, B_27) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_1)), B_27) | ~r1_tarski(C_5, A_1))), inference(resolution, [status(thm)], [c_4, c_44])).
% 2.94/1.51  tff(c_48, plain, (![C_5, B_27, A_1]: (r1_tarski(C_5, B_27) | ~r1_tarski(A_1, B_27) | ~r1_tarski(C_5, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 2.94/1.51  tff(c_493, plain, (![C_96, A_97, C_98, B_99]: (r1_tarski(C_96, k5_setfam_1(u1_struct_0(A_97), C_98)) | ~r1_tarski(C_96, k5_setfam_1(u1_struct_0(k1_pre_topc(A_97, B_99)), k1_tops_2(A_97, B_99, C_98))) | ~m1_subset_1(C_98, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97)))) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_89, c_48])).
% 2.94/1.51  tff(c_538, plain, (r1_tarski('#skF_4', k5_setfam_1(u1_struct_0('#skF_3'), '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_493])).
% 2.94/1.51  tff(c_556, plain, (r1_tarski('#skF_4', k5_setfam_1(u1_struct_0('#skF_3'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_538])).
% 2.94/1.51  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_556])).
% 2.94/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.51  
% 2.94/1.51  Inference rules
% 2.94/1.51  ----------------------
% 2.94/1.51  #Ref     : 0
% 2.94/1.51  #Sup     : 121
% 2.94/1.51  #Fact    : 0
% 2.94/1.51  #Define  : 0
% 2.94/1.51  #Split   : 0
% 2.94/1.51  #Chain   : 0
% 2.94/1.51  #Close   : 0
% 2.94/1.51  
% 2.94/1.51  Ordering : KBO
% 2.94/1.51  
% 2.94/1.51  Simplification rules
% 2.94/1.51  ----------------------
% 2.94/1.51  #Subsume      : 4
% 2.94/1.51  #Demod        : 13
% 2.94/1.51  #Tautology    : 11
% 2.94/1.51  #SimpNegUnit  : 1
% 2.94/1.51  #BackRed      : 0
% 2.94/1.51  
% 2.94/1.51  #Partial instantiations: 0
% 2.94/1.51  #Strategies tried      : 1
% 2.94/1.51  
% 2.94/1.51  Timing (in seconds)
% 2.94/1.51  ----------------------
% 2.94/1.51  Preprocessing        : 0.31
% 2.94/1.51  Parsing              : 0.17
% 2.94/1.51  CNF conversion       : 0.02
% 2.94/1.51  Main loop            : 0.38
% 2.94/1.52  Inferencing          : 0.14
% 2.94/1.52  Reduction            : 0.09
% 2.94/1.52  Demodulation         : 0.06
% 2.94/1.52  BG Simplification    : 0.02
% 2.94/1.52  Subsumption          : 0.10
% 2.94/1.52  Abstraction          : 0.02
% 2.94/1.52  MUC search           : 0.00
% 2.94/1.52  Cooper               : 0.00
% 2.94/1.52  Total                : 0.71
% 2.94/1.52  Index Insertion      : 0.00
% 2.94/1.52  Index Deletion       : 0.00
% 2.94/1.52  Index Matching       : 0.00
% 2.94/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
