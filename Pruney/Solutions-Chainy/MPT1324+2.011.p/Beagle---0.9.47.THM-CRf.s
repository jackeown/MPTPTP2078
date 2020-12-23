%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:08 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  55 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_6,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_21,B_22)),k1_tops_2(A_21,B_22,C_23)),k5_setfam_1(u1_struct_0(A_21),C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21))))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_27,A_28,C_29,B_30] :
      ( r1_tarski(A_27,k5_setfam_1(u1_struct_0(A_28),C_29))
      | ~ r1_tarski(A_27,k5_setfam_1(u1_struct_0(k1_pre_topc(A_28,B_30)),k1_tops_2(A_28,B_30,C_29)))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_31,c_2])).

tff(c_58,plain,
    ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_68,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_10,c_58])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.15  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.15  
% 1.62/1.15  %Foreground sorts:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Background operators:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Foreground operators:
% 1.62/1.15  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.62/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.62/1.15  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.62/1.15  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.62/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.15  
% 1.62/1.16  tff(f_54, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 1.62/1.16  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 1.62/1.16  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.62/1.16  tff(c_6, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.16  tff(c_14, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.16  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.16  tff(c_10, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.16  tff(c_8, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.16  tff(c_31, plain, (![A_21, B_22, C_23]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_21, B_22)), k1_tops_2(A_21, B_22, C_23)), k5_setfam_1(u1_struct_0(A_21), C_23)) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21)))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.16  tff(c_45, plain, (![A_27, A_28, C_29, B_30]: (r1_tarski(A_27, k5_setfam_1(u1_struct_0(A_28), C_29)) | ~r1_tarski(A_27, k5_setfam_1(u1_struct_0(k1_pre_topc(A_28, B_30)), k1_tops_2(A_28, B_30, C_29))) | ~m1_subset_1(C_29, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_31, c_2])).
% 1.62/1.16  tff(c_58, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_45])).
% 1.62/1.16  tff(c_68, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_10, c_58])).
% 1.62/1.16  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_68])).
% 1.62/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  Inference rules
% 1.62/1.16  ----------------------
% 1.62/1.16  #Ref     : 0
% 1.62/1.16  #Sup     : 12
% 1.62/1.16  #Fact    : 0
% 1.62/1.16  #Define  : 0
% 1.62/1.16  #Split   : 0
% 1.62/1.16  #Chain   : 0
% 1.62/1.16  #Close   : 0
% 1.62/1.16  
% 1.62/1.16  Ordering : KBO
% 1.62/1.16  
% 1.62/1.16  Simplification rules
% 1.62/1.16  ----------------------
% 1.62/1.16  #Subsume      : 2
% 1.62/1.16  #Demod        : 10
% 1.62/1.16  #Tautology    : 1
% 1.62/1.16  #SimpNegUnit  : 1
% 1.62/1.16  #BackRed      : 0
% 1.62/1.16  
% 1.62/1.16  #Partial instantiations: 0
% 1.62/1.16  #Strategies tried      : 1
% 1.62/1.16  
% 1.62/1.16  Timing (in seconds)
% 1.62/1.16  ----------------------
% 1.62/1.16  Preprocessing        : 0.25
% 1.62/1.16  Parsing              : 0.14
% 1.62/1.16  CNF conversion       : 0.02
% 1.62/1.16  Main loop            : 0.11
% 1.62/1.16  Inferencing          : 0.04
% 1.62/1.17  Reduction            : 0.03
% 1.62/1.17  Demodulation         : 0.02
% 1.62/1.17  BG Simplification    : 0.01
% 1.62/1.17  Subsumption          : 0.02
% 1.62/1.17  Abstraction          : 0.01
% 1.62/1.17  MUC search           : 0.00
% 1.62/1.17  Cooper               : 0.00
% 1.62/1.17  Total                : 0.40
% 1.62/1.17  Index Insertion      : 0.00
% 1.62/1.17  Index Deletion       : 0.00
% 1.62/1.17  Index Matching       : 0.00
% 1.62/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
