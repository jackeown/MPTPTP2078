%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:08 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_3',k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    r1_tarski('#skF_3',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_tops_2('#skF_2','#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6,B_10,C_12] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_6,B_10)),k1_tops_2(A_6,B_10,C_12)),k5_setfam_1(u1_struct_0(A_6),C_12))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_28,B_29,B_30] :
      ( r2_hidden('#skF_1'(A_28,B_29),B_30)
      | ~ r1_tarski(A_28,B_30)
      | r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_31,B_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(B_34,B_33)
      | ~ r1_tarski(A_31,B_34)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_79,plain,(
    ! [B_43,A_42,A_44,C_45,B_41] :
      ( r2_hidden('#skF_1'(A_42,B_41),k5_setfam_1(u1_struct_0(A_44),C_45))
      | ~ r1_tarski(A_42,k5_setfam_1(u1_struct_0(k1_pre_topc(A_44,B_43)),k1_tops_2(A_44,B_43,C_45)))
      | r1_tarski(A_42,B_41)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_8,c_41])).

tff(c_86,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_1'('#skF_3',B_41),k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4'))
      | r1_tarski('#skF_3',B_41)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_98,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_1'('#skF_3',B_46),k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4'))
      | r1_tarski('#skF_3',B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_86])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    r1_tarski('#skF_3',k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_10,c_104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.33  
% 1.96/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.96/1.33  
% 1.96/1.33  %Foreground sorts:
% 1.96/1.33  
% 1.96/1.33  
% 1.96/1.33  %Background operators:
% 1.96/1.33  
% 1.96/1.33  
% 1.96/1.33  %Foreground operators:
% 1.96/1.33  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 1.96/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.96/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.33  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.96/1.33  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 1.96/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.96/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.33  
% 1.96/1.34  tff(f_55, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 1.96/1.34  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 1.96/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.96/1.34  tff(c_10, plain, (~r1_tarski('#skF_3', k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.34  tff(c_18, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.34  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.34  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.34  tff(c_12, plain, (r1_tarski('#skF_3', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_tops_2('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.34  tff(c_8, plain, (![A_6, B_10, C_12]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_6, B_10)), k1_tops_2(A_6, B_10, C_12)), k5_setfam_1(u1_struct_0(A_6), C_12)) | ~m1_subset_1(C_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.34  tff(c_27, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.34  tff(c_32, plain, (![A_28, B_29, B_30]: (r2_hidden('#skF_1'(A_28, B_29), B_30) | ~r1_tarski(A_28, B_30) | r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_6, c_27])).
% 1.96/1.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.34  tff(c_41, plain, (![A_31, B_32, B_33, B_34]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(B_34, B_33) | ~r1_tarski(A_31, B_34) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.96/1.34  tff(c_79, plain, (![B_43, A_42, A_44, C_45, B_41]: (r2_hidden('#skF_1'(A_42, B_41), k5_setfam_1(u1_struct_0(A_44), C_45)) | ~r1_tarski(A_42, k5_setfam_1(u1_struct_0(k1_pre_topc(A_44, B_43)), k1_tops_2(A_44, B_43, C_45))) | r1_tarski(A_42, B_41) | ~m1_subset_1(C_45, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_8, c_41])).
% 1.96/1.34  tff(c_86, plain, (![B_41]: (r2_hidden('#skF_1'('#skF_3', B_41), k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4')) | r1_tarski('#skF_3', B_41) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_79])).
% 1.96/1.34  tff(c_98, plain, (![B_46]: (r2_hidden('#skF_1'('#skF_3', B_46), k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4')) | r1_tarski('#skF_3', B_46))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_86])).
% 1.96/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.34  tff(c_104, plain, (r1_tarski('#skF_3', k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_4])).
% 1.96/1.34  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_10, c_104])).
% 1.96/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.34  
% 1.96/1.34  Inference rules
% 1.96/1.34  ----------------------
% 1.96/1.34  #Ref     : 0
% 1.96/1.34  #Sup     : 19
% 1.96/1.34  #Fact    : 0
% 1.96/1.34  #Define  : 0
% 1.96/1.34  #Split   : 0
% 1.96/1.34  #Chain   : 0
% 1.96/1.34  #Close   : 0
% 1.96/1.34  
% 1.96/1.34  Ordering : KBO
% 1.96/1.34  
% 1.96/1.34  Simplification rules
% 1.96/1.34  ----------------------
% 1.96/1.34  #Subsume      : 3
% 1.96/1.34  #Demod        : 9
% 1.96/1.34  #Tautology    : 1
% 1.96/1.34  #SimpNegUnit  : 1
% 1.96/1.34  #BackRed      : 0
% 1.96/1.34  
% 1.96/1.34  #Partial instantiations: 0
% 1.96/1.34  #Strategies tried      : 1
% 1.96/1.34  
% 1.96/1.34  Timing (in seconds)
% 1.96/1.34  ----------------------
% 1.96/1.35  Preprocessing        : 0.36
% 1.96/1.35  Parsing              : 0.20
% 1.96/1.35  CNF conversion       : 0.02
% 1.96/1.35  Main loop            : 0.18
% 1.96/1.35  Inferencing          : 0.08
% 1.96/1.35  Reduction            : 0.05
% 1.96/1.35  Demodulation         : 0.03
% 1.96/1.35  BG Simplification    : 0.01
% 1.96/1.35  Subsumption          : 0.04
% 1.96/1.35  Abstraction          : 0.01
% 1.96/1.35  MUC search           : 0.00
% 1.96/1.35  Cooper               : 0.00
% 1.96/1.35  Total                : 0.57
% 1.96/1.35  Index Insertion      : 0.00
% 1.96/1.35  Index Deletion       : 0.00
% 1.96/1.35  Index Matching       : 0.00
% 1.96/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
