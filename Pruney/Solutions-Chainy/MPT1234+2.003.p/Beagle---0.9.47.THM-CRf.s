%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:35 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  70 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_12,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_12,B_14] :
      ( k3_subset_1(u1_struct_0(A_12),k2_pre_topc(A_12,k3_subset_1(u1_struct_0(A_12),B_14))) = k1_tops_1(A_12,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [B_18,A_19] :
      ( r1_tarski(B_18,k2_pre_topc(A_19,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_29),B_30),k2_pre_topc(A_29,k3_subset_1(u1_struct_0(A_29),B_30)))
      | ~ l1_pre_topc(A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29))) ) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

tff(c_4,plain,(
    ! [A_3,C_6,B_4] :
      ( r1_tarski(k3_subset_1(A_3,C_6),B_4)
      | ~ r1_tarski(k3_subset_1(A_3,B_4),C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_41),k2_pre_topc(A_41,k3_subset_1(u1_struct_0(A_41),B_42))),B_42)
      | ~ m1_subset_1(k2_pre_topc(A_41,k3_subset_1(u1_struct_0(A_41),B_42)),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41))) ) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_106,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tops_1(A_43,B_44),B_44)
      | ~ m1_subset_1(k2_pre_topc(A_43,k3_subset_1(u1_struct_0(A_43),B_44)),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_113,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_tops_1(A_45,B_46),B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_45),B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_120,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tops_1(A_47,B_48),B_48)
      | ~ l1_pre_topc(A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47))) ) ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_129,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_120])).

tff(c_135,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_129])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.33  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.13/1.33  
% 2.13/1.33  %Foreground sorts:
% 2.13/1.33  
% 2.13/1.33  
% 2.13/1.33  %Background operators:
% 2.13/1.33  
% 2.13/1.33  
% 2.13/1.33  %Foreground operators:
% 2.13/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.13/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.13/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.13/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.33  
% 2.28/1.34  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.28/1.34  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.28/1.34  tff(f_44, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.28/1.34  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.28/1.34  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.28/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 2.28/1.34  tff(c_12, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.34  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.34  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.34  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.34  tff(c_6, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.34  tff(c_10, plain, (![A_12, B_14]: (k3_subset_1(u1_struct_0(A_12), k2_pre_topc(A_12, k3_subset_1(u1_struct_0(A_12), B_14)))=k1_tops_1(A_12, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.34  tff(c_18, plain, (![B_18, A_19]: (r1_tarski(B_18, k2_pre_topc(A_19, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.34  tff(c_54, plain, (![A_29, B_30]: (r1_tarski(k3_subset_1(u1_struct_0(A_29), B_30), k2_pre_topc(A_29, k3_subset_1(u1_struct_0(A_29), B_30))) | ~l1_pre_topc(A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))))), inference(resolution, [status(thm)], [c_2, c_18])).
% 2.28/1.34  tff(c_4, plain, (![A_3, C_6, B_4]: (r1_tarski(k3_subset_1(A_3, C_6), B_4) | ~r1_tarski(k3_subset_1(A_3, B_4), C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.34  tff(c_96, plain, (![A_41, B_42]: (r1_tarski(k3_subset_1(u1_struct_0(A_41), k2_pre_topc(A_41, k3_subset_1(u1_struct_0(A_41), B_42))), B_42) | ~m1_subset_1(k2_pre_topc(A_41, k3_subset_1(u1_struct_0(A_41), B_42)), k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))))), inference(resolution, [status(thm)], [c_54, c_4])).
% 2.28/1.34  tff(c_106, plain, (![A_43, B_44]: (r1_tarski(k1_tops_1(A_43, B_44), B_44) | ~m1_subset_1(k2_pre_topc(A_43, k3_subset_1(u1_struct_0(A_43), B_44)), k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_96])).
% 2.28/1.34  tff(c_113, plain, (![A_45, B_46]: (r1_tarski(k1_tops_1(A_45, B_46), B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_45), B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_6, c_106])).
% 2.28/1.34  tff(c_120, plain, (![A_47, B_48]: (r1_tarski(k1_tops_1(A_47, B_48), B_48) | ~l1_pre_topc(A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))))), inference(resolution, [status(thm)], [c_2, c_113])).
% 2.28/1.34  tff(c_129, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_120])).
% 2.28/1.34  tff(c_135, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_129])).
% 2.28/1.34  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_135])).
% 2.28/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.34  
% 2.28/1.34  Inference rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Ref     : 0
% 2.28/1.34  #Sup     : 30
% 2.28/1.34  #Fact    : 0
% 2.28/1.34  #Define  : 0
% 2.28/1.34  #Split   : 0
% 2.28/1.34  #Chain   : 0
% 2.28/1.34  #Close   : 0
% 2.28/1.34  
% 2.28/1.34  Ordering : KBO
% 2.28/1.34  
% 2.28/1.34  Simplification rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Subsume      : 5
% 2.28/1.34  #Demod        : 2
% 2.28/1.34  #Tautology    : 2
% 2.28/1.34  #SimpNegUnit  : 1
% 2.28/1.34  #BackRed      : 0
% 2.28/1.34  
% 2.28/1.34  #Partial instantiations: 0
% 2.28/1.34  #Strategies tried      : 1
% 2.28/1.34  
% 2.28/1.34  Timing (in seconds)
% 2.28/1.34  ----------------------
% 2.28/1.34  Preprocessing        : 0.31
% 2.28/1.34  Parsing              : 0.17
% 2.28/1.34  CNF conversion       : 0.02
% 2.28/1.34  Main loop            : 0.20
% 2.28/1.34  Inferencing          : 0.08
% 2.28/1.34  Reduction            : 0.05
% 2.28/1.34  Demodulation         : 0.04
% 2.28/1.34  BG Simplification    : 0.01
% 2.28/1.34  Subsumption          : 0.04
% 2.28/1.34  Abstraction          : 0.01
% 2.28/1.34  MUC search           : 0.00
% 2.28/1.34  Cooper               : 0.00
% 2.28/1.34  Total                : 0.54
% 2.28/1.34  Index Insertion      : 0.00
% 2.28/1.34  Index Deletion       : 0.00
% 2.28/1.34  Index Matching       : 0.00
% 2.28/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
