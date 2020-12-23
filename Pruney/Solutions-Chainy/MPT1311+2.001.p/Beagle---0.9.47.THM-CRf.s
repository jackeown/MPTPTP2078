%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   38 (  60 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 154 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(c_16,plain,(
    ~ v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( ~ v4_pre_topc('#skF_1'(A_26,B_27),A_26)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_26),B_27),A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,
    ( ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_45,plain,
    ( ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_42])).

tff(c_46,plain,(
    ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_45])).

tff(c_18,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_5] :
      ( m1_subset_1('#skF_1'(A_1,B_5),k1_zfmisc_1(u1_struct_0(A_1)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1),B_5),A_1)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_1'(A_24,B_25),B_25)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_24),B_25),A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_24))))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_38,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_35])).

tff(c_39,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_38])).

tff(c_47,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_pre_topc(C_28,A_29)
      | ~ r2_hidden(C_28,B_30)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ v2_tops_2(B_30,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_33] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),A_33)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ v2_tops_2('#skF_4',A_33)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33))))
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_39,c_47])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tops_2('#skF_4','#skF_3')
    | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_59,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_56])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_46,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  %$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.71/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.13  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.71/1.13  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.13  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.71/1.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.71/1.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.71/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.13  
% 1.85/1.14  tff(f_67, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v4_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_2)).
% 1.85/1.14  tff(f_41, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A)))) => v4_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_pre_topc)).
% 1.85/1.14  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 1.85/1.14  tff(c_16, plain, (~v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.14  tff(c_24, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.14  tff(c_22, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.14  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.14  tff(c_40, plain, (![A_26, B_27]: (~v4_pre_topc('#skF_1'(A_26, B_27), A_26) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_26), B_27), A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.14  tff(c_42, plain, (~v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_40])).
% 1.85/1.14  tff(c_45, plain, (~v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_42])).
% 1.85/1.14  tff(c_46, plain, (~v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_16, c_45])).
% 1.85/1.14  tff(c_18, plain, (v2_tops_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.85/1.14  tff(c_6, plain, (![A_1, B_5]: (m1_subset_1('#skF_1'(A_1, B_5), k1_zfmisc_1(u1_struct_0(A_1))) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1), B_5), A_1) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.14  tff(c_33, plain, (![A_24, B_25]: (r2_hidden('#skF_1'(A_24, B_25), B_25) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_24), B_25), A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_24)))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.14  tff(c_35, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_33])).
% 1.85/1.14  tff(c_38, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_35])).
% 1.85/1.14  tff(c_39, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_16, c_38])).
% 1.85/1.14  tff(c_47, plain, (![C_28, A_29, B_30]: (v4_pre_topc(C_28, A_29) | ~r2_hidden(C_28, B_30) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_29))) | ~v2_tops_2(B_30, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29)))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.14  tff(c_52, plain, (![A_33]: (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_33) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_33))) | ~v2_tops_2('#skF_4', A_33) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33)))) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_39, c_47])).
% 1.85/1.14  tff(c_56, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tops_2('#skF_4', '#skF_3') | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_52])).
% 1.85/1.14  tff(c_59, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_56])).
% 1.85/1.14  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_46, c_59])).
% 1.85/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.14  
% 1.85/1.14  Inference rules
% 1.85/1.14  ----------------------
% 1.85/1.14  #Ref     : 0
% 1.85/1.14  #Sup     : 5
% 1.85/1.14  #Fact    : 0
% 1.85/1.14  #Define  : 0
% 1.85/1.14  #Split   : 0
% 1.85/1.14  #Chain   : 0
% 1.85/1.14  #Close   : 0
% 1.85/1.14  
% 1.85/1.14  Ordering : KBO
% 1.85/1.14  
% 1.85/1.14  Simplification rules
% 1.85/1.14  ----------------------
% 1.85/1.14  #Subsume      : 0
% 1.85/1.14  #Demod        : 10
% 1.85/1.14  #Tautology    : 1
% 1.85/1.14  #SimpNegUnit  : 3
% 1.85/1.14  #BackRed      : 0
% 1.85/1.14  
% 1.85/1.14  #Partial instantiations: 0
% 1.85/1.14  #Strategies tried      : 1
% 1.85/1.14  
% 1.85/1.14  Timing (in seconds)
% 1.85/1.14  ----------------------
% 1.85/1.15  Preprocessing        : 0.27
% 1.85/1.15  Parsing              : 0.15
% 1.85/1.15  CNF conversion       : 0.02
% 1.85/1.15  Main loop            : 0.12
% 1.85/1.15  Inferencing          : 0.06
% 1.85/1.15  Reduction            : 0.03
% 1.85/1.15  Demodulation         : 0.03
% 1.85/1.15  BG Simplification    : 0.01
% 1.85/1.15  Subsumption          : 0.02
% 1.85/1.15  Abstraction          : 0.00
% 1.85/1.15  MUC search           : 0.00
% 1.85/1.15  Cooper               : 0.00
% 1.85/1.15  Total                : 0.42
% 1.85/1.15  Index Insertion      : 0.00
% 1.85/1.15  Index Deletion       : 0.00
% 1.85/1.15  Index Matching       : 0.00
% 1.85/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
