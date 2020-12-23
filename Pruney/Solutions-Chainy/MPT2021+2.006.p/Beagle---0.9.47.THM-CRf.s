%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:11 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 170 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :   90 ( 492 expanded)
%              Number of equality atoms :   24 ( 186 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tops_2(C,A) )
                     => v2_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> r1_tarski(B,k7_setfam_1(u1_struct_0(A),u1_pre_topc(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_12,plain,(
    ~ v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    v2_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    v2_tops_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( r1_tarski(B_10,k7_setfam_1(u1_struct_0(A_8),u1_pre_topc(A_8)))
      | ~ v2_tops_2(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_51,plain,(
    ! [D_27,B_28,C_29,A_30] :
      ( D_27 = B_28
      | g1_pre_topc(C_29,D_27) != g1_pre_topc(A_30,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    ! [B_33,A_34] :
      ( u1_pre_topc('#skF_2') = B_33
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_34,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_51])).

tff(c_81,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_88,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_81])).

tff(c_90,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_88])).

tff(c_55,plain,(
    ! [D_27,C_29] :
      ( u1_pre_topc('#skF_2') = D_27
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_29,D_27)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_51])).

tff(c_99,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_117,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_99])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2])).

tff(c_115,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_115])).

tff(c_120,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_138,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_120])).

tff(c_42,plain,(
    ! [C_23,A_24,D_25,B_26] :
      ( C_23 = A_24
      | g1_pre_topc(C_23,D_25) != g1_pre_topc(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [C_23,D_25] :
      ( u1_struct_0('#skF_2') = C_23
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_23,D_25)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_42])).

tff(c_182,plain,(
    ! [C_23,D_25] :
      ( u1_struct_0('#skF_2') = C_23
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_23,D_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_90,c_46])).

tff(c_185,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_182])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( v2_tops_2(B_10,A_8)
      | ~ r1_tarski(B_10,k7_setfam_1(u1_struct_0(A_8),u1_pre_topc(A_8)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [B_10] :
      ( v2_tops_2(B_10,'#skF_2')
      | ~ r1_tarski(B_10,k7_setfam_1(u1_struct_0('#skF_2'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_134,plain,(
    ! [B_10] :
      ( v2_tops_2(B_10,'#skF_2')
      | ~ r1_tarski(B_10,k7_setfam_1(u1_struct_0('#skF_2'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_127])).

tff(c_226,plain,(
    ! [B_46] :
      ( v2_tops_2(B_46,'#skF_2')
      | ~ r1_tarski(B_46,k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_134])).

tff(c_230,plain,(
    ! [B_10] :
      ( v2_tops_2(B_10,'#skF_2')
      | ~ v2_tops_2(B_10,'#skF_1')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_245,plain,(
    ! [B_48] :
      ( v2_tops_2(B_48,'#skF_2')
      | ~ v2_tops_2(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_230])).

tff(c_255,plain,
    ( v2_tops_2('#skF_4','#skF_2')
    | ~ v2_tops_2('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_245])).

tff(c_262,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_255])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:08:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.91/1.22  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.91/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.91/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.22  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.22  
% 2.13/1.23  tff(f_67, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tops_2(C, A)) => v2_tops_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_waybel_9)).
% 2.13/1.23  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> r1_tarski(B, k7_setfam_1(u1_struct_0(A), u1_pre_topc(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_2)).
% 2.13/1.23  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.13/1.23  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.13/1.23  tff(c_12, plain, (~v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_16, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_14, plain, (v2_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_28, plain, (v2_tops_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14])).
% 2.13/1.23  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_27, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.13/1.23  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_10, plain, (![B_10, A_8]: (r1_tarski(B_10, k7_setfam_1(u1_struct_0(A_8), u1_pre_topc(A_8))) | ~v2_tops_2(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.23  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.23  tff(c_18, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_51, plain, (![D_27, B_28, C_29, A_30]: (D_27=B_28 | g1_pre_topc(C_29, D_27)!=g1_pre_topc(A_30, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.23  tff(c_71, plain, (![B_33, A_34]: (u1_pre_topc('#skF_2')=B_33 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_34, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_51])).
% 2.13/1.23  tff(c_81, plain, (![A_1]: (u1_pre_topc(A_1)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.13/1.23  tff(c_88, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_81])).
% 2.13/1.23  tff(c_90, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_88])).
% 2.13/1.23  tff(c_55, plain, (![D_27, C_29]: (u1_pre_topc('#skF_2')=D_27 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_29, D_27) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_51])).
% 2.13/1.23  tff(c_99, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_55])).
% 2.13/1.23  tff(c_117, plain, (~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_99])).
% 2.13/1.23  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_109, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_2])).
% 2.13/1.23  tff(c_115, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_109])).
% 2.13/1.23  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_115])).
% 2.13/1.23  tff(c_120, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_55])).
% 2.13/1.23  tff(c_138, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_120])).
% 2.13/1.23  tff(c_42, plain, (![C_23, A_24, D_25, B_26]: (C_23=A_24 | g1_pre_topc(C_23, D_25)!=g1_pre_topc(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.23  tff(c_46, plain, (![C_23, D_25]: (u1_struct_0('#skF_2')=C_23 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_23, D_25) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_42])).
% 2.13/1.23  tff(c_182, plain, (![C_23, D_25]: (u1_struct_0('#skF_2')=C_23 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_23, D_25))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_90, c_46])).
% 2.13/1.23  tff(c_185, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_182])).
% 2.13/1.23  tff(c_8, plain, (![B_10, A_8]: (v2_tops_2(B_10, A_8) | ~r1_tarski(B_10, k7_setfam_1(u1_struct_0(A_8), u1_pre_topc(A_8))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.23  tff(c_127, plain, (![B_10]: (v2_tops_2(B_10, '#skF_2') | ~r1_tarski(B_10, k7_setfam_1(u1_struct_0('#skF_2'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_8])).
% 2.13/1.23  tff(c_134, plain, (![B_10]: (v2_tops_2(B_10, '#skF_2') | ~r1_tarski(B_10, k7_setfam_1(u1_struct_0('#skF_2'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_127])).
% 2.13/1.23  tff(c_226, plain, (![B_46]: (v2_tops_2(B_46, '#skF_2') | ~r1_tarski(B_46, k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_134])).
% 2.13/1.23  tff(c_230, plain, (![B_10]: (v2_tops_2(B_10, '#skF_2') | ~v2_tops_2(B_10, '#skF_1') | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_226])).
% 2.13/1.23  tff(c_245, plain, (![B_48]: (v2_tops_2(B_48, '#skF_2') | ~v2_tops_2(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_230])).
% 2.13/1.23  tff(c_255, plain, (v2_tops_2('#skF_4', '#skF_2') | ~v2_tops_2('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_27, c_245])).
% 2.13/1.23  tff(c_262, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_255])).
% 2.13/1.23  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_262])).
% 2.13/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.23  
% 2.13/1.23  Inference rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Ref     : 6
% 2.13/1.23  #Sup     : 45
% 2.13/1.23  #Fact    : 0
% 2.13/1.23  #Define  : 0
% 2.13/1.23  #Split   : 3
% 2.13/1.23  #Chain   : 0
% 2.13/1.23  #Close   : 0
% 2.13/1.23  
% 2.13/1.23  Ordering : KBO
% 2.13/1.23  
% 2.13/1.23  Simplification rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Subsume      : 12
% 2.13/1.23  #Demod        : 46
% 2.13/1.23  #Tautology    : 26
% 2.13/1.23  #SimpNegUnit  : 2
% 2.13/1.23  #BackRed      : 10
% 2.13/1.23  
% 2.13/1.23  #Partial instantiations: 0
% 2.13/1.23  #Strategies tried      : 1
% 2.13/1.23  
% 2.13/1.23  Timing (in seconds)
% 2.13/1.23  ----------------------
% 2.13/1.23  Preprocessing        : 0.28
% 2.13/1.23  Parsing              : 0.15
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.23  Main loop            : 0.20
% 2.13/1.23  Inferencing          : 0.07
% 2.13/1.23  Reduction            : 0.07
% 2.13/1.23  Demodulation         : 0.05
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.04
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.51
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
