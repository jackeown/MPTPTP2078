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
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   53 (  89 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 238 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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
                        & v1_tops_2(C,A) )
                     => v1_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

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

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    v1_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    v1_tops_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_75,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,u1_pre_topc(A_35))
      | ~ v1_tops_2(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,
    ( r1_tarski('#skF_4',u1_pre_topc('#skF_1'))
    | ~ v1_tops_2('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_75])).

tff(c_92,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_84])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [C_23,A_24,D_25,B_26] :
      ( C_23 = A_24
      | g1_pre_topc(C_23,D_25) != g1_pre_topc(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [A_37,B_38] :
      ( u1_struct_0('#skF_2') = A_37
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_42])).

tff(c_108,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_129,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_108])).

tff(c_131,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_129])).

tff(c_51,plain,(
    ! [D_27,B_28,C_29,A_30] :
      ( D_27 = B_28
      | g1_pre_topc(C_29,D_27) != g1_pre_topc(A_30,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [D_27,C_29] :
      ( u1_pre_topc('#skF_2') = D_27
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_29,D_27)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_51])).

tff(c_140,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_166,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_140])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2])).

tff(c_164,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_156])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_164])).

tff(c_168,plain,(
    ! [D_27,C_29] :
      ( u1_pre_topc('#skF_2') = D_27
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_29,D_27) ) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_293,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_168])).

tff(c_12,plain,(
    ~ v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    ! [B_31,A_32] :
      ( v1_tops_2(B_31,A_32)
      | ~ r1_tarski(B_31,u1_pre_topc(A_32))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_32))))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,
    ( v1_tops_2('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_69,plain,
    ( v1_tops_2('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_69])).

tff(c_305,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_70])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.33  
% 2.25/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.33  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.25/1.33  
% 2.25/1.33  %Foreground sorts:
% 2.25/1.33  
% 2.25/1.33  
% 2.25/1.33  %Background operators:
% 2.25/1.33  
% 2.25/1.33  
% 2.25/1.33  %Foreground operators:
% 2.25/1.33  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.25/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.33  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.25/1.33  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.25/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.33  
% 2.25/1.34  tff(f_67, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v1_tops_2(C, A)) => v1_tops_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_waybel_9)).
% 2.25/1.34  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 2.25/1.34  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.25/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.25/1.34  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_16, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_14, plain, (v1_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_28, plain, (v1_tops_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14])).
% 2.25/1.34  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_27, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.25/1.34  tff(c_75, plain, (![B_34, A_35]: (r1_tarski(B_34, u1_pre_topc(A_35)) | ~v1_tops_2(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.25/1.34  tff(c_84, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_1')) | ~v1_tops_2('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27, c_75])).
% 2.25/1.34  tff(c_92, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_84])).
% 2.25/1.34  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.34  tff(c_18, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_42, plain, (![C_23, A_24, D_25, B_26]: (C_23=A_24 | g1_pre_topc(C_23, D_25)!=g1_pre_topc(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.34  tff(c_98, plain, (![A_37, B_38]: (u1_struct_0('#skF_2')=A_37 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_42])).
% 2.25/1.34  tff(c_108, plain, (![A_1]: (u1_struct_0(A_1)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_98])).
% 2.25/1.34  tff(c_129, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_108])).
% 2.25/1.34  tff(c_131, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_129])).
% 2.25/1.34  tff(c_51, plain, (![D_27, B_28, C_29, A_30]: (D_27=B_28 | g1_pre_topc(C_29, D_27)!=g1_pre_topc(A_30, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.34  tff(c_55, plain, (![D_27, C_29]: (u1_pre_topc('#skF_2')=D_27 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_29, D_27) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_51])).
% 2.25/1.34  tff(c_140, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_55])).
% 2.25/1.34  tff(c_166, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_140])).
% 2.25/1.34  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_156, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_131, c_2])).
% 2.25/1.34  tff(c_164, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_156])).
% 2.25/1.34  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_164])).
% 2.25/1.34  tff(c_168, plain, (![D_27, C_29]: (u1_pre_topc('#skF_2')=D_27 | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=g1_pre_topc(C_29, D_27))), inference(splitRight, [status(thm)], [c_55])).
% 2.25/1.34  tff(c_293, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_168])).
% 2.25/1.34  tff(c_12, plain, (~v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.34  tff(c_56, plain, (![B_31, A_32]: (v1_tops_2(B_31, A_32) | ~r1_tarski(B_31, u1_pre_topc(A_32)) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_32)))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.25/1.34  tff(c_62, plain, (v1_tops_2('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_56])).
% 2.25/1.34  tff(c_69, plain, (v1_tops_2('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 2.25/1.34  tff(c_70, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_12, c_69])).
% 2.25/1.34  tff(c_305, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_70])).
% 2.25/1.34  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_305])).
% 2.25/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.34  
% 2.25/1.34  Inference rules
% 2.25/1.34  ----------------------
% 2.25/1.34  #Ref     : 5
% 2.25/1.34  #Sup     : 51
% 2.25/1.34  #Fact    : 0
% 2.25/1.34  #Define  : 0
% 2.25/1.34  #Split   : 5
% 2.25/1.34  #Chain   : 0
% 2.25/1.34  #Close   : 0
% 2.25/1.34  
% 2.25/1.34  Ordering : KBO
% 2.25/1.34  
% 2.25/1.34  Simplification rules
% 2.25/1.34  ----------------------
% 2.25/1.34  #Subsume      : 12
% 2.25/1.34  #Demod        : 59
% 2.25/1.34  #Tautology    : 28
% 2.25/1.34  #SimpNegUnit  : 4
% 2.25/1.34  #BackRed      : 20
% 2.25/1.34  
% 2.25/1.34  #Partial instantiations: 0
% 2.25/1.34  #Strategies tried      : 1
% 2.25/1.34  
% 2.25/1.34  Timing (in seconds)
% 2.25/1.34  ----------------------
% 2.25/1.35  Preprocessing        : 0.27
% 2.25/1.35  Parsing              : 0.15
% 2.25/1.35  CNF conversion       : 0.02
% 2.25/1.35  Main loop            : 0.27
% 2.25/1.35  Inferencing          : 0.08
% 2.25/1.35  Reduction            : 0.09
% 2.25/1.35  Demodulation         : 0.06
% 2.25/1.35  BG Simplification    : 0.02
% 2.25/1.35  Subsumption          : 0.06
% 2.25/1.35  Abstraction          : 0.02
% 2.25/1.35  MUC search           : 0.00
% 2.25/1.35  Cooper               : 0.00
% 2.25/1.35  Total                : 0.58
% 2.25/1.35  Index Insertion      : 0.00
% 2.25/1.35  Index Deletion       : 0.00
% 2.25/1.35  Index Matching       : 0.00
% 2.25/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
