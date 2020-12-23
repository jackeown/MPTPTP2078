%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:54 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  90 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_10,plain,(
    ! [A_4] : l1_orders_2(k2_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( m1_subset_1(u1_struct_0(B_8),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,(
    ! [B_49,A_50] :
      ( v1_subset_1(u1_struct_0(B_49),u1_struct_0(A_50))
      | ~ m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v1_tex_2(B_49,A_50)
      | ~ m1_pre_topc(B_49,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,(
    ! [B_52,A_53] :
      ( v1_subset_1(u1_struct_0(B_52),u1_struct_0(A_53))
      | ~ v1_tex_2(B_52,A_53)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_16,c_167])).

tff(c_227,plain,(
    ! [B_52] :
      ( v1_subset_1(u1_struct_0(B_52),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_52,'#skF_2')
      | ~ m1_pre_topc(B_52,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_218])).

tff(c_237,plain,(
    ! [B_54] :
      ( v1_subset_1(u1_struct_0(B_54),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_54,'#skF_2')
      | ~ m1_pre_topc(B_54,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_227])).

tff(c_12,plain,(
    ! [A_5] : u1_struct_0(k2_yellow_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_66,plain,(
    ! [A_4] : u1_struct_0(k2_yellow_1(A_4)) = k2_struct_0(k2_yellow_1(A_4)) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_68,plain,(
    ! [A_4] : k2_struct_0(k2_yellow_1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_66])).

tff(c_78,plain,(
    ! [A_28] :
      ( ~ v1_subset_1(k2_struct_0(A_28),u1_struct_0(A_28))
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_5] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_5)),A_5)
      | ~ l1_struct_0(k2_yellow_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_89,plain,(
    ! [A_5] :
      ( ~ v1_subset_1(A_5,A_5)
      | ~ l1_struct_0(k2_yellow_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_87])).

tff(c_240,plain,
    ( ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_89])).

tff(c_249,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_240])).

tff(c_265,plain,(
    ~ l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6,c_249])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.28  
% 1.99/1.28  %Foreground sorts:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Background operators:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Foreground operators:
% 1.99/1.28  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.99/1.28  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.99/1.28  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.99/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.99/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.99/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.28  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.99/1.28  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.99/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.99/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.28  
% 2.27/1.29  tff(f_42, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.27/1.29  tff(f_38, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.27/1.29  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 2.27/1.29  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.27/1.29  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.27/1.29  tff(f_46, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.27/1.29  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.27/1.29  tff(f_34, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.27/1.29  tff(c_10, plain, (![A_4]: (l1_orders_2(k2_yellow_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.29  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.29  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_26, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_28, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.29  tff(c_16, plain, (![B_8, A_6]: (m1_subset_1(u1_struct_0(B_8), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.29  tff(c_167, plain, (![B_49, A_50]: (v1_subset_1(u1_struct_0(B_49), u1_struct_0(A_50)) | ~m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_50))) | ~v1_tex_2(B_49, A_50) | ~m1_pre_topc(B_49, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.29  tff(c_218, plain, (![B_52, A_53]: (v1_subset_1(u1_struct_0(B_52), u1_struct_0(A_53)) | ~v1_tex_2(B_52, A_53) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_16, c_167])).
% 2.27/1.29  tff(c_227, plain, (![B_52]: (v1_subset_1(u1_struct_0(B_52), u1_struct_0('#skF_3')) | ~v1_tex_2(B_52, '#skF_2') | ~m1_pre_topc(B_52, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_218])).
% 2.27/1.29  tff(c_237, plain, (![B_54]: (v1_subset_1(u1_struct_0(B_54), u1_struct_0('#skF_3')) | ~v1_tex_2(B_54, '#skF_2') | ~m1_pre_topc(B_54, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_227])).
% 2.27/1.29  tff(c_12, plain, (![A_5]: (u1_struct_0(k2_yellow_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.27/1.29  tff(c_58, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.29  tff(c_63, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_orders_2(A_26))), inference(resolution, [status(thm)], [c_6, c_58])).
% 2.27/1.29  tff(c_66, plain, (![A_4]: (u1_struct_0(k2_yellow_1(A_4))=k2_struct_0(k2_yellow_1(A_4)))), inference(resolution, [status(thm)], [c_10, c_63])).
% 2.27/1.29  tff(c_68, plain, (![A_4]: (k2_struct_0(k2_yellow_1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_66])).
% 2.27/1.29  tff(c_78, plain, (![A_28]: (~v1_subset_1(k2_struct_0(A_28), u1_struct_0(A_28)) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.29  tff(c_87, plain, (![A_5]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_5)), A_5) | ~l1_struct_0(k2_yellow_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_78])).
% 2.27/1.29  tff(c_89, plain, (![A_5]: (~v1_subset_1(A_5, A_5) | ~l1_struct_0(k2_yellow_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_87])).
% 2.27/1.29  tff(c_240, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_237, c_89])).
% 2.27/1.29  tff(c_249, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_240])).
% 2.27/1.29  tff(c_265, plain, (~l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_249])).
% 2.27/1.29  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_265])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 0
% 2.27/1.29  #Sup     : 53
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 2
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 8
% 2.27/1.29  #Demod        : 18
% 2.27/1.29  #Tautology    : 8
% 2.27/1.29  #SimpNegUnit  : 0
% 2.27/1.29  #BackRed      : 0
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.29  Preprocessing        : 0.31
% 2.27/1.29  Parsing              : 0.16
% 2.27/1.29  CNF conversion       : 0.02
% 2.27/1.29  Main loop            : 0.21
% 2.27/1.29  Inferencing          : 0.08
% 2.27/1.29  Reduction            : 0.06
% 2.27/1.29  Demodulation         : 0.05
% 2.27/1.30  BG Simplification    : 0.01
% 2.27/1.30  Subsumption          : 0.04
% 2.27/1.30  Abstraction          : 0.01
% 2.27/1.30  MUC search           : 0.00
% 2.27/1.30  Cooper               : 0.00
% 2.27/1.30  Total                : 0.56
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
