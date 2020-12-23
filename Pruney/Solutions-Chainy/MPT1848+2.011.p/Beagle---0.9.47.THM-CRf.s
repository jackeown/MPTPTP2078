%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 171 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 343 expanded)
%              Number of equality atoms :   13 (  76 expanded)
%              Maximal formula depth    :    9 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_10,plain,(
    ! [A_4] : l1_orders_2(k2_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_5] : u1_struct_0(k2_yellow_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [B_27,A_28] :
      ( v1_subset_1(B_27,A_28)
      | B_27 = A_28
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_91,plain,(
    ! [A_31] :
      ( v1_subset_1(k2_struct_0(A_31),u1_struct_0(A_31))
      | u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_subset_1(k2_struct_0(A_2),u1_struct_0(A_2))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_105,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_110,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_orders_2(A_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_113,plain,(
    ! [A_4] : u1_struct_0(k2_yellow_1(A_4)) = k2_struct_0(k2_yellow_1(A_4)) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_115,plain,(
    ! [A_4] : k2_struct_0(k2_yellow_1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_73,plain,(
    ! [A_26] :
      ( m1_subset_1(k2_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_5] :
      ( m1_subset_1(k2_struct_0(k2_yellow_1(A_5)),k1_zfmisc_1(A_5))
      | ~ l1_struct_0(k2_yellow_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_73])).

tff(c_116,plain,(
    ! [A_5] :
      ( m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ l1_struct_0(k2_yellow_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_76])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_182,plain,(
    ! [B_48,A_49] :
      ( v1_subset_1(u1_struct_0(B_48),u1_struct_0(A_49))
      | ~ m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ v1_tex_2(B_48,A_49)
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_198,plain,(
    ! [B_48] :
      ( v1_subset_1(u1_struct_0(B_48),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_48,'#skF_2')
      | ~ m1_pre_topc(B_48,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_182])).

tff(c_206,plain,(
    ! [B_51] :
      ( v1_subset_1(u1_struct_0(B_51),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_51),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_51,'#skF_2')
      | ~ m1_pre_topc(B_51,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_198])).

tff(c_210,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_116,c_206])).

tff(c_219,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_210])).

tff(c_222,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_226,plain,(
    ~ l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_226])).

tff(c_232,plain,(
    l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_231,plain,(
    v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_60,plain,(
    ! [A_24] :
      ( ~ v1_subset_1(k2_struct_0(A_24),u1_struct_0(A_24))
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_5] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_5)),A_5)
      | ~ l1_struct_0(k2_yellow_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_60])).

tff(c_117,plain,(
    ! [A_5] :
      ( ~ v1_subset_1(A_5,A_5)
      | ~ l1_struct_0(k2_yellow_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_63])).

tff(c_239,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_231,c_117])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.27  
% 2.07/1.27  %Foreground sorts:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Background operators:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Foreground operators:
% 2.07/1.27  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.27  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.07/1.27  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.07/1.27  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.07/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.07/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.27  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.07/1.27  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.07/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.27  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.07/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.27  
% 2.07/1.29  tff(f_42, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.07/1.29  tff(f_38, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.07/1.29  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.07/1.29  tff(f_46, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.07/1.29  tff(f_29, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.07/1.29  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.07/1.29  tff(f_34, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.07/1.29  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 2.07/1.29  tff(c_10, plain, (![A_4]: (l1_orders_2(k2_yellow_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.07/1.29  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_orders_2(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.07/1.29  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.07/1.29  tff(c_28, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.07/1.29  tff(c_12, plain, (![A_5]: (u1_struct_0(k2_yellow_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.29  tff(c_2, plain, (![A_1]: (m1_subset_1(k2_struct_0(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.29  tff(c_80, plain, (![B_27, A_28]: (v1_subset_1(B_27, A_28) | B_27=A_28 | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.07/1.29  tff(c_91, plain, (![A_31]: (v1_subset_1(k2_struct_0(A_31), u1_struct_0(A_31)) | u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(resolution, [status(thm)], [c_2, c_80])).
% 2.07/1.29  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_struct_0(A_2), u1_struct_0(A_2)) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.07/1.29  tff(c_105, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(resolution, [status(thm)], [c_91, c_4])).
% 2.07/1.29  tff(c_110, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_orders_2(A_35))), inference(resolution, [status(thm)], [c_6, c_105])).
% 2.07/1.29  tff(c_113, plain, (![A_4]: (u1_struct_0(k2_yellow_1(A_4))=k2_struct_0(k2_yellow_1(A_4)))), inference(resolution, [status(thm)], [c_10, c_110])).
% 2.07/1.29  tff(c_115, plain, (![A_4]: (k2_struct_0(k2_yellow_1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_113])).
% 2.07/1.29  tff(c_73, plain, (![A_26]: (m1_subset_1(k2_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.29  tff(c_76, plain, (![A_5]: (m1_subset_1(k2_struct_0(k2_yellow_1(A_5)), k1_zfmisc_1(A_5)) | ~l1_struct_0(k2_yellow_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_73])).
% 2.07/1.29  tff(c_116, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~l1_struct_0(k2_yellow_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_76])).
% 2.07/1.29  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.07/1.29  tff(c_30, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.07/1.29  tff(c_182, plain, (![B_48, A_49]: (v1_subset_1(u1_struct_0(B_48), u1_struct_0(A_49)) | ~m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(u1_struct_0(A_49))) | ~v1_tex_2(B_48, A_49) | ~m1_pre_topc(B_48, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.29  tff(c_198, plain, (![B_48]: (v1_subset_1(u1_struct_0(B_48), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_48, '#skF_2') | ~m1_pre_topc(B_48, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_182])).
% 2.07/1.29  tff(c_206, plain, (![B_51]: (v1_subset_1(u1_struct_0(B_51), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_51), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_51, '#skF_2') | ~m1_pre_topc(B_51, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_198])).
% 2.07/1.29  tff(c_210, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_116, c_206])).
% 2.07/1.29  tff(c_219, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_210])).
% 2.07/1.29  tff(c_222, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_219])).
% 2.07/1.29  tff(c_226, plain, (~l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_222])).
% 2.07/1.29  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_226])).
% 2.07/1.29  tff(c_232, plain, (l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_219])).
% 2.07/1.29  tff(c_231, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_219])).
% 2.07/1.29  tff(c_60, plain, (![A_24]: (~v1_subset_1(k2_struct_0(A_24), u1_struct_0(A_24)) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.07/1.29  tff(c_63, plain, (![A_5]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_5)), A_5) | ~l1_struct_0(k2_yellow_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_60])).
% 2.07/1.29  tff(c_117, plain, (![A_5]: (~v1_subset_1(A_5, A_5) | ~l1_struct_0(k2_yellow_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_63])).
% 2.07/1.29  tff(c_239, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_231, c_117])).
% 2.07/1.29  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_239])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 0
% 2.07/1.29  #Sup     : 42
% 2.07/1.29  #Fact    : 0
% 2.07/1.29  #Define  : 0
% 2.07/1.29  #Split   : 3
% 2.07/1.29  #Chain   : 0
% 2.07/1.29  #Close   : 0
% 2.07/1.29  
% 2.07/1.29  Ordering : KBO
% 2.07/1.29  
% 2.07/1.29  Simplification rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Subsume      : 7
% 2.07/1.29  #Demod        : 26
% 2.07/1.29  #Tautology    : 12
% 2.07/1.29  #SimpNegUnit  : 0
% 2.07/1.29  #BackRed      : 2
% 2.07/1.29  
% 2.07/1.29  #Partial instantiations: 0
% 2.07/1.29  #Strategies tried      : 1
% 2.07/1.29  
% 2.07/1.29  Timing (in seconds)
% 2.07/1.29  ----------------------
% 2.07/1.29  Preprocessing        : 0.31
% 2.07/1.29  Parsing              : 0.16
% 2.07/1.29  CNF conversion       : 0.02
% 2.07/1.29  Main loop            : 0.21
% 2.07/1.29  Inferencing          : 0.08
% 2.07/1.29  Reduction            : 0.06
% 2.07/1.29  Demodulation         : 0.04
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.04
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.55
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
