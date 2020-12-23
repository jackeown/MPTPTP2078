%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:54 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 (  93 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_64,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_14,plain,(
    ! [A_6] : l1_orders_2(k2_yellow_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_130,plain,(
    ! [B_39,A_40] :
      ( v1_subset_1(u1_struct_0(B_39),u1_struct_0(A_40))
      | ~ m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v1_tex_2(B_39,A_40)
      | ~ m1_pre_topc(B_39,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_142,plain,(
    ! [B_39] :
      ( v1_subset_1(u1_struct_0(B_39),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_39,'#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_130])).

tff(c_197,plain,(
    ! [B_47] :
      ( v1_subset_1(u1_struct_0(B_47),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_47,'#skF_2')
      | ~ m1_pre_topc(B_47,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_142])).

tff(c_207,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_197])).

tff(c_213,plain,(
    v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_207])).

tff(c_16,plain,(
    ! [A_7] : u1_struct_0(k2_yellow_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_79,plain,(
    ! [A_6] : u1_struct_0(k2_yellow_1(A_6)) = k2_struct_0(k2_yellow_1(A_6)) ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_81,plain,(
    ! [A_6] : k2_struct_0(k2_yellow_1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_91,plain,(
    ! [A_29] :
      ( ~ v1_subset_1(k2_struct_0(A_29),u1_struct_0(A_29))
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_7] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_7)),A_7)
      | ~ l1_struct_0(k2_yellow_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_102,plain,(
    ! [A_7] :
      ( ~ v1_subset_1(A_7,A_7)
      | ~ l1_struct_0(k2_yellow_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_97])).

tff(c_216,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_213,c_102])).

tff(c_235,plain,(
    ~ l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_216])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.13/1.26  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.13/1.26  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.13/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.13/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.13/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.13/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.26  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.13/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.26  
% 2.13/1.27  tff(f_46, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.13/1.27  tff(f_42, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.13/1.27  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.13/1.27  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.13/1.27  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.13/1.27  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 2.13/1.27  tff(f_50, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.13/1.27  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.13/1.27  tff(f_38, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.13/1.27  tff(c_14, plain, (![A_6]: (l1_orders_2(k2_yellow_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.27  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.27  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_28, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.27  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.27  tff(c_35, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.13/1.27  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_30, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_130, plain, (![B_39, A_40]: (v1_subset_1(u1_struct_0(B_39), u1_struct_0(A_40)) | ~m1_subset_1(u1_struct_0(B_39), k1_zfmisc_1(u1_struct_0(A_40))) | ~v1_tex_2(B_39, A_40) | ~m1_pre_topc(B_39, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.27  tff(c_142, plain, (![B_39]: (v1_subset_1(u1_struct_0(B_39), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0(B_39), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_39, '#skF_2') | ~m1_pre_topc(B_39, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_130])).
% 2.13/1.27  tff(c_197, plain, (![B_47]: (v1_subset_1(u1_struct_0(B_47), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_47, '#skF_2') | ~m1_pre_topc(B_47, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_142])).
% 2.13/1.27  tff(c_207, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_35, c_197])).
% 2.13/1.27  tff(c_213, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_207])).
% 2.13/1.27  tff(c_16, plain, (![A_7]: (u1_struct_0(k2_yellow_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.27  tff(c_71, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.27  tff(c_76, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_orders_2(A_27))), inference(resolution, [status(thm)], [c_10, c_71])).
% 2.13/1.27  tff(c_79, plain, (![A_6]: (u1_struct_0(k2_yellow_1(A_6))=k2_struct_0(k2_yellow_1(A_6)))), inference(resolution, [status(thm)], [c_14, c_76])).
% 2.13/1.27  tff(c_81, plain, (![A_6]: (k2_struct_0(k2_yellow_1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 2.13/1.27  tff(c_91, plain, (![A_29]: (~v1_subset_1(k2_struct_0(A_29), u1_struct_0(A_29)) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.27  tff(c_97, plain, (![A_7]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_7)), A_7) | ~l1_struct_0(k2_yellow_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_91])).
% 2.13/1.27  tff(c_102, plain, (![A_7]: (~v1_subset_1(A_7, A_7) | ~l1_struct_0(k2_yellow_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_97])).
% 2.13/1.27  tff(c_216, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_213, c_102])).
% 2.13/1.27  tff(c_235, plain, (~l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_216])).
% 2.13/1.27  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_235])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 42
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 2
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 10
% 2.13/1.27  #Demod        : 31
% 2.13/1.27  #Tautology    : 11
% 2.13/1.27  #SimpNegUnit  : 0
% 2.13/1.27  #BackRed      : 0
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.29
% 2.13/1.27  Parsing              : 0.15
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.18
% 2.13/1.27  Inferencing          : 0.07
% 2.13/1.27  Reduction            : 0.06
% 2.13/1.27  Demodulation         : 0.04
% 2.13/1.27  BG Simplification    : 0.01
% 2.13/1.27  Subsumption          : 0.03
% 2.13/1.27  Abstraction          : 0.01
% 2.13/1.27  MUC search           : 0.00
% 2.13/1.27  Cooper               : 0.00
% 2.13/1.27  Total                : 0.51
% 2.13/1.27  Index Insertion      : 0.00
% 2.13/1.27  Index Deletion       : 0.00
% 2.13/1.27  Index Matching       : 0.00
% 2.13/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
