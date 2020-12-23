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

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 246 expanded)
%              Number of leaves         :   29 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 573 expanded)
%              Number of equality atoms :   11 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_12,plain,(
    ! [A_7] : l1_orders_2(k2_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v1_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_92,plain,(
    ! [B_32,A_33] :
      ( l1_pre_topc(B_32)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_102,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_98])).

tff(c_20,plain,(
    ! [A_12] :
      ( m1_pre_topc(A_12,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_108,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,(
    ! [B_34] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_34,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_123,plain,(
    ! [B_36] :
      ( m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(B_36,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_114])).

tff(c_126,plain,
    ( m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_123])).

tff(c_130,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_133,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_133])).

tff(c_139,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( m1_subset_1(u1_struct_0(B_11),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_232,plain,(
    ! [B_43,A_44] :
      ( v1_subset_1(u1_struct_0(B_43),u1_struct_0(A_44))
      | ~ v1_tex_2(B_43,A_44)
      | ~ m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_276,plain,(
    ! [B_11,A_9] :
      ( v1_subset_1(u1_struct_0(B_11),u1_struct_0(A_9))
      | ~ v1_tex_2(B_11,A_9)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_232])).

tff(c_140,plain,(
    ! [B_37,A_38] :
      ( v1_tex_2(B_37,A_38)
      | ~ v1_subset_1(u1_struct_0(B_37),u1_struct_0(A_38))
      | ~ m1_subset_1(u1_struct_0(B_37),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_328,plain,(
    ! [B_51,A_52] :
      ( v1_tex_2(B_51,A_52)
      | ~ v1_subset_1(u1_struct_0(B_51),u1_struct_0(A_52))
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_334,plain,(
    ! [B_51] :
      ( v1_tex_2(B_51,'#skF_2')
      | ~ v1_subset_1(u1_struct_0(B_51),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_51,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_328])).

tff(c_372,plain,(
    ! [B_55] :
      ( v1_tex_2(B_55,'#skF_2')
      | ~ v1_subset_1(u1_struct_0(B_55),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_334])).

tff(c_376,plain,(
    ! [B_11] :
      ( v1_tex_2(B_11,'#skF_2')
      | ~ m1_pre_topc(B_11,'#skF_2')
      | ~ v1_tex_2(B_11,'#skF_1')
      | ~ m1_pre_topc(B_11,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_276,c_372])).

tff(c_445,plain,(
    ! [B_60] :
      ( v1_tex_2(B_60,'#skF_2')
      | ~ m1_pre_topc(B_60,'#skF_2')
      | ~ v1_tex_2(B_60,'#skF_1')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_376])).

tff(c_138,plain,(
    m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_24,plain,(
    ! [B_17,A_13] :
      ( v1_tex_2(B_17,A_13)
      | ~ v1_subset_1(u1_struct_0(B_17),u1_struct_0(A_13))
      | ~ m1_subset_1(u1_struct_0(B_17),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_pre_topc(B_17,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_176,plain,
    ( v1_tex_2('#skF_1','#skF_1')
    | ~ v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_138,c_24])).

tff(c_179,plain,
    ( v1_tex_2('#skF_1','#skF_1')
    | ~ v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_176])).

tff(c_215,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_218,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_218])).

tff(c_223,plain,
    ( ~ v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | v1_tex_2('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_231,plain,(
    ~ v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_343,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(u1_struct_0(B_53),u1_struct_0(A_54))
      | ~ v1_tex_2(B_53,A_54)
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_18,c_232])).

tff(c_358,plain,(
    ! [B_53] :
      ( v1_subset_1(u1_struct_0(B_53),u1_struct_0('#skF_1'))
      | ~ v1_tex_2(B_53,'#skF_2')
      | ~ m1_pre_topc(B_53,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_343])).

tff(c_388,plain,(
    ! [B_56] :
      ( v1_subset_1(u1_struct_0(B_56),u1_struct_0('#skF_1'))
      | ~ v1_tex_2(B_56,'#skF_2')
      | ~ m1_pre_topc(B_56,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_358])).

tff(c_403,plain,
    ( v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_388])).

tff(c_414,plain,
    ( v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_403])).

tff(c_415,plain,(
    ~ v1_tex_2('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_414])).

tff(c_451,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ v1_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_445,c_415])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_139,c_451])).

tff(c_458,plain,(
    v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_14,plain,(
    ! [A_8] : u1_struct_0(k2_yellow_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_orders_2(A_28) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_67,plain,(
    ! [A_7] : u1_struct_0(k2_yellow_1(A_7)) = k2_struct_0(k2_yellow_1(A_7)) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_69,plain,(
    ! [A_7] : k2_struct_0(k2_yellow_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_79,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(k2_struct_0(A_30),u1_struct_0(A_30))
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_8] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_8)),A_8)
      | ~ l1_struct_0(k2_yellow_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_90,plain,(
    ! [A_8] :
      ( ~ v1_subset_1(A_8,A_8)
      | ~ l1_struct_0(k2_yellow_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_88])).

tff(c_461,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_458,c_90])).

tff(c_470,plain,(
    ~ l1_orders_2(k2_yellow_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_461])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:42:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.32  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1
% 2.52/1.32  
% 2.52/1.32  %Foreground sorts:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Background operators:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Foreground operators:
% 2.52/1.32  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.52/1.32  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.52/1.32  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.52/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.52/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.52/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.32  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.52/1.32  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.52/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.52/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.52/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.32  
% 2.52/1.33  tff(f_49, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.52/1.33  tff(f_45, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.52/1.33  tff(f_89, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.52/1.33  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.52/1.33  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.52/1.33  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.52/1.33  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.52/1.33  tff(f_53, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.52/1.33  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.52/1.33  tff(f_41, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.52/1.33  tff(c_12, plain, (![A_7]: (l1_orders_2(k2_yellow_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.52/1.33  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.33  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.33  tff(c_26, plain, (v1_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.33  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.33  tff(c_92, plain, (![B_32, A_33]: (l1_pre_topc(B_32) | ~m1_pre_topc(B_32, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.33  tff(c_98, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.52/1.33  tff(c_102, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_98])).
% 2.52/1.33  tff(c_20, plain, (![A_12]: (m1_pre_topc(A_12, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.33  tff(c_28, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.33  tff(c_108, plain, (![B_34, A_35]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.33  tff(c_114, plain, (![B_34]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(B_34, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_108])).
% 2.52/1.33  tff(c_123, plain, (![B_36]: (m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(B_36, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_114])).
% 2.52/1.33  tff(c_126, plain, (m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_123])).
% 2.52/1.33  tff(c_130, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 2.52/1.33  tff(c_133, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_130])).
% 2.52/1.33  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_133])).
% 2.52/1.33  tff(c_139, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 2.52/1.33  tff(c_18, plain, (![B_11, A_9]: (m1_subset_1(u1_struct_0(B_11), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.33  tff(c_232, plain, (![B_43, A_44]: (v1_subset_1(u1_struct_0(B_43), u1_struct_0(A_44)) | ~v1_tex_2(B_43, A_44) | ~m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.52/1.33  tff(c_276, plain, (![B_11, A_9]: (v1_subset_1(u1_struct_0(B_11), u1_struct_0(A_9)) | ~v1_tex_2(B_11, A_9) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_18, c_232])).
% 2.52/1.33  tff(c_140, plain, (![B_37, A_38]: (v1_tex_2(B_37, A_38) | ~v1_subset_1(u1_struct_0(B_37), u1_struct_0(A_38)) | ~m1_subset_1(u1_struct_0(B_37), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.52/1.33  tff(c_328, plain, (![B_51, A_52]: (v1_tex_2(B_51, A_52) | ~v1_subset_1(u1_struct_0(B_51), u1_struct_0(A_52)) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_18, c_140])).
% 2.52/1.33  tff(c_334, plain, (![B_51]: (v1_tex_2(B_51, '#skF_2') | ~v1_subset_1(u1_struct_0(B_51), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_51, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_328])).
% 2.52/1.33  tff(c_372, plain, (![B_55]: (v1_tex_2(B_55, '#skF_2') | ~v1_subset_1(u1_struct_0(B_55), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_334])).
% 2.52/1.33  tff(c_376, plain, (![B_11]: (v1_tex_2(B_11, '#skF_2') | ~m1_pre_topc(B_11, '#skF_2') | ~v1_tex_2(B_11, '#skF_1') | ~m1_pre_topc(B_11, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_276, c_372])).
% 2.52/1.33  tff(c_445, plain, (![B_60]: (v1_tex_2(B_60, '#skF_2') | ~m1_pre_topc(B_60, '#skF_2') | ~v1_tex_2(B_60, '#skF_1') | ~m1_pre_topc(B_60, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_376])).
% 2.52/1.33  tff(c_138, plain, (m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_126])).
% 2.52/1.33  tff(c_24, plain, (![B_17, A_13]: (v1_tex_2(B_17, A_13) | ~v1_subset_1(u1_struct_0(B_17), u1_struct_0(A_13)) | ~m1_subset_1(u1_struct_0(B_17), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_pre_topc(B_17, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.52/1.33  tff(c_176, plain, (v1_tex_2('#skF_1', '#skF_1') | ~v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_138, c_24])).
% 2.52/1.33  tff(c_179, plain, (v1_tex_2('#skF_1', '#skF_1') | ~v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_176])).
% 2.52/1.33  tff(c_215, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_179])).
% 2.52/1.33  tff(c_218, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_215])).
% 2.52/1.33  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_218])).
% 2.52/1.33  tff(c_223, plain, (~v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | v1_tex_2('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_179])).
% 2.52/1.33  tff(c_231, plain, (~v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_223])).
% 2.52/1.33  tff(c_343, plain, (![B_53, A_54]: (v1_subset_1(u1_struct_0(B_53), u1_struct_0(A_54)) | ~v1_tex_2(B_53, A_54) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_18, c_232])).
% 2.52/1.33  tff(c_358, plain, (![B_53]: (v1_subset_1(u1_struct_0(B_53), u1_struct_0('#skF_1')) | ~v1_tex_2(B_53, '#skF_2') | ~m1_pre_topc(B_53, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_343])).
% 2.52/1.33  tff(c_388, plain, (![B_56]: (v1_subset_1(u1_struct_0(B_56), u1_struct_0('#skF_1')) | ~v1_tex_2(B_56, '#skF_2') | ~m1_pre_topc(B_56, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_358])).
% 2.52/1.33  tff(c_403, plain, (v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_388])).
% 2.52/1.33  tff(c_414, plain, (v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~v1_tex_2('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_403])).
% 2.52/1.33  tff(c_415, plain, (~v1_tex_2('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_231, c_414])).
% 2.52/1.33  tff(c_451, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~v1_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_445, c_415])).
% 2.52/1.33  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_139, c_451])).
% 2.52/1.33  tff(c_458, plain, (v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_223])).
% 2.52/1.33  tff(c_14, plain, (![A_8]: (u1_struct_0(k2_yellow_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.52/1.33  tff(c_59, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.33  tff(c_64, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_orders_2(A_28))), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.52/1.33  tff(c_67, plain, (![A_7]: (u1_struct_0(k2_yellow_1(A_7))=k2_struct_0(k2_yellow_1(A_7)))), inference(resolution, [status(thm)], [c_12, c_64])).
% 2.52/1.33  tff(c_69, plain, (![A_7]: (k2_struct_0(k2_yellow_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_67])).
% 2.52/1.33  tff(c_79, plain, (![A_30]: (~v1_subset_1(k2_struct_0(A_30), u1_struct_0(A_30)) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.52/1.33  tff(c_88, plain, (![A_8]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_8)), A_8) | ~l1_struct_0(k2_yellow_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_79])).
% 2.52/1.33  tff(c_90, plain, (![A_8]: (~v1_subset_1(A_8, A_8) | ~l1_struct_0(k2_yellow_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_88])).
% 2.52/1.33  tff(c_461, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_458, c_90])).
% 2.52/1.33  tff(c_470, plain, (~l1_orders_2(k2_yellow_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_461])).
% 2.52/1.33  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_470])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 89
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 5
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 11
% 2.52/1.33  #Demod        : 49
% 2.52/1.33  #Tautology    : 16
% 2.52/1.33  #SimpNegUnit  : 3
% 2.52/1.33  #BackRed      : 0
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.34  Preprocessing        : 0.30
% 2.52/1.34  Parsing              : 0.16
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.27
% 2.52/1.34  Inferencing          : 0.10
% 2.52/1.34  Reduction            : 0.08
% 2.52/1.34  Demodulation         : 0.06
% 2.52/1.34  BG Simplification    : 0.01
% 2.52/1.34  Subsumption          : 0.06
% 2.52/1.34  Abstraction          : 0.01
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.60
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
