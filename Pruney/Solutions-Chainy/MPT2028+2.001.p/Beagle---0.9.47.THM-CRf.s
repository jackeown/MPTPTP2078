%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:18 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 217 expanded)
%              Number of leaves         :   41 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 858 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k4_waybel_1,type,(
    k4_waybel_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k6_waybel_0,type,(
    k6_waybel_0: ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & v8_pre_topc(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_waybel_9(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => v5_pre_topc(k4_waybel_1(A,C),A,A) )
             => v4_pre_topc(k6_waybel_0(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_9)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(c_40,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_55,plain,(
    ! [A_48] :
      ( l1_orders_2(A_48)
      | ~ l1_waybel_9(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_59,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_44,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_73,plain,(
    ! [A_56,B_57] :
      ( v1_funct_1(k4_waybel_1(A_56,B_57))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_76,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_79,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_76])).

tff(c_80,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_16,plain,(
    ! [A_31] :
      ( ~ v2_struct_0(A_31)
      | ~ v1_lattice3(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_16])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_44,c_83])).

tff(c_89,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    ! [A_49] :
      ( l1_pre_topc(A_49)
      | ~ l1_waybel_9(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_88,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_96,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k6_waybel_0(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_64,B_65] :
      ( v1_xboole_0(k6_waybel_0(A_64,B_65))
      | ~ v1_xboole_0(u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_109,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_112,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_109])).

tff(c_113,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_112])).

tff(c_114,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_52,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_36,plain,(
    ! [C_47] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_47),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_47,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_30,plain,(
    ! [A_37,B_39] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ v8_pre_topc(A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_22,plain,(
    ! [A_34,B_35] :
      ( v1_funct_2(k4_waybel_1(A_34,B_35),u1_struct_0(A_34),u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k6_domain_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_40,B_42] :
      ( k8_relset_1(u1_struct_0(A_40),u1_struct_0(A_40),k4_waybel_1(A_40,B_42),k6_domain_1(u1_struct_0(A_40),B_42)) = k6_waybel_0(A_40,B_42)
      | ~ m1_subset_1(B_42,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | ~ v2_lattice3(A_40)
      | ~ v5_orders_2(A_40)
      | ~ v3_orders_2(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k4_waybel_1(A_34,B_35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34),u1_struct_0(A_34))))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_157,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_87),u1_struct_0(B_88),C_89,D_90),A_87)
      | ~ v4_pre_topc(D_90,B_88)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ v5_pre_topc(C_89,A_87,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_89,u1_struct_0(A_87),u1_struct_0(B_88))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,(
    ! [A_101,B_102,D_103] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_101),u1_struct_0(A_101),k4_waybel_1(A_101,B_102),D_103),A_101)
      | ~ v4_pre_topc(D_103,A_101)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v5_pre_topc(k4_waybel_1(A_101,B_102),A_101,A_101)
      | ~ v1_funct_2(k4_waybel_1(A_101,B_102),u1_struct_0(A_101),u1_struct_0(A_101))
      | ~ v1_funct_1(k4_waybel_1(A_101,B_102))
      | ~ l1_pre_topc(A_101)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_195,plain,(
    ! [A_107,B_108] :
      ( v4_pre_topc(k6_waybel_0(A_107,B_108),A_107)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_107),B_108),A_107)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_107),B_108),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v5_pre_topc(k4_waybel_1(A_107,B_108),A_107,A_107)
      | ~ v1_funct_2(k4_waybel_1(A_107,B_108),u1_struct_0(A_107),u1_struct_0(A_107))
      | ~ v1_funct_1(k4_waybel_1(A_107,B_108))
      | ~ l1_pre_topc(A_107)
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | v2_struct_0(A_107)
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | ~ v2_lattice3(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v3_orders_2(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_185])).

tff(c_200,plain,(
    ! [A_109,B_110] :
      ( v4_pre_topc(k6_waybel_0(A_109,B_110),A_109)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_109),B_110),A_109)
      | ~ v5_pre_topc(k4_waybel_1(A_109,B_110),A_109,A_109)
      | ~ v1_funct_2(k4_waybel_1(A_109,B_110),u1_struct_0(A_109),u1_struct_0(A_109))
      | ~ v1_funct_1(k4_waybel_1(A_109,B_110))
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109)
      | ~ l1_orders_2(A_109)
      | ~ v2_lattice3(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | v1_xboole_0(u1_struct_0(A_109)) ) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_205,plain,(
    ! [A_111,B_112] :
      ( v4_pre_topc(k6_waybel_0(A_111,B_112),A_111)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_111),B_112),A_111)
      | ~ v5_pre_topc(k4_waybel_1(A_111,B_112),A_111,A_111)
      | ~ v1_funct_1(k4_waybel_1(A_111,B_112))
      | ~ l1_pre_topc(A_111)
      | ~ v2_lattice3(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v1_xboole_0(u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_22,c_200])).

tff(c_212,plain,(
    ! [A_113,B_114] :
      ( v4_pre_topc(k6_waybel_0(A_113,B_114),A_113)
      | ~ v5_pre_topc(k4_waybel_1(A_113,B_114),A_113,A_113)
      | ~ v1_funct_1(k4_waybel_1(A_113,B_114))
      | ~ v2_lattice3(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v1_xboole_0(u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v8_pre_topc(A_113)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_30,c_205])).

tff(c_215,plain,(
    ! [C_47] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_47),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_47))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_47,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_212])).

tff(c_218,plain,(
    ! [C_47] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_47),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_47))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_47,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64,c_52,c_59,c_50,c_46,c_42,c_215])).

tff(c_220,plain,(
    ! [C_115] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_115),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_115))
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_114,c_218])).

tff(c_34,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_223,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_220,c_34])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_88,c_223])).

tff(c_228,plain,(
    v1_xboole_0(k6_waybel_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v4_pre_topc(B_6,A_4)
      | ~ v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_237,plain,(
    ! [A_122,B_123] :
      ( v4_pre_topc(k6_waybel_0(A_122,B_123),A_122)
      | ~ v1_xboole_0(k6_waybel_0(A_122,B_123))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_240,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_34])).

tff(c_243,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_38,c_54,c_64,c_228,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.34  
% 2.71/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.35  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.71/1.35  
% 2.71/1.35  %Foreground sorts:
% 2.71/1.35  
% 2.71/1.35  
% 2.71/1.35  %Background operators:
% 2.71/1.35  
% 2.71/1.35  
% 2.71/1.35  %Foreground operators:
% 2.71/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.71/1.35  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.71/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.71/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.71/1.35  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.71/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.71/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.71/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.71/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.71/1.35  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.35  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.71/1.35  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.71/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.71/1.35  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.71/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.35  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.71/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.35  
% 2.71/1.37  tff(f_160, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.71/1.37  tff(f_106, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.71/1.37  tff(f_100, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.71/1.37  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.71/1.37  tff(f_87, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k6_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 2.71/1.37  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.71/1.37  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.71/1.37  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.71/1.37  tff(f_133, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.71/1.37  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.71/1.37  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.71/1.37  tff(c_40, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_55, plain, (![A_48]: (l1_orders_2(A_48) | ~l1_waybel_9(A_48))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.71/1.37  tff(c_59, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_40, c_55])).
% 2.71/1.37  tff(c_44, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_73, plain, (![A_56, B_57]: (v1_funct_1(k4_waybel_1(A_56, B_57)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.37  tff(c_76, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_73])).
% 2.71/1.37  tff(c_79, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_76])).
% 2.71/1.37  tff(c_80, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_79])).
% 2.71/1.37  tff(c_16, plain, (![A_31]: (~v2_struct_0(A_31) | ~v1_lattice3(A_31) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.37  tff(c_83, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_80, c_16])).
% 2.71/1.37  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_44, c_83])).
% 2.71/1.37  tff(c_89, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_79])).
% 2.71/1.37  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_60, plain, (![A_49]: (l1_pre_topc(A_49) | ~l1_waybel_9(A_49))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.71/1.37  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_60])).
% 2.71/1.37  tff(c_88, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_79])).
% 2.71/1.37  tff(c_96, plain, (![A_60, B_61]: (m1_subset_1(k6_waybel_0(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_orders_2(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.71/1.37  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_106, plain, (![A_64, B_65]: (v1_xboole_0(k6_waybel_0(A_64, B_65)) | ~v1_xboole_0(u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.71/1.37  tff(c_109, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_106])).
% 2.71/1.37  tff(c_112, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_109])).
% 2.71/1.37  tff(c_113, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_89, c_112])).
% 2.71/1.37  tff(c_114, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_113])).
% 2.71/1.37  tff(c_52, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_50, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_46, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_42, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_36, plain, (![C_47]: (v5_pre_topc(k4_waybel_1('#skF_2', C_47), '#skF_2', '#skF_2') | ~m1_subset_1(C_47, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_30, plain, (![A_37, B_39]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~v8_pre_topc(A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.71/1.37  tff(c_22, plain, (![A_34, B_35]: (v1_funct_2(k4_waybel_1(A_34, B_35), u1_struct_0(A_34), u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.37  tff(c_14, plain, (![A_29, B_30]: (m1_subset_1(k6_domain_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.37  tff(c_32, plain, (![A_40, B_42]: (k8_relset_1(u1_struct_0(A_40), u1_struct_0(A_40), k4_waybel_1(A_40, B_42), k6_domain_1(u1_struct_0(A_40), B_42))=k6_waybel_0(A_40, B_42) | ~m1_subset_1(B_42, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | ~v2_lattice3(A_40) | ~v5_orders_2(A_40) | ~v3_orders_2(A_40))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.71/1.37  tff(c_20, plain, (![A_34, B_35]: (m1_subset_1(k4_waybel_1(A_34, B_35), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34), u1_struct_0(A_34)))) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.37  tff(c_157, plain, (![A_87, B_88, C_89, D_90]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_87), u1_struct_0(B_88), C_89, D_90), A_87) | ~v4_pre_topc(D_90, B_88) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(B_88))) | ~v5_pre_topc(C_89, A_87, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87), u1_struct_0(B_88)))) | ~v1_funct_2(C_89, u1_struct_0(A_87), u1_struct_0(B_88)) | ~v1_funct_1(C_89) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.37  tff(c_185, plain, (![A_101, B_102, D_103]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_101), u1_struct_0(A_101), k4_waybel_1(A_101, B_102), D_103), A_101) | ~v4_pre_topc(D_103, A_101) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(A_101))) | ~v5_pre_topc(k4_waybel_1(A_101, B_102), A_101, A_101) | ~v1_funct_2(k4_waybel_1(A_101, B_102), u1_struct_0(A_101), u1_struct_0(A_101)) | ~v1_funct_1(k4_waybel_1(A_101, B_102)) | ~l1_pre_topc(A_101) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | v2_struct_0(A_101))), inference(resolution, [status(thm)], [c_20, c_157])).
% 2.71/1.37  tff(c_195, plain, (![A_107, B_108]: (v4_pre_topc(k6_waybel_0(A_107, B_108), A_107) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_107), B_108), A_107) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_107), B_108), k1_zfmisc_1(u1_struct_0(A_107))) | ~v5_pre_topc(k4_waybel_1(A_107, B_108), A_107, A_107) | ~v1_funct_2(k4_waybel_1(A_107, B_108), u1_struct_0(A_107), u1_struct_0(A_107)) | ~v1_funct_1(k4_waybel_1(A_107, B_108)) | ~l1_pre_topc(A_107) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | v2_struct_0(A_107) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | ~v2_lattice3(A_107) | ~v5_orders_2(A_107) | ~v3_orders_2(A_107))), inference(superposition, [status(thm), theory('equality')], [c_32, c_185])).
% 2.71/1.37  tff(c_200, plain, (![A_109, B_110]: (v4_pre_topc(k6_waybel_0(A_109, B_110), A_109) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_109), B_110), A_109) | ~v5_pre_topc(k4_waybel_1(A_109, B_110), A_109, A_109) | ~v1_funct_2(k4_waybel_1(A_109, B_110), u1_struct_0(A_109), u1_struct_0(A_109)) | ~v1_funct_1(k4_waybel_1(A_109, B_110)) | ~l1_pre_topc(A_109) | v2_struct_0(A_109) | ~l1_orders_2(A_109) | ~v2_lattice3(A_109) | ~v5_orders_2(A_109) | ~v3_orders_2(A_109) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | v1_xboole_0(u1_struct_0(A_109)))), inference(resolution, [status(thm)], [c_14, c_195])).
% 2.71/1.37  tff(c_205, plain, (![A_111, B_112]: (v4_pre_topc(k6_waybel_0(A_111, B_112), A_111) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_111), B_112), A_111) | ~v5_pre_topc(k4_waybel_1(A_111, B_112), A_111, A_111) | ~v1_funct_1(k4_waybel_1(A_111, B_112)) | ~l1_pre_topc(A_111) | ~v2_lattice3(A_111) | ~v5_orders_2(A_111) | ~v3_orders_2(A_111) | v1_xboole_0(u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_22, c_200])).
% 2.71/1.37  tff(c_212, plain, (![A_113, B_114]: (v4_pre_topc(k6_waybel_0(A_113, B_114), A_113) | ~v5_pre_topc(k4_waybel_1(A_113, B_114), A_113, A_113) | ~v1_funct_1(k4_waybel_1(A_113, B_114)) | ~v2_lattice3(A_113) | ~v5_orders_2(A_113) | ~v3_orders_2(A_113) | v1_xboole_0(u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v8_pre_topc(A_113) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_30, c_205])).
% 2.71/1.37  tff(c_215, plain, (![C_47]: (v4_pre_topc(k6_waybel_0('#skF_2', C_47), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_47)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_47, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_212])).
% 2.71/1.37  tff(c_218, plain, (![C_47]: (v4_pre_topc(k6_waybel_0('#skF_2', C_47), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_47)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_47, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64, c_52, c_59, c_50, c_46, c_42, c_215])).
% 2.71/1.37  tff(c_220, plain, (![C_115]: (v4_pre_topc(k6_waybel_0('#skF_2', C_115), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_115)) | ~m1_subset_1(C_115, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_89, c_114, c_218])).
% 2.71/1.37  tff(c_34, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.71/1.37  tff(c_223, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_220, c_34])).
% 2.71/1.37  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_88, c_223])).
% 2.71/1.37  tff(c_228, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_113])).
% 2.71/1.37  tff(c_4, plain, (![B_6, A_4]: (v4_pre_topc(B_6, A_4) | ~v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.37  tff(c_237, plain, (![A_122, B_123]: (v4_pre_topc(k6_waybel_0(A_122, B_123), A_122) | ~v1_xboole_0(k6_waybel_0(A_122, B_123)) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_96, c_4])).
% 2.71/1.37  tff(c_240, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_237, c_34])).
% 2.71/1.37  tff(c_243, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_38, c_54, c_64, c_228, c_240])).
% 2.71/1.37  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_243])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 33
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 2
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 4
% 2.71/1.37  #Demod        : 22
% 2.71/1.37  #Tautology    : 4
% 2.71/1.37  #SimpNegUnit  : 4
% 2.71/1.37  #BackRed      : 0
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.32
% 2.71/1.37  Parsing              : 0.18
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.27
% 2.71/1.37  Inferencing          : 0.12
% 2.71/1.37  Reduction            : 0.07
% 2.71/1.37  Demodulation         : 0.04
% 2.71/1.37  BG Simplification    : 0.02
% 2.71/1.37  Subsumption          : 0.04
% 2.71/1.37  Abstraction          : 0.01
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.63
% 2.71/1.37  Index Insertion      : 0.00
% 2.71/1.37  Index Deletion       : 0.00
% 2.71/1.37  Index Matching       : 0.00
% 2.71/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
