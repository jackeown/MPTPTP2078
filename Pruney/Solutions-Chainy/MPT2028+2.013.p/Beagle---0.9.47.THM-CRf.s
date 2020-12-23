%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:20 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 131 expanded)
%              Number of leaves         :   39 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 ( 511 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k7_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k7_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_waybel_0(A,B)) = k6_domain_1(u1_struct_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_waybel_9)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).

tff(f_50,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_51,plain,(
    ! [A_45] :
      ( l1_orders_2(A_45)
      | ~ l1_waybel_9(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_38,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63,plain,(
    ! [A_49,B_50] :
      ( v1_funct_1(k4_waybel_1(A_49,B_50))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_69,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_66])).

tff(c_70,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_12,plain,(
    ! [A_27] :
      ( ~ v2_struct_0(A_27)
      | ~ v2_lattice3(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_38,c_73])).

tff(c_78,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_79,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    ! [A_46] :
      ( l1_pre_topc(A_46)
      | ~ l1_waybel_9(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_48,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    ! [C_44] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_44),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_24,plain,(
    ! [A_31,B_33] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_31),B_33),A_31)
      | ~ v8_pre_topc(A_31)
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_28,B_29] :
      ( v1_funct_2(k4_waybel_1(A_28,B_29),u1_struct_0(A_28),u1_struct_0(A_28))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k4_waybel_1(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(A_28))))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93,plain,(
    ! [A_63,B_64] :
      ( k7_relset_1(u1_struct_0(A_63),u1_struct_0(A_63),k4_waybel_1(A_63,B_64),k6_waybel_0(A_63,B_64)) = k6_domain_1(u1_struct_0(A_63),B_64)
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v2_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v3_orders_2(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k7_relset_1(A_1,B_2,C_3,D_4),k1_zfmisc_1(B_2))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_68),B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(k4_waybel_1(A_68,B_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(A_68))))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l1_orders_2(A_68)
      | ~ v2_lattice3(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v3_orders_2(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_117,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_28),B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ v2_lattice3(A_28)
      | ~ v5_orders_2(A_28)
      | ~ v3_orders_2(A_28)
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_28,plain,(
    ! [A_37,B_39] :
      ( k8_relset_1(u1_struct_0(A_37),u1_struct_0(A_37),k4_waybel_1(A_37,B_39),k6_domain_1(u1_struct_0(A_37),B_39)) = k6_waybel_0(A_37,B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v2_lattice3(A_37)
      | ~ v5_orders_2(A_37)
      | ~ v3_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_134,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_84),u1_struct_0(B_85),C_86,D_87),A_84)
      | ~ v4_pre_topc(D_87,B_85)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0(B_85)))
      | ~ v5_pre_topc(C_86,A_84,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),u1_struct_0(B_85))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_84),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ l1_pre_topc(B_85)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [A_88,B_89,D_90] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_88),u1_struct_0(A_88),k4_waybel_1(A_88,B_89),D_90),A_88)
      | ~ v4_pre_topc(D_90,A_88)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ v5_pre_topc(k4_waybel_1(A_88,B_89),A_88,A_88)
      | ~ v1_funct_2(k4_waybel_1(A_88,B_89),u1_struct_0(A_88),u1_struct_0(A_88))
      | ~ v1_funct_1(k4_waybel_1(A_88,B_89))
      | ~ l1_pre_topc(A_88)
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_14,c_134])).

tff(c_151,plain,(
    ! [A_91,B_92] :
      ( v4_pre_topc(k6_waybel_0(A_91,B_92),A_91)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_91),B_92),A_91)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_91),B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v5_pre_topc(k4_waybel_1(A_91,B_92),A_91,A_91)
      | ~ v1_funct_2(k4_waybel_1(A_91,B_92),u1_struct_0(A_91),u1_struct_0(A_91))
      | ~ v1_funct_1(k4_waybel_1(A_91,B_92))
      | ~ l1_pre_topc(A_91)
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_orders_2(A_91)
      | v2_struct_0(A_91)
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_orders_2(A_91)
      | ~ v2_lattice3(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v3_orders_2(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_155,plain,(
    ! [A_93,B_94] :
      ( v4_pre_topc(k6_waybel_0(A_93,B_94),A_93)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_93),B_94),A_93)
      | ~ v5_pre_topc(k4_waybel_1(A_93,B_94),A_93,A_93)
      | ~ v1_funct_2(k4_waybel_1(A_93,B_94),u1_struct_0(A_93),u1_struct_0(A_93))
      | ~ v1_funct_1(k4_waybel_1(A_93,B_94))
      | ~ l1_pre_topc(A_93)
      | ~ v2_lattice3(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_117,c_151])).

tff(c_160,plain,(
    ! [A_95,B_96] :
      ( v4_pre_topc(k6_waybel_0(A_95,B_96),A_95)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_95),B_96),A_95)
      | ~ v5_pre_topc(k4_waybel_1(A_95,B_96),A_95,A_95)
      | ~ v1_funct_1(k4_waybel_1(A_95,B_96))
      | ~ l1_pre_topc(A_95)
      | ~ v2_lattice3(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_164,plain,(
    ! [A_97,B_98] :
      ( v4_pre_topc(k6_waybel_0(A_97,B_98),A_97)
      | ~ v5_pre_topc(k4_waybel_1(A_97,B_98),A_97,A_97)
      | ~ v1_funct_1(k4_waybel_1(A_97,B_98))
      | ~ v2_lattice3(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | ~ l1_orders_2(A_97)
      | ~ v8_pre_topc(A_97)
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_167,plain,(
    ! [C_44] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_44),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_44))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_164])).

tff(c_170,plain,(
    ! [C_44] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_44),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_44))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_48,c_55,c_46,c_42,c_38,c_167])).

tff(c_172,plain,(
    ! [C_99] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_99),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_99))
      | ~ m1_subset_1(C_99,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_170])).

tff(c_30,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_175,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_172,c_30])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_78,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.49  
% 2.45/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.50  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k7_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.45/1.50  
% 2.45/1.50  %Foreground sorts:
% 2.45/1.50  
% 2.45/1.50  
% 2.45/1.50  %Background operators:
% 2.45/1.50  
% 2.45/1.50  
% 2.45/1.50  %Foreground operators:
% 2.45/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.50  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.45/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.45/1.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.45/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.45/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.50  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.45/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.45/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.45/1.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.45/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.45/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.45/1.50  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.45/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.50  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.45/1.50  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.45/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.45/1.50  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.45/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.50  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.45/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.50  
% 2.45/1.52  tff(f_143, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.45/1.52  tff(f_76, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.45/1.52  tff(f_70, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.45/1.52  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 2.45/1.52  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.45/1.52  tff(f_103, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_waybel_0(A, B)) = k6_domain_1(u1_struct_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_waybel_9)).
% 2.45/1.52  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.45/1.52  tff(f_116, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.45/1.52  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.45/1.52  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_36, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_51, plain, (![A_45]: (l1_orders_2(A_45) | ~l1_waybel_9(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.45/1.52  tff(c_55, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_36, c_51])).
% 2.45/1.52  tff(c_38, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_63, plain, (![A_49, B_50]: (v1_funct_1(k4_waybel_1(A_49, B_50)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.52  tff(c_66, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.45/1.52  tff(c_69, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_66])).
% 2.45/1.52  tff(c_70, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_69])).
% 2.45/1.52  tff(c_12, plain, (![A_27]: (~v2_struct_0(A_27) | ~v2_lattice3(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.52  tff(c_73, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_70, c_12])).
% 2.45/1.52  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_38, c_73])).
% 2.45/1.52  tff(c_78, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_69])).
% 2.45/1.52  tff(c_79, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_69])).
% 2.45/1.52  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_56, plain, (![A_46]: (l1_pre_topc(A_46) | ~l1_waybel_9(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.45/1.52  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.45/1.52  tff(c_48, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_32, plain, (![C_44]: (v5_pre_topc(k4_waybel_1('#skF_2', C_44), '#skF_2', '#skF_2') | ~m1_subset_1(C_44, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_24, plain, (![A_31, B_33]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_31), B_33), A_31) | ~v8_pre_topc(A_31) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.45/1.52  tff(c_16, plain, (![A_28, B_29]: (v1_funct_2(k4_waybel_1(A_28, B_29), u1_struct_0(A_28), u1_struct_0(A_28)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.52  tff(c_14, plain, (![A_28, B_29]: (m1_subset_1(k4_waybel_1(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(A_28)))) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.52  tff(c_93, plain, (![A_63, B_64]: (k7_relset_1(u1_struct_0(A_63), u1_struct_0(A_63), k4_waybel_1(A_63, B_64), k6_waybel_0(A_63, B_64))=k6_domain_1(u1_struct_0(A_63), B_64) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | ~v2_lattice3(A_63) | ~v5_orders_2(A_63) | ~v3_orders_2(A_63))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.45/1.52  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k7_relset_1(A_1, B_2, C_3, D_4), k1_zfmisc_1(B_2)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.52  tff(c_113, plain, (![A_68, B_69]: (m1_subset_1(k6_domain_1(u1_struct_0(A_68), B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(k4_waybel_1(A_68, B_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(A_68)))) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l1_orders_2(A_68) | ~v2_lattice3(A_68) | ~v5_orders_2(A_68) | ~v3_orders_2(A_68))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 2.45/1.52  tff(c_117, plain, (![A_28, B_29]: (m1_subset_1(k6_domain_1(u1_struct_0(A_28), B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~v2_lattice3(A_28) | ~v5_orders_2(A_28) | ~v3_orders_2(A_28) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | v2_struct_0(A_28))), inference(resolution, [status(thm)], [c_14, c_113])).
% 2.45/1.52  tff(c_28, plain, (![A_37, B_39]: (k8_relset_1(u1_struct_0(A_37), u1_struct_0(A_37), k4_waybel_1(A_37, B_39), k6_domain_1(u1_struct_0(A_37), B_39))=k6_waybel_0(A_37, B_39) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v2_lattice3(A_37) | ~v5_orders_2(A_37) | ~v3_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.45/1.52  tff(c_134, plain, (![A_84, B_85, C_86, D_87]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_84), u1_struct_0(B_85), C_86, D_87), A_84) | ~v4_pre_topc(D_87, B_85) | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0(B_85))) | ~v5_pre_topc(C_86, A_84, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), u1_struct_0(B_85)))) | ~v1_funct_2(C_86, u1_struct_0(A_84), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~l1_pre_topc(B_85) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.52  tff(c_142, plain, (![A_88, B_89, D_90]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_88), u1_struct_0(A_88), k4_waybel_1(A_88, B_89), D_90), A_88) | ~v4_pre_topc(D_90, A_88) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~v5_pre_topc(k4_waybel_1(A_88, B_89), A_88, A_88) | ~v1_funct_2(k4_waybel_1(A_88, B_89), u1_struct_0(A_88), u1_struct_0(A_88)) | ~v1_funct_1(k4_waybel_1(A_88, B_89)) | ~l1_pre_topc(A_88) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_14, c_134])).
% 2.45/1.52  tff(c_151, plain, (![A_91, B_92]: (v4_pre_topc(k6_waybel_0(A_91, B_92), A_91) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_91), B_92), A_91) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_91), B_92), k1_zfmisc_1(u1_struct_0(A_91))) | ~v5_pre_topc(k4_waybel_1(A_91, B_92), A_91, A_91) | ~v1_funct_2(k4_waybel_1(A_91, B_92), u1_struct_0(A_91), u1_struct_0(A_91)) | ~v1_funct_1(k4_waybel_1(A_91, B_92)) | ~l1_pre_topc(A_91) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_orders_2(A_91) | v2_struct_0(A_91) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_orders_2(A_91) | ~v2_lattice3(A_91) | ~v5_orders_2(A_91) | ~v3_orders_2(A_91))), inference(superposition, [status(thm), theory('equality')], [c_28, c_142])).
% 2.45/1.52  tff(c_155, plain, (![A_93, B_94]: (v4_pre_topc(k6_waybel_0(A_93, B_94), A_93) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_93), B_94), A_93) | ~v5_pre_topc(k4_waybel_1(A_93, B_94), A_93, A_93) | ~v1_funct_2(k4_waybel_1(A_93, B_94), u1_struct_0(A_93), u1_struct_0(A_93)) | ~v1_funct_1(k4_waybel_1(A_93, B_94)) | ~l1_pre_topc(A_93) | ~v2_lattice3(A_93) | ~v5_orders_2(A_93) | ~v3_orders_2(A_93) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_117, c_151])).
% 2.45/1.52  tff(c_160, plain, (![A_95, B_96]: (v4_pre_topc(k6_waybel_0(A_95, B_96), A_95) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_95), B_96), A_95) | ~v5_pre_topc(k4_waybel_1(A_95, B_96), A_95, A_95) | ~v1_funct_1(k4_waybel_1(A_95, B_96)) | ~l1_pre_topc(A_95) | ~v2_lattice3(A_95) | ~v5_orders_2(A_95) | ~v3_orders_2(A_95) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | v2_struct_0(A_95))), inference(resolution, [status(thm)], [c_16, c_155])).
% 2.45/1.52  tff(c_164, plain, (![A_97, B_98]: (v4_pre_topc(k6_waybel_0(A_97, B_98), A_97) | ~v5_pre_topc(k4_waybel_1(A_97, B_98), A_97, A_97) | ~v1_funct_1(k4_waybel_1(A_97, B_98)) | ~v2_lattice3(A_97) | ~v5_orders_2(A_97) | ~v3_orders_2(A_97) | ~l1_orders_2(A_97) | ~v8_pre_topc(A_97) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_24, c_160])).
% 2.45/1.52  tff(c_167, plain, (![C_44]: (v4_pre_topc(k6_waybel_0('#skF_2', C_44), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_44)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_44, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_164])).
% 2.45/1.52  tff(c_170, plain, (![C_44]: (v4_pre_topc(k6_waybel_0('#skF_2', C_44), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_44)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_44, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_48, c_55, c_46, c_42, c_38, c_167])).
% 2.45/1.52  tff(c_172, plain, (![C_99]: (v4_pre_topc(k6_waybel_0('#skF_2', C_99), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_99)) | ~m1_subset_1(C_99, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_79, c_170])).
% 2.45/1.52  tff(c_30, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.45/1.52  tff(c_175, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_172, c_30])).
% 2.45/1.52  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_78, c_175])).
% 2.45/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.52  
% 2.45/1.52  Inference rules
% 2.45/1.52  ----------------------
% 2.45/1.52  #Ref     : 0
% 2.45/1.52  #Sup     : 24
% 2.45/1.52  #Fact    : 0
% 2.45/1.52  #Define  : 0
% 2.45/1.52  #Split   : 1
% 2.45/1.52  #Chain   : 0
% 2.45/1.52  #Close   : 0
% 2.45/1.52  
% 2.45/1.52  Ordering : KBO
% 2.45/1.52  
% 2.45/1.52  Simplification rules
% 2.45/1.52  ----------------------
% 2.45/1.52  #Subsume      : 3
% 2.45/1.52  #Demod        : 12
% 2.45/1.52  #Tautology    : 5
% 2.45/1.52  #SimpNegUnit  : 1
% 2.45/1.52  #BackRed      : 0
% 2.45/1.52  
% 2.45/1.52  #Partial instantiations: 0
% 2.45/1.52  #Strategies tried      : 1
% 2.45/1.52  
% 2.45/1.52  Timing (in seconds)
% 2.45/1.52  ----------------------
% 2.45/1.52  Preprocessing        : 0.41
% 2.45/1.52  Parsing              : 0.26
% 2.45/1.52  CNF conversion       : 0.02
% 2.45/1.52  Main loop            : 0.23
% 2.45/1.52  Inferencing          : 0.10
% 2.45/1.52  Reduction            : 0.06
% 2.45/1.52  Demodulation         : 0.04
% 2.45/1.52  BG Simplification    : 0.02
% 2.45/1.52  Subsumption          : 0.03
% 2.45/1.52  Abstraction          : 0.01
% 2.45/1.52  MUC search           : 0.00
% 2.45/1.52  Cooper               : 0.00
% 2.45/1.52  Total                : 0.67
% 2.45/1.52  Index Insertion      : 0.00
% 2.45/1.52  Index Deletion       : 0.00
% 2.45/1.52  Index Matching       : 0.00
% 2.45/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
