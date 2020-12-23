%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:19 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 207 expanded)
%              Number of leaves         :   41 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  221 ( 886 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_145,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).

tff(f_46,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    ! [A_43] :
      ( l1_orders_2(A_43)
      | ~ l1_waybel_9(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_42,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,(
    ! [A_50,B_51] :
      ( v1_funct_1(k4_waybel_1(A_50,B_51))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_71,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_74,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_71])).

tff(c_75,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_16,plain,(
    ! [A_27] :
      ( ~ v2_struct_0(A_27)
      | ~ v1_lattice3(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_16])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42,c_78])).

tff(c_83,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_53,plain,(
    ! [A_42] :
      ( l1_pre_topc(A_42)
      | ~ l1_waybel_9(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_10,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_34,plain,(
    ! [C_41] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_41),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28,plain,(
    ! [A_31,B_33] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_31),B_33),A_31)
      | ~ v8_pre_topc(A_31)
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    ! [A_28,B_29] :
      ( v1_funct_2(k4_waybel_1(A_28,B_29),u1_struct_0(A_28),u1_struct_0(A_28))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k6_domain_1(A_25,B_26),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_34,B_36] :
      ( k8_relset_1(u1_struct_0(A_34),u1_struct_0(A_34),k4_waybel_1(A_34,B_36),k6_domain_1(u1_struct_0(A_34),B_36)) = k6_waybel_0(A_34,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v2_lattice3(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v3_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k4_waybel_1(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(A_28))))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_120,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_75),u1_struct_0(B_76),C_77,D_78),A_75)
      | ~ v4_pre_topc(D_78,B_76)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(u1_struct_0(B_76)))
      | ~ v5_pre_topc(C_77,A_75,B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75),u1_struct_0(B_76))))
      | ~ v1_funct_2(C_77,u1_struct_0(A_75),u1_struct_0(B_76))
      | ~ v1_funct_1(C_77)
      | ~ l1_pre_topc(B_76)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_128,plain,(
    ! [A_79,B_80,D_81] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_79),u1_struct_0(A_79),k4_waybel_1(A_79,B_80),D_81),A_79)
      | ~ v4_pre_topc(D_81,A_79)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ v5_pre_topc(k4_waybel_1(A_79,B_80),A_79,A_79)
      | ~ v1_funct_2(k4_waybel_1(A_79,B_80),u1_struct_0(A_79),u1_struct_0(A_79))
      | ~ v1_funct_1(k4_waybel_1(A_79,B_80))
      | ~ l1_pre_topc(A_79)
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_138,plain,(
    ! [A_85,B_86] :
      ( v4_pre_topc(k6_waybel_0(A_85,B_86),A_85)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_85),B_86),A_85)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_85),B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v5_pre_topc(k4_waybel_1(A_85,B_86),A_85,A_85)
      | ~ v1_funct_2(k4_waybel_1(A_85,B_86),u1_struct_0(A_85),u1_struct_0(A_85))
      | ~ v1_funct_1(k4_waybel_1(A_85,B_86))
      | ~ l1_pre_topc(A_85)
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85)
      | v2_struct_0(A_85)
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85)
      | ~ v2_lattice3(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v3_orders_2(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_128])).

tff(c_143,plain,(
    ! [A_87,B_88] :
      ( v4_pre_topc(k6_waybel_0(A_87,B_88),A_87)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_87),B_88),A_87)
      | ~ v5_pre_topc(k4_waybel_1(A_87,B_88),A_87,A_87)
      | ~ v1_funct_2(k4_waybel_1(A_87,B_88),u1_struct_0(A_87),u1_struct_0(A_87))
      | ~ v1_funct_1(k4_waybel_1(A_87,B_88))
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87)
      | ~ l1_orders_2(A_87)
      | ~ v2_lattice3(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | v1_xboole_0(u1_struct_0(A_87)) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_148,plain,(
    ! [A_89,B_90] :
      ( v4_pre_topc(k6_waybel_0(A_89,B_90),A_89)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_89),B_90),A_89)
      | ~ v5_pre_topc(k4_waybel_1(A_89,B_90),A_89,A_89)
      | ~ v1_funct_1(k4_waybel_1(A_89,B_90))
      | ~ l1_pre_topc(A_89)
      | ~ v2_lattice3(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v1_xboole_0(u1_struct_0(A_89))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_152,plain,(
    ! [A_91,B_92] :
      ( v4_pre_topc(k6_waybel_0(A_91,B_92),A_91)
      | ~ v5_pre_topc(k4_waybel_1(A_91,B_92),A_91,A_91)
      | ~ v1_funct_1(k4_waybel_1(A_91,B_92))
      | ~ v2_lattice3(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v1_xboole_0(u1_struct_0(A_91))
      | ~ l1_orders_2(A_91)
      | ~ v8_pre_topc(A_91)
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_28,c_148])).

tff(c_155,plain,(
    ! [C_41] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_41),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_41))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_152])).

tff(c_158,plain,(
    ! [C_41] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_41),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_41))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_57,c_50,c_62,c_48,c_44,c_40,c_155])).

tff(c_159,plain,(
    ! [C_41] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_41),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_41))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_158])).

tff(c_160,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_12,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_163,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_12])).

tff(c_166,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_163])).

tff(c_169,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_169])).

tff(c_177,plain,(
    ! [C_96] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_96),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_96))
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_32,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_180,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_177,c_32])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_83,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:30:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.28  
% 2.41/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.28  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.41/1.28  
% 2.41/1.28  %Foreground sorts:
% 2.41/1.28  
% 2.41/1.28  
% 2.41/1.28  %Background operators:
% 2.41/1.28  
% 2.41/1.28  
% 2.41/1.28  %Foreground operators:
% 2.41/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.28  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.41/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.41/1.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.41/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.41/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.41/1.28  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.41/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.41/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.41/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.41/1.28  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.41/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.28  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.41/1.28  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.41/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.28  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.41/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.28  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.41/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.28  
% 2.41/1.30  tff(f_145, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.41/1.30  tff(f_91, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.41/1.30  tff(f_85, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.41/1.30  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.41/1.30  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.41/1.30  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.41/1.30  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.41/1.30  tff(f_118, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.41/1.30  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.41/1.30  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.41/1.30  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_38, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_58, plain, (![A_43]: (l1_orders_2(A_43) | ~l1_waybel_9(A_43))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.41/1.30  tff(c_62, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.41/1.30  tff(c_42, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_68, plain, (![A_50, B_51]: (v1_funct_1(k4_waybel_1(A_50, B_51)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.30  tff(c_71, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.41/1.30  tff(c_74, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_71])).
% 2.41/1.30  tff(c_75, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 2.41/1.30  tff(c_16, plain, (![A_27]: (~v2_struct_0(A_27) | ~v1_lattice3(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.41/1.30  tff(c_78, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_75, c_16])).
% 2.41/1.30  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_42, c_78])).
% 2.41/1.30  tff(c_83, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 2.41/1.30  tff(c_53, plain, (![A_42]: (l1_pre_topc(A_42) | ~l1_waybel_9(A_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.41/1.30  tff(c_57, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.41/1.30  tff(c_10, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.30  tff(c_84, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_74])).
% 2.41/1.30  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_50, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_40, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_34, plain, (![C_41]: (v5_pre_topc(k4_waybel_1('#skF_2', C_41), '#skF_2', '#skF_2') | ~m1_subset_1(C_41, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_28, plain, (![A_31, B_33]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_31), B_33), A_31) | ~v8_pre_topc(A_31) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.30  tff(c_20, plain, (![A_28, B_29]: (v1_funct_2(k4_waybel_1(A_28, B_29), u1_struct_0(A_28), u1_struct_0(A_28)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.30  tff(c_14, plain, (![A_25, B_26]: (m1_subset_1(k6_domain_1(A_25, B_26), k1_zfmisc_1(A_25)) | ~m1_subset_1(B_26, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.30  tff(c_30, plain, (![A_34, B_36]: (k8_relset_1(u1_struct_0(A_34), u1_struct_0(A_34), k4_waybel_1(A_34, B_36), k6_domain_1(u1_struct_0(A_34), B_36))=k6_waybel_0(A_34, B_36) | ~m1_subset_1(B_36, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | ~v2_lattice3(A_34) | ~v5_orders_2(A_34) | ~v3_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.41/1.30  tff(c_18, plain, (![A_28, B_29]: (m1_subset_1(k4_waybel_1(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(A_28)))) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.30  tff(c_120, plain, (![A_75, B_76, C_77, D_78]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_75), u1_struct_0(B_76), C_77, D_78), A_75) | ~v4_pre_topc(D_78, B_76) | ~m1_subset_1(D_78, k1_zfmisc_1(u1_struct_0(B_76))) | ~v5_pre_topc(C_77, A_75, B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75), u1_struct_0(B_76)))) | ~v1_funct_2(C_77, u1_struct_0(A_75), u1_struct_0(B_76)) | ~v1_funct_1(C_77) | ~l1_pre_topc(B_76) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.30  tff(c_128, plain, (![A_79, B_80, D_81]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_79), u1_struct_0(A_79), k4_waybel_1(A_79, B_80), D_81), A_79) | ~v4_pre_topc(D_81, A_79) | ~m1_subset_1(D_81, k1_zfmisc_1(u1_struct_0(A_79))) | ~v5_pre_topc(k4_waybel_1(A_79, B_80), A_79, A_79) | ~v1_funct_2(k4_waybel_1(A_79, B_80), u1_struct_0(A_79), u1_struct_0(A_79)) | ~v1_funct_1(k4_waybel_1(A_79, B_80)) | ~l1_pre_topc(A_79) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l1_orders_2(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_18, c_120])).
% 2.41/1.30  tff(c_138, plain, (![A_85, B_86]: (v4_pre_topc(k6_waybel_0(A_85, B_86), A_85) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_85), B_86), A_85) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_85), B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~v5_pre_topc(k4_waybel_1(A_85, B_86), A_85, A_85) | ~v1_funct_2(k4_waybel_1(A_85, B_86), u1_struct_0(A_85), u1_struct_0(A_85)) | ~v1_funct_1(k4_waybel_1(A_85, B_86)) | ~l1_pre_topc(A_85) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_orders_2(A_85) | v2_struct_0(A_85) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_orders_2(A_85) | ~v2_lattice3(A_85) | ~v5_orders_2(A_85) | ~v3_orders_2(A_85))), inference(superposition, [status(thm), theory('equality')], [c_30, c_128])).
% 2.41/1.30  tff(c_143, plain, (![A_87, B_88]: (v4_pre_topc(k6_waybel_0(A_87, B_88), A_87) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_87), B_88), A_87) | ~v5_pre_topc(k4_waybel_1(A_87, B_88), A_87, A_87) | ~v1_funct_2(k4_waybel_1(A_87, B_88), u1_struct_0(A_87), u1_struct_0(A_87)) | ~v1_funct_1(k4_waybel_1(A_87, B_88)) | ~l1_pre_topc(A_87) | v2_struct_0(A_87) | ~l1_orders_2(A_87) | ~v2_lattice3(A_87) | ~v5_orders_2(A_87) | ~v3_orders_2(A_87) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | v1_xboole_0(u1_struct_0(A_87)))), inference(resolution, [status(thm)], [c_14, c_138])).
% 2.41/1.30  tff(c_148, plain, (![A_89, B_90]: (v4_pre_topc(k6_waybel_0(A_89, B_90), A_89) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_89), B_90), A_89) | ~v5_pre_topc(k4_waybel_1(A_89, B_90), A_89, A_89) | ~v1_funct_1(k4_waybel_1(A_89, B_90)) | ~l1_pre_topc(A_89) | ~v2_lattice3(A_89) | ~v5_orders_2(A_89) | ~v3_orders_2(A_89) | v1_xboole_0(u1_struct_0(A_89)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_orders_2(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_20, c_143])).
% 2.41/1.30  tff(c_152, plain, (![A_91, B_92]: (v4_pre_topc(k6_waybel_0(A_91, B_92), A_91) | ~v5_pre_topc(k4_waybel_1(A_91, B_92), A_91, A_91) | ~v1_funct_1(k4_waybel_1(A_91, B_92)) | ~v2_lattice3(A_91) | ~v5_orders_2(A_91) | ~v3_orders_2(A_91) | v1_xboole_0(u1_struct_0(A_91)) | ~l1_orders_2(A_91) | ~v8_pre_topc(A_91) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_28, c_148])).
% 2.41/1.30  tff(c_155, plain, (![C_41]: (v4_pre_topc(k6_waybel_0('#skF_2', C_41), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_41)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_41, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_152])).
% 2.41/1.30  tff(c_158, plain, (![C_41]: (v4_pre_topc(k6_waybel_0('#skF_2', C_41), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_41)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_41, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_57, c_50, c_62, c_48, c_44, c_40, c_155])).
% 2.41/1.30  tff(c_159, plain, (![C_41]: (v4_pre_topc(k6_waybel_0('#skF_2', C_41), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_41)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(C_41, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_84, c_158])).
% 2.41/1.30  tff(c_160, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_159])).
% 2.41/1.30  tff(c_12, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.30  tff(c_163, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_160, c_12])).
% 2.41/1.30  tff(c_166, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_84, c_163])).
% 2.41/1.30  tff(c_169, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_166])).
% 2.41/1.30  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_169])).
% 2.41/1.30  tff(c_177, plain, (![C_96]: (v4_pre_topc(k6_waybel_0('#skF_2', C_96), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_96)) | ~m1_subset_1(C_96, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_159])).
% 2.41/1.30  tff(c_32, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.41/1.30  tff(c_180, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_177, c_32])).
% 2.41/1.30  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_83, c_180])).
% 2.41/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.30  
% 2.41/1.30  Inference rules
% 2.41/1.30  ----------------------
% 2.41/1.30  #Ref     : 0
% 2.41/1.30  #Sup     : 22
% 2.41/1.30  #Fact    : 0
% 2.41/1.30  #Define  : 0
% 2.41/1.30  #Split   : 2
% 2.41/1.30  #Chain   : 0
% 2.41/1.30  #Close   : 0
% 2.41/1.30  
% 2.41/1.30  Ordering : KBO
% 2.41/1.30  
% 2.41/1.30  Simplification rules
% 2.41/1.30  ----------------------
% 2.41/1.30  #Subsume      : 2
% 2.41/1.30  #Demod        : 13
% 2.41/1.30  #Tautology    : 3
% 2.41/1.30  #SimpNegUnit  : 2
% 2.41/1.30  #BackRed      : 0
% 2.41/1.30  
% 2.41/1.30  #Partial instantiations: 0
% 2.41/1.30  #Strategies tried      : 1
% 2.41/1.30  
% 2.41/1.30  Timing (in seconds)
% 2.41/1.30  ----------------------
% 2.41/1.30  Preprocessing        : 0.31
% 2.41/1.30  Parsing              : 0.17
% 2.41/1.30  CNF conversion       : 0.02
% 2.41/1.30  Main loop            : 0.23
% 2.41/1.30  Inferencing          : 0.10
% 2.41/1.30  Reduction            : 0.06
% 2.41/1.30  Demodulation         : 0.04
% 2.41/1.30  BG Simplification    : 0.02
% 2.41/1.30  Subsumption          : 0.03
% 2.41/1.30  Abstraction          : 0.01
% 2.41/1.30  MUC search           : 0.00
% 2.41/1.31  Cooper               : 0.00
% 2.41/1.31  Total                : 0.58
% 2.41/1.31  Index Insertion      : 0.00
% 2.41/1.31  Index Deletion       : 0.00
% 2.41/1.31  Index Matching       : 0.00
% 2.41/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
