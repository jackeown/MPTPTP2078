%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:19 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 183 expanded)
%              Number of leaves         :   44 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 716 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r1_orders_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_176,negated_conjecture,(
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

tff(f_122,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k6_waybel_0(A,B))
              <=> r1_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_9)).

tff(f_53,axiom,(
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

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_59,plain,(
    ! [A_55] :
      ( l1_orders_2(A_55)
      | ~ l1_waybel_9(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_63,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_48,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_76,plain,(
    ! [A_64,B_65] :
      ( v1_funct_1(k4_waybel_1(A_64,B_65))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_79,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_82,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_79])).

tff(c_83,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_16,plain,(
    ! [A_31] :
      ( ~ v2_struct_0(A_31)
      | ~ v1_lattice3(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_83,c_16])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_86])).

tff(c_91,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_93,plain,(
    ! [A_66,B_67] :
      ( r1_orders_2(A_66,B_67,B_67)
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | ~ l1_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_98,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_63,c_95])).

tff(c_99,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_98])).

tff(c_113,plain,(
    ! [C_85,A_86,B_87] :
      ( r2_hidden(C_85,k6_waybel_0(A_86,B_87))
      | ~ r1_orders_2(A_86,B_87,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_100,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k6_waybel_0(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l1_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_68,A_1,B_69] :
      ( ~ v1_xboole_0(u1_struct_0(A_68))
      | ~ r2_hidden(A_1,k6_waybel_0(A_68,B_69))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l1_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_122,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ v1_xboole_0(u1_struct_0(A_88))
      | ~ r1_orders_2(A_88,B_89,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_113,c_103])).

tff(c_124,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_122])).

tff(c_127,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_124])).

tff(c_128,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_127])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_64,plain,(
    ! [A_56] :
      ( l1_pre_topc(A_56)
      | ~ l1_waybel_9(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_56,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_40,plain,(
    ! [C_54] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_54),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_34,plain,(
    ! [A_44,B_46] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_44),B_46),A_44)
      | ~ v8_pre_topc(A_44)
      | ~ m1_subset_1(B_46,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_26,plain,(
    ! [A_41,B_42] :
      ( v1_funct_2(k4_waybel_1(A_41,B_42),u1_struct_0(A_41),u1_struct_0(A_41))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k6_domain_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_47,B_49] :
      ( k8_relset_1(u1_struct_0(A_47),u1_struct_0(A_47),k4_waybel_1(A_47,B_49),k6_domain_1(u1_struct_0(A_47),B_49)) = k6_waybel_0(A_47,B_49)
      | ~ m1_subset_1(B_49,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v2_lattice3(A_47)
      | ~ v5_orders_2(A_47)
      | ~ v3_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_24,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k4_waybel_1(A_41,B_42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_41),u1_struct_0(A_41))))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_155,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_102),u1_struct_0(B_103),C_104,D_105),A_102)
      | ~ v4_pre_topc(D_105,B_103)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(u1_struct_0(B_103)))
      | ~ v5_pre_topc(C_104,A_102,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc(B_103)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_173,plain,(
    ! [A_115,B_116,D_117] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_115),u1_struct_0(A_115),k4_waybel_1(A_115,B_116),D_117),A_115)
      | ~ v4_pre_topc(D_117,A_115)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v5_pre_topc(k4_waybel_1(A_115,B_116),A_115,A_115)
      | ~ v1_funct_2(k4_waybel_1(A_115,B_116),u1_struct_0(A_115),u1_struct_0(A_115))
      | ~ v1_funct_1(k4_waybel_1(A_115,B_116))
      | ~ l1_pre_topc(A_115)
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_24,c_155])).

tff(c_183,plain,(
    ! [A_121,B_122] :
      ( v4_pre_topc(k6_waybel_0(A_121,B_122),A_121)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_121),B_122),A_121)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_121),B_122),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v5_pre_topc(k4_waybel_1(A_121,B_122),A_121,A_121)
      | ~ v1_funct_2(k4_waybel_1(A_121,B_122),u1_struct_0(A_121),u1_struct_0(A_121))
      | ~ v1_funct_1(k4_waybel_1(A_121,B_122))
      | ~ l1_pre_topc(A_121)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | v2_struct_0(A_121)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v2_lattice3(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v3_orders_2(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_173])).

tff(c_188,plain,(
    ! [A_123,B_124] :
      ( v4_pre_topc(k6_waybel_0(A_123,B_124),A_123)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_123),B_124),A_123)
      | ~ v5_pre_topc(k4_waybel_1(A_123,B_124),A_123,A_123)
      | ~ v1_funct_2(k4_waybel_1(A_123,B_124),u1_struct_0(A_123),u1_struct_0(A_123))
      | ~ v1_funct_1(k4_waybel_1(A_123,B_124))
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | v1_xboole_0(u1_struct_0(A_123)) ) ),
    inference(resolution,[status(thm)],[c_12,c_183])).

tff(c_193,plain,(
    ! [A_125,B_126] :
      ( v4_pre_topc(k6_waybel_0(A_125,B_126),A_125)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_125),B_126),A_125)
      | ~ v5_pre_topc(k4_waybel_1(A_125,B_126),A_125,A_125)
      | ~ v1_funct_1(k4_waybel_1(A_125,B_126))
      | ~ l1_pre_topc(A_125)
      | ~ v2_lattice3(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v1_xboole_0(u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_197,plain,(
    ! [A_127,B_128] :
      ( v4_pre_topc(k6_waybel_0(A_127,B_128),A_127)
      | ~ v5_pre_topc(k4_waybel_1(A_127,B_128),A_127,A_127)
      | ~ v1_funct_1(k4_waybel_1(A_127,B_128))
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v1_xboole_0(u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v8_pre_topc(A_127)
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_34,c_193])).

tff(c_200,plain,(
    ! [C_54] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_54),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_54))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_197])).

tff(c_203,plain,(
    ! [C_54] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_54),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_54))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68,c_56,c_63,c_54,c_50,c_46,c_200])).

tff(c_205,plain,(
    ! [C_129] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_129),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_129))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_128,c_203])).

tff(c_38,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_208,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_205,c_38])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_91,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.34  %$ v5_pre_topc > v1_funct_2 > r1_orders_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.62/1.34  
% 2.62/1.34  %Foreground sorts:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Background operators:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Foreground operators:
% 2.62/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.62/1.34  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.62/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.62/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.62/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.62/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.62/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.62/1.34  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.62/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.62/1.34  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.62/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.62/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.62/1.34  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.34  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.62/1.34  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.62/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.62/1.34  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.62/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.34  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.62/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.34  
% 2.62/1.36  tff(f_176, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.62/1.36  tff(f_122, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.62/1.36  tff(f_116, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.62/1.36  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.62/1.36  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.62/1.36  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k6_waybel_0(A, B)) <=> r1_orders_2(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_waybel_0)).
% 2.62/1.36  tff(f_88, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k6_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 2.62/1.36  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.62/1.36  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.62/1.36  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.62/1.36  tff(f_149, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.62/1.36  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.62/1.36  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_44, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_59, plain, (![A_55]: (l1_orders_2(A_55) | ~l1_waybel_9(A_55))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.36  tff(c_63, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_44, c_59])).
% 2.62/1.36  tff(c_48, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_76, plain, (![A_64, B_65]: (v1_funct_1(k4_waybel_1(A_64, B_65)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.36  tff(c_79, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_76])).
% 2.62/1.36  tff(c_82, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_79])).
% 2.62/1.36  tff(c_83, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_82])).
% 2.62/1.36  tff(c_16, plain, (![A_31]: (~v2_struct_0(A_31) | ~v1_lattice3(A_31) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.62/1.36  tff(c_86, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_83, c_16])).
% 2.62/1.36  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_86])).
% 2.62/1.36  tff(c_91, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_82])).
% 2.62/1.36  tff(c_92, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_82])).
% 2.62/1.36  tff(c_54, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_93, plain, (![A_66, B_67]: (r1_orders_2(A_66, B_67, B_67) | ~m1_subset_1(B_67, u1_struct_0(A_66)) | ~l1_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.62/1.36  tff(c_95, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_93])).
% 2.62/1.36  tff(c_98, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_63, c_95])).
% 2.62/1.36  tff(c_99, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_92, c_98])).
% 2.62/1.36  tff(c_113, plain, (![C_85, A_86, B_87]: (r2_hidden(C_85, k6_waybel_0(A_86, B_87)) | ~r1_orders_2(A_86, B_87, C_85) | ~m1_subset_1(C_85, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.62/1.36  tff(c_100, plain, (![A_68, B_69]: (m1_subset_1(k6_waybel_0(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l1_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.62/1.36  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.36  tff(c_103, plain, (![A_68, A_1, B_69]: (~v1_xboole_0(u1_struct_0(A_68)) | ~r2_hidden(A_1, k6_waybel_0(A_68, B_69)) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l1_orders_2(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.62/1.36  tff(c_122, plain, (![A_88, B_89, C_90]: (~v1_xboole_0(u1_struct_0(A_88)) | ~r1_orders_2(A_88, B_89, C_90) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_113, c_103])).
% 2.62/1.36  tff(c_124, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_99, c_122])).
% 2.62/1.36  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_124])).
% 2.62/1.36  tff(c_128, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_92, c_127])).
% 2.62/1.36  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_64, plain, (![A_56]: (l1_pre_topc(A_56) | ~l1_waybel_9(A_56))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.62/1.36  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_64])).
% 2.62/1.36  tff(c_56, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_50, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_46, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_40, plain, (![C_54]: (v5_pre_topc(k4_waybel_1('#skF_2', C_54), '#skF_2', '#skF_2') | ~m1_subset_1(C_54, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_34, plain, (![A_44, B_46]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_44), B_46), A_44) | ~v8_pre_topc(A_44) | ~m1_subset_1(B_46, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.62/1.36  tff(c_26, plain, (![A_41, B_42]: (v1_funct_2(k4_waybel_1(A_41, B_42), u1_struct_0(A_41), u1_struct_0(A_41)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.36  tff(c_12, plain, (![A_26, B_27]: (m1_subset_1(k6_domain_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.36  tff(c_36, plain, (![A_47, B_49]: (k8_relset_1(u1_struct_0(A_47), u1_struct_0(A_47), k4_waybel_1(A_47, B_49), k6_domain_1(u1_struct_0(A_47), B_49))=k6_waybel_0(A_47, B_49) | ~m1_subset_1(B_49, u1_struct_0(A_47)) | ~l1_orders_2(A_47) | ~v2_lattice3(A_47) | ~v5_orders_2(A_47) | ~v3_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.62/1.36  tff(c_24, plain, (![A_41, B_42]: (m1_subset_1(k4_waybel_1(A_41, B_42), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_41), u1_struct_0(A_41)))) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.62/1.36  tff(c_155, plain, (![A_102, B_103, C_104, D_105]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_102), u1_struct_0(B_103), C_104, D_105), A_102) | ~v4_pre_topc(D_105, B_103) | ~m1_subset_1(D_105, k1_zfmisc_1(u1_struct_0(B_103))) | ~v5_pre_topc(C_104, A_102, B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), u1_struct_0(B_103)))) | ~v1_funct_2(C_104, u1_struct_0(A_102), u1_struct_0(B_103)) | ~v1_funct_1(C_104) | ~l1_pre_topc(B_103) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.36  tff(c_173, plain, (![A_115, B_116, D_117]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_115), u1_struct_0(A_115), k4_waybel_1(A_115, B_116), D_117), A_115) | ~v4_pre_topc(D_117, A_115) | ~m1_subset_1(D_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~v5_pre_topc(k4_waybel_1(A_115, B_116), A_115, A_115) | ~v1_funct_2(k4_waybel_1(A_115, B_116), u1_struct_0(A_115), u1_struct_0(A_115)) | ~v1_funct_1(k4_waybel_1(A_115, B_116)) | ~l1_pre_topc(A_115) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~l1_orders_2(A_115) | v2_struct_0(A_115))), inference(resolution, [status(thm)], [c_24, c_155])).
% 2.62/1.36  tff(c_183, plain, (![A_121, B_122]: (v4_pre_topc(k6_waybel_0(A_121, B_122), A_121) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_121), B_122), A_121) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_121), B_122), k1_zfmisc_1(u1_struct_0(A_121))) | ~v5_pre_topc(k4_waybel_1(A_121, B_122), A_121, A_121) | ~v1_funct_2(k4_waybel_1(A_121, B_122), u1_struct_0(A_121), u1_struct_0(A_121)) | ~v1_funct_1(k4_waybel_1(A_121, B_122)) | ~l1_pre_topc(A_121) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | v2_struct_0(A_121) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v2_lattice3(A_121) | ~v5_orders_2(A_121) | ~v3_orders_2(A_121))), inference(superposition, [status(thm), theory('equality')], [c_36, c_173])).
% 2.62/1.36  tff(c_188, plain, (![A_123, B_124]: (v4_pre_topc(k6_waybel_0(A_123, B_124), A_123) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_123), B_124), A_123) | ~v5_pre_topc(k4_waybel_1(A_123, B_124), A_123, A_123) | ~v1_funct_2(k4_waybel_1(A_123, B_124), u1_struct_0(A_123), u1_struct_0(A_123)) | ~v1_funct_1(k4_waybel_1(A_123, B_124)) | ~l1_pre_topc(A_123) | v2_struct_0(A_123) | ~l1_orders_2(A_123) | ~v2_lattice3(A_123) | ~v5_orders_2(A_123) | ~v3_orders_2(A_123) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | v1_xboole_0(u1_struct_0(A_123)))), inference(resolution, [status(thm)], [c_12, c_183])).
% 2.62/1.36  tff(c_193, plain, (![A_125, B_126]: (v4_pre_topc(k6_waybel_0(A_125, B_126), A_125) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_125), B_126), A_125) | ~v5_pre_topc(k4_waybel_1(A_125, B_126), A_125, A_125) | ~v1_funct_1(k4_waybel_1(A_125, B_126)) | ~l1_pre_topc(A_125) | ~v2_lattice3(A_125) | ~v5_orders_2(A_125) | ~v3_orders_2(A_125) | v1_xboole_0(u1_struct_0(A_125)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_26, c_188])).
% 2.62/1.36  tff(c_197, plain, (![A_127, B_128]: (v4_pre_topc(k6_waybel_0(A_127, B_128), A_127) | ~v5_pre_topc(k4_waybel_1(A_127, B_128), A_127, A_127) | ~v1_funct_1(k4_waybel_1(A_127, B_128)) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127) | ~v3_orders_2(A_127) | v1_xboole_0(u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v8_pre_topc(A_127) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_34, c_193])).
% 2.62/1.36  tff(c_200, plain, (![C_54]: (v4_pre_topc(k6_waybel_0('#skF_2', C_54), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_54)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_54, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_197])).
% 2.62/1.36  tff(c_203, plain, (![C_54]: (v4_pre_topc(k6_waybel_0('#skF_2', C_54), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_54)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_54, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68, c_56, c_63, c_54, c_50, c_46, c_200])).
% 2.62/1.36  tff(c_205, plain, (![C_129]: (v4_pre_topc(k6_waybel_0('#skF_2', C_129), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_129)) | ~m1_subset_1(C_129, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_92, c_128, c_203])).
% 2.62/1.36  tff(c_38, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.62/1.36  tff(c_208, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_205, c_38])).
% 2.62/1.36  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_91, c_208])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 0
% 2.62/1.36  #Sup     : 28
% 2.62/1.36  #Fact    : 0
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 1
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.62/1.36  
% 2.62/1.36  Ordering : KBO
% 2.62/1.36  
% 2.62/1.36  Simplification rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Subsume      : 2
% 2.62/1.36  #Demod        : 16
% 2.62/1.36  #Tautology    : 5
% 2.62/1.36  #SimpNegUnit  : 3
% 2.62/1.36  #BackRed      : 0
% 2.62/1.36  
% 2.62/1.36  #Partial instantiations: 0
% 2.62/1.36  #Strategies tried      : 1
% 2.62/1.36  
% 2.62/1.36  Timing (in seconds)
% 2.62/1.36  ----------------------
% 2.62/1.36  Preprocessing        : 0.33
% 2.62/1.36  Parsing              : 0.19
% 2.62/1.36  CNF conversion       : 0.03
% 2.62/1.36  Main loop            : 0.26
% 2.62/1.36  Inferencing          : 0.11
% 2.62/1.36  Reduction            : 0.07
% 2.62/1.36  Demodulation         : 0.05
% 2.62/1.36  BG Simplification    : 0.02
% 2.62/1.36  Subsumption          : 0.04
% 2.62/1.36  Abstraction          : 0.01
% 2.62/1.36  MUC search           : 0.00
% 2.62/1.36  Cooper               : 0.00
% 2.62/1.36  Total                : 0.63
% 2.62/1.36  Index Insertion      : 0.00
% 2.62/1.36  Index Deletion       : 0.00
% 2.62/1.36  Index Matching       : 0.00
% 2.62/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
