%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:19 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 225 expanded)
%              Number of leaves         :   46 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  315 ( 930 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r3_orders_2 > r1_orders_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_187,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_9)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k6_waybel_0(A,B))
              <=> r1_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

tff(f_160,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_57,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_48,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    ! [A_61] :
      ( l1_orders_2(A_61)
      | ~ l1_waybel_9(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_72,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_52,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_80,plain,(
    ! [A_69,B_70] :
      ( v1_funct_1(k4_waybel_1(A_69,B_70))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_83,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_80])).

tff(c_86,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_83])).

tff(c_87,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_22,plain,(
    ! [A_38] :
      ( ~ v2_struct_0(A_38)
      | ~ v1_lattice3(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_90,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_22])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52,c_90])).

tff(c_95,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_58,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_54,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_50,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_103,plain,(
    ! [A_82,B_83,C_84] :
      ( r3_orders_2(A_82,B_83,B_83)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_105,plain,(
    ! [B_83] :
      ( r3_orders_2('#skF_2',B_83,B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_108,plain,(
    ! [B_83] :
      ( r3_orders_2('#skF_2',B_83,B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72,c_105])).

tff(c_110,plain,(
    ! [B_85] :
      ( r3_orders_2('#skF_2',B_85,B_85)
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_108])).

tff(c_113,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_110])).

tff(c_133,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_orders_2(A_102,B_103,C_104)
      | ~ r3_orders_2(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_135,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_113,c_133])).

tff(c_138,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72,c_46,c_135])).

tff(c_139,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_138])).

tff(c_24,plain,(
    ! [C_45,A_39,B_43] :
      ( r2_hidden(C_45,k6_waybel_0(A_39,B_43))
      | ~ r1_orders_2(A_39,B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k4_waybel_1(A_46,B_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46),u1_struct_0(A_46))))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_147,plain,(
    ! [A_106,B_107] :
      ( k8_relset_1(u1_struct_0(A_106),u1_struct_0(A_106),k4_waybel_1(A_106,B_107),k6_domain_1(u1_struct_0(A_106),B_107)) = k6_waybel_0(A_106,B_107)
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v2_lattice3(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v3_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( m1_subset_1(k8_relset_1(A_4,B_5,C_6,D_7),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k6_waybel_0(A_111,B_112),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(k4_waybel_1(A_111,B_112),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(A_111))))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v2_lattice3(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v3_orders_2(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_4])).

tff(c_178,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1(k6_waybel_0(A_113,B_114),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v2_lattice3(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_28,c_173])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_182,plain,(
    ! [A_115,A_116,B_117] :
      ( ~ v1_xboole_0(u1_struct_0(A_115))
      | ~ r2_hidden(A_116,k6_waybel_0(A_115,B_117))
      | ~ v2_lattice3(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | ~ m1_subset_1(B_117,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_178,c_2])).

tff(c_187,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ v1_xboole_0(u1_struct_0(A_118))
      | ~ v2_lattice3(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | ~ r1_orders_2(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_189,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_139,c_187])).

tff(c_192,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46,c_58,c_54,c_50,c_189])).

tff(c_193,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_192])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_63,plain,(
    ! [A_60] :
      ( l1_pre_topc(A_60)
      | ~ l1_waybel_9(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_67,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_60,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_44,plain,(
    ! [C_59] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_59),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_59,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_38,plain,(
    ! [A_49,B_51] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_49),B_51),A_49)
      | ~ v8_pre_topc(A_49)
      | ~ m1_subset_1(B_51,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    ! [A_46,B_47] :
      ( v1_funct_2(k4_waybel_1(A_46,B_47),u1_struct_0(A_46),u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k6_domain_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ! [A_52,B_54] :
      ( k8_relset_1(u1_struct_0(A_52),u1_struct_0(A_52),k4_waybel_1(A_52,B_54),k6_domain_1(u1_struct_0(A_52),B_54)) = k6_waybel_0(A_52,B_54)
      | ~ m1_subset_1(B_54,u1_struct_0(A_52))
      | ~ l1_orders_2(A_52)
      | ~ v2_lattice3(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v3_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_215,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_132),u1_struct_0(B_133),C_134,D_135),A_132)
      | ~ v4_pre_topc(D_135,B_133)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0(B_133)))
      | ~ v5_pre_topc(C_134,A_132,B_133)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_132),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_233,plain,(
    ! [A_143,B_144,D_145] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_143),u1_struct_0(A_143),k4_waybel_1(A_143,B_144),D_145),A_143)
      | ~ v4_pre_topc(D_145,A_143)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ v5_pre_topc(k4_waybel_1(A_143,B_144),A_143,A_143)
      | ~ v1_funct_2(k4_waybel_1(A_143,B_144),u1_struct_0(A_143),u1_struct_0(A_143))
      | ~ v1_funct_1(k4_waybel_1(A_143,B_144))
      | ~ l1_pre_topc(A_143)
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_247,plain,(
    ! [A_152,B_153] :
      ( v4_pre_topc(k6_waybel_0(A_152,B_153),A_152)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_152),B_153),A_152)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_152),B_153),k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ v5_pre_topc(k4_waybel_1(A_152,B_153),A_152,A_152)
      | ~ v1_funct_2(k4_waybel_1(A_152,B_153),u1_struct_0(A_152),u1_struct_0(A_152))
      | ~ v1_funct_1(k4_waybel_1(A_152,B_153))
      | ~ l1_pre_topc(A_152)
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | v2_struct_0(A_152)
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v2_lattice3(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v3_orders_2(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_233])).

tff(c_252,plain,(
    ! [A_154,B_155] :
      ( v4_pre_topc(k6_waybel_0(A_154,B_155),A_154)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_154),B_155),A_154)
      | ~ v5_pre_topc(k4_waybel_1(A_154,B_155),A_154,A_154)
      | ~ v1_funct_2(k4_waybel_1(A_154,B_155),u1_struct_0(A_154),u1_struct_0(A_154))
      | ~ v1_funct_1(k4_waybel_1(A_154,B_155))
      | ~ l1_pre_topc(A_154)
      | v2_struct_0(A_154)
      | ~ l1_orders_2(A_154)
      | ~ v2_lattice3(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | v1_xboole_0(u1_struct_0(A_154)) ) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_257,plain,(
    ! [A_156,B_157] :
      ( v4_pre_topc(k6_waybel_0(A_156,B_157),A_156)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_156),B_157),A_156)
      | ~ v5_pre_topc(k4_waybel_1(A_156,B_157),A_156,A_156)
      | ~ v1_funct_1(k4_waybel_1(A_156,B_157))
      | ~ l1_pre_topc(A_156)
      | ~ v2_lattice3(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_30,c_252])).

tff(c_261,plain,(
    ! [A_158,B_159] :
      ( v4_pre_topc(k6_waybel_0(A_158,B_159),A_158)
      | ~ v5_pre_topc(k4_waybel_1(A_158,B_159),A_158,A_158)
      | ~ v1_funct_1(k4_waybel_1(A_158,B_159))
      | ~ v2_lattice3(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v1_xboole_0(u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v8_pre_topc(A_158)
      | ~ m1_subset_1(B_159,u1_struct_0(A_158))
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_264,plain,(
    ! [C_59] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_59),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_59))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_59,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_261])).

tff(c_267,plain,(
    ! [C_59] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_59),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_59))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_59,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_67,c_60,c_72,c_58,c_54,c_50,c_264])).

tff(c_269,plain,(
    ! [C_160] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_160),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_160))
      | ~ m1_subset_1(C_160,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_193,c_267])).

tff(c_42,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_272,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_269,c_42])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.38  
% 2.90/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.38  %$ v5_pre_topc > v1_funct_2 > r3_orders_2 > r1_orders_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.90/1.38  
% 2.90/1.38  %Foreground sorts:
% 2.90/1.38  
% 2.90/1.38  
% 2.90/1.38  %Background operators:
% 2.90/1.38  
% 2.90/1.38  
% 2.90/1.38  %Foreground operators:
% 2.90/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.38  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.90/1.38  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.90/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.90/1.38  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.90/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.90/1.38  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.90/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.90/1.38  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.90/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.38  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.90/1.38  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.90/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.90/1.38  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.90/1.38  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.90/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.38  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.90/1.38  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.90/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.38  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.90/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.38  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.90/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.38  
% 2.90/1.40  tff(f_187, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.90/1.40  tff(f_133, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.90/1.40  tff(f_127, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.90/1.40  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.90/1.40  tff(f_92, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.90/1.40  tff(f_79, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.90/1.40  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k6_waybel_0(A, B)) <=> r1_orders_2(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_waybel_0)).
% 2.90/1.40  tff(f_160, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.90/1.40  tff(f_36, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.90/1.40  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.90/1.40  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.90/1.40  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.90/1.40  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.90/1.40  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_48, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_68, plain, (![A_61]: (l1_orders_2(A_61) | ~l1_waybel_9(A_61))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_72, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_48, c_68])).
% 2.90/1.40  tff(c_52, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_80, plain, (![A_69, B_70]: (v1_funct_1(k4_waybel_1(A_69, B_70)) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.90/1.40  tff(c_83, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_80])).
% 2.90/1.40  tff(c_86, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_83])).
% 2.90/1.40  tff(c_87, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_86])).
% 2.90/1.40  tff(c_22, plain, (![A_38]: (~v2_struct_0(A_38) | ~v1_lattice3(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.90/1.40  tff(c_90, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_87, c_22])).
% 2.90/1.40  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_52, c_90])).
% 2.90/1.40  tff(c_95, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_86])).
% 2.90/1.40  tff(c_96, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 2.90/1.40  tff(c_58, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_54, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_50, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_103, plain, (![A_82, B_83, C_84]: (r3_orders_2(A_82, B_83, B_83) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.90/1.40  tff(c_105, plain, (![B_83]: (r3_orders_2('#skF_2', B_83, B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_103])).
% 2.90/1.40  tff(c_108, plain, (![B_83]: (r3_orders_2('#skF_2', B_83, B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72, c_105])).
% 2.90/1.40  tff(c_110, plain, (![B_85]: (r3_orders_2('#skF_2', B_85, B_85) | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_96, c_108])).
% 2.90/1.40  tff(c_113, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_110])).
% 2.90/1.40  tff(c_133, plain, (![A_102, B_103, C_104]: (r1_orders_2(A_102, B_103, C_104) | ~r3_orders_2(A_102, B_103, C_104) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.90/1.40  tff(c_135, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_113, c_133])).
% 2.90/1.40  tff(c_138, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72, c_46, c_135])).
% 2.90/1.40  tff(c_139, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_96, c_138])).
% 2.90/1.40  tff(c_24, plain, (![C_45, A_39, B_43]: (r2_hidden(C_45, k6_waybel_0(A_39, B_43)) | ~r1_orders_2(A_39, B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.90/1.40  tff(c_28, plain, (![A_46, B_47]: (m1_subset_1(k4_waybel_1(A_46, B_47), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46), u1_struct_0(A_46)))) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.90/1.40  tff(c_147, plain, (![A_106, B_107]: (k8_relset_1(u1_struct_0(A_106), u1_struct_0(A_106), k4_waybel_1(A_106, B_107), k6_domain_1(u1_struct_0(A_106), B_107))=k6_waybel_0(A_106, B_107) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v2_lattice3(A_106) | ~v5_orders_2(A_106) | ~v3_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.90/1.40  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (m1_subset_1(k8_relset_1(A_4, B_5, C_6, D_7), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.40  tff(c_173, plain, (![A_111, B_112]: (m1_subset_1(k6_waybel_0(A_111, B_112), k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(k4_waybel_1(A_111, B_112), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(A_111)))) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v2_lattice3(A_111) | ~v5_orders_2(A_111) | ~v3_orders_2(A_111))), inference(superposition, [status(thm), theory('equality')], [c_147, c_4])).
% 2.90/1.40  tff(c_178, plain, (![A_113, B_114]: (m1_subset_1(k6_waybel_0(A_113, B_114), k1_zfmisc_1(u1_struct_0(A_113))) | ~v2_lattice3(A_113) | ~v5_orders_2(A_113) | ~v3_orders_2(A_113) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_28, c_173])).
% 2.90/1.40  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.40  tff(c_182, plain, (![A_115, A_116, B_117]: (~v1_xboole_0(u1_struct_0(A_115)) | ~r2_hidden(A_116, k6_waybel_0(A_115, B_117)) | ~v2_lattice3(A_115) | ~v5_orders_2(A_115) | ~v3_orders_2(A_115) | ~m1_subset_1(B_117, u1_struct_0(A_115)) | ~l1_orders_2(A_115) | v2_struct_0(A_115))), inference(resolution, [status(thm)], [c_178, c_2])).
% 2.90/1.40  tff(c_187, plain, (![A_118, B_119, C_120]: (~v1_xboole_0(u1_struct_0(A_118)) | ~v2_lattice3(A_118) | ~v5_orders_2(A_118) | ~v3_orders_2(A_118) | ~r1_orders_2(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_24, c_182])).
% 2.90/1.40  tff(c_189, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_139, c_187])).
% 2.90/1.40  tff(c_192, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46, c_58, c_54, c_50, c_189])).
% 2.90/1.40  tff(c_193, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_96, c_192])).
% 2.90/1.40  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_63, plain, (![A_60]: (l1_pre_topc(A_60) | ~l1_waybel_9(A_60))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_67, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_63])).
% 2.90/1.40  tff(c_60, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_44, plain, (![C_59]: (v5_pre_topc(k4_waybel_1('#skF_2', C_59), '#skF_2', '#skF_2') | ~m1_subset_1(C_59, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_38, plain, (![A_49, B_51]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_49), B_51), A_49) | ~v8_pre_topc(A_49) | ~m1_subset_1(B_51, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.90/1.40  tff(c_30, plain, (![A_46, B_47]: (v1_funct_2(k4_waybel_1(A_46, B_47), u1_struct_0(A_46), u1_struct_0(A_46)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.90/1.40  tff(c_14, plain, (![A_30, B_31]: (m1_subset_1(k6_domain_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.90/1.40  tff(c_40, plain, (![A_52, B_54]: (k8_relset_1(u1_struct_0(A_52), u1_struct_0(A_52), k4_waybel_1(A_52, B_54), k6_domain_1(u1_struct_0(A_52), B_54))=k6_waybel_0(A_52, B_54) | ~m1_subset_1(B_54, u1_struct_0(A_52)) | ~l1_orders_2(A_52) | ~v2_lattice3(A_52) | ~v5_orders_2(A_52) | ~v3_orders_2(A_52))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.90/1.40  tff(c_215, plain, (![A_132, B_133, C_134, D_135]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_132), u1_struct_0(B_133), C_134, D_135), A_132) | ~v4_pre_topc(D_135, B_133) | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0(B_133))) | ~v5_pre_topc(C_134, A_132, B_133) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0(A_132), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.40  tff(c_233, plain, (![A_143, B_144, D_145]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_143), u1_struct_0(A_143), k4_waybel_1(A_143, B_144), D_145), A_143) | ~v4_pre_topc(D_145, A_143) | ~m1_subset_1(D_145, k1_zfmisc_1(u1_struct_0(A_143))) | ~v5_pre_topc(k4_waybel_1(A_143, B_144), A_143, A_143) | ~v1_funct_2(k4_waybel_1(A_143, B_144), u1_struct_0(A_143), u1_struct_0(A_143)) | ~v1_funct_1(k4_waybel_1(A_143, B_144)) | ~l1_pre_topc(A_143) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_28, c_215])).
% 2.90/1.40  tff(c_247, plain, (![A_152, B_153]: (v4_pre_topc(k6_waybel_0(A_152, B_153), A_152) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_152), B_153), A_152) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_152), B_153), k1_zfmisc_1(u1_struct_0(A_152))) | ~v5_pre_topc(k4_waybel_1(A_152, B_153), A_152, A_152) | ~v1_funct_2(k4_waybel_1(A_152, B_153), u1_struct_0(A_152), u1_struct_0(A_152)) | ~v1_funct_1(k4_waybel_1(A_152, B_153)) | ~l1_pre_topc(A_152) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | v2_struct_0(A_152) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v2_lattice3(A_152) | ~v5_orders_2(A_152) | ~v3_orders_2(A_152))), inference(superposition, [status(thm), theory('equality')], [c_40, c_233])).
% 2.90/1.40  tff(c_252, plain, (![A_154, B_155]: (v4_pre_topc(k6_waybel_0(A_154, B_155), A_154) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_154), B_155), A_154) | ~v5_pre_topc(k4_waybel_1(A_154, B_155), A_154, A_154) | ~v1_funct_2(k4_waybel_1(A_154, B_155), u1_struct_0(A_154), u1_struct_0(A_154)) | ~v1_funct_1(k4_waybel_1(A_154, B_155)) | ~l1_pre_topc(A_154) | v2_struct_0(A_154) | ~l1_orders_2(A_154) | ~v2_lattice3(A_154) | ~v5_orders_2(A_154) | ~v3_orders_2(A_154) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | v1_xboole_0(u1_struct_0(A_154)))), inference(resolution, [status(thm)], [c_14, c_247])).
% 2.90/1.40  tff(c_257, plain, (![A_156, B_157]: (v4_pre_topc(k6_waybel_0(A_156, B_157), A_156) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_156), B_157), A_156) | ~v5_pre_topc(k4_waybel_1(A_156, B_157), A_156, A_156) | ~v1_funct_1(k4_waybel_1(A_156, B_157)) | ~l1_pre_topc(A_156) | ~v2_lattice3(A_156) | ~v5_orders_2(A_156) | ~v3_orders_2(A_156) | v1_xboole_0(u1_struct_0(A_156)) | ~m1_subset_1(B_157, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_30, c_252])).
% 2.90/1.40  tff(c_261, plain, (![A_158, B_159]: (v4_pre_topc(k6_waybel_0(A_158, B_159), A_158) | ~v5_pre_topc(k4_waybel_1(A_158, B_159), A_158, A_158) | ~v1_funct_1(k4_waybel_1(A_158, B_159)) | ~v2_lattice3(A_158) | ~v5_orders_2(A_158) | ~v3_orders_2(A_158) | v1_xboole_0(u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v8_pre_topc(A_158) | ~m1_subset_1(B_159, u1_struct_0(A_158)) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_38, c_257])).
% 2.90/1.40  tff(c_264, plain, (![C_59]: (v4_pre_topc(k6_waybel_0('#skF_2', C_59), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_59)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_59, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_261])).
% 2.90/1.40  tff(c_267, plain, (![C_59]: (v4_pre_topc(k6_waybel_0('#skF_2', C_59), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_59)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_59, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_67, c_60, c_72, c_58, c_54, c_50, c_264])).
% 2.90/1.40  tff(c_269, plain, (![C_160]: (v4_pre_topc(k6_waybel_0('#skF_2', C_160), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_160)) | ~m1_subset_1(C_160, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_96, c_193, c_267])).
% 2.90/1.40  tff(c_42, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.90/1.40  tff(c_272, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_269, c_42])).
% 2.90/1.40  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_95, c_272])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 0
% 2.90/1.40  #Sup     : 41
% 2.90/1.40  #Fact    : 0
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 1
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 3
% 2.90/1.40  #Demod        : 26
% 2.90/1.40  #Tautology    : 6
% 2.90/1.40  #SimpNegUnit  : 5
% 2.90/1.40  #BackRed      : 0
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.41  Preprocessing        : 0.34
% 2.90/1.41  Parsing              : 0.19
% 2.90/1.41  CNF conversion       : 0.03
% 2.90/1.41  Main loop            : 0.30
% 2.90/1.41  Inferencing          : 0.13
% 2.90/1.41  Reduction            : 0.08
% 2.90/1.41  Demodulation         : 0.05
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.05
% 2.90/1.41  Abstraction          : 0.01
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.68
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
