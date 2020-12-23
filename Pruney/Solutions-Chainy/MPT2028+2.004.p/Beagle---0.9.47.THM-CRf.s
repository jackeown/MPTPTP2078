%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:18 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 225 expanded)
%              Number of leaves         :   44 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  265 ( 876 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_166,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).

tff(f_70,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(c_44,plain,(
    l1_waybel_9('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_59,plain,(
    ! [A_52] :
      ( l1_orders_2(A_52)
      | ~ l1_waybel_9(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_63,plain,(
    l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_48,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_82,plain,(
    ! [A_64,B_65] :
      ( v1_funct_1(k4_waybel_1(A_64,B_65))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_85,plain,
    ( v1_funct_1(k4_waybel_1('#skF_3','#skF_4'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_88,plain,
    ( v1_funct_1(k4_waybel_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_85])).

tff(c_89,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_20,plain,(
    ! [A_35] :
      ( ~ v2_struct_0(A_35)
      | ~ v1_lattice3(A_35)
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_20])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_92])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    ! [A_53] :
      ( l1_pre_topc(A_53)
      | ~ l1_waybel_9(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_97,plain,(
    v1_funct_1(k4_waybel_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k6_waybel_0(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l1_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    ! [A_72,A_73,B_74] :
      ( ~ v1_xboole_0(u1_struct_0(A_72))
      | ~ r2_hidden(A_73,k6_waybel_0(A_72,B_74))
      | ~ m1_subset_1(B_74,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_105,c_6])).

tff(c_124,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77)
      | v2_struct_0(A_77)
      | v1_xboole_0(k6_waybel_0(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_127,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(k6_waybel_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_130,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v1_xboole_0(k6_waybel_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_127])).

tff(c_131,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_xboole_0(k6_waybel_0('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_130])).

tff(c_132,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_56,plain,(
    v8_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_40,plain,(
    ! [C_51] :
      ( v5_pre_topc(k4_waybel_1('#skF_3',C_51),'#skF_3','#skF_3')
      | ~ m1_subset_1(C_51,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    ! [A_41,B_43] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_41),B_43),A_41)
      | ~ v8_pre_topc(A_41)
      | ~ m1_subset_1(B_43,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( v1_funct_2(k4_waybel_1(A_38,B_39),u1_struct_0(A_38),u1_struct_0(A_38))
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k6_domain_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ! [A_44,B_46] :
      ( k8_relset_1(u1_struct_0(A_44),u1_struct_0(A_44),k4_waybel_1(A_44,B_46),k6_domain_1(u1_struct_0(A_44),B_46)) = k6_waybel_0(A_44,B_46)
      | ~ m1_subset_1(B_46,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v2_lattice3(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v3_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k4_waybel_1(A_38,B_39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(A_38))))
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_183,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_105),u1_struct_0(B_106),C_107,D_108),A_105)
      | ~ v4_pre_topc(D_108,B_106)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(u1_struct_0(B_106)))
      | ~ v5_pre_topc(C_107,A_105,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_107,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_106)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_202,plain,(
    ! [A_116,B_117,D_118] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_116),u1_struct_0(A_116),k4_waybel_1(A_116,B_117),D_118),A_116)
      | ~ v4_pre_topc(D_118,A_116)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ v5_pre_topc(k4_waybel_1(A_116,B_117),A_116,A_116)
      | ~ v1_funct_2(k4_waybel_1(A_116,B_117),u1_struct_0(A_116),u1_struct_0(A_116))
      | ~ v1_funct_1(k4_waybel_1(A_116,B_117))
      | ~ l1_pre_topc(A_116)
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_24,c_183])).

tff(c_212,plain,(
    ! [A_122,B_123] :
      ( v4_pre_topc(k6_waybel_0(A_122,B_123),A_122)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_122),B_123),A_122)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_122),B_123),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ v5_pre_topc(k4_waybel_1(A_122,B_123),A_122,A_122)
      | ~ v1_funct_2(k4_waybel_1(A_122,B_123),u1_struct_0(A_122),u1_struct_0(A_122))
      | ~ v1_funct_1(k4_waybel_1(A_122,B_123))
      | ~ l1_pre_topc(A_122)
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | v2_struct_0(A_122)
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v2_lattice3(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v3_orders_2(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_202])).

tff(c_217,plain,(
    ! [A_124,B_125] :
      ( v4_pre_topc(k6_waybel_0(A_124,B_125),A_124)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_124),B_125),A_124)
      | ~ v5_pre_topc(k4_waybel_1(A_124,B_125),A_124,A_124)
      | ~ v1_funct_2(k4_waybel_1(A_124,B_125),u1_struct_0(A_124),u1_struct_0(A_124))
      | ~ v1_funct_1(k4_waybel_1(A_124,B_125))
      | ~ l1_pre_topc(A_124)
      | v2_struct_0(A_124)
      | ~ l1_orders_2(A_124)
      | ~ v2_lattice3(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | v1_xboole_0(u1_struct_0(A_124)) ) ),
    inference(resolution,[status(thm)],[c_18,c_212])).

tff(c_222,plain,(
    ! [A_126,B_127] :
      ( v4_pre_topc(k6_waybel_0(A_126,B_127),A_126)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_126),B_127),A_126)
      | ~ v5_pre_topc(k4_waybel_1(A_126,B_127),A_126,A_126)
      | ~ v1_funct_1(k4_waybel_1(A_126,B_127))
      | ~ l1_pre_topc(A_126)
      | ~ v2_lattice3(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v1_xboole_0(u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_26,c_217])).

tff(c_229,plain,(
    ! [A_128,B_129] :
      ( v4_pre_topc(k6_waybel_0(A_128,B_129),A_128)
      | ~ v5_pre_topc(k4_waybel_1(A_128,B_129),A_128,A_128)
      | ~ v1_funct_1(k4_waybel_1(A_128,B_129))
      | ~ v2_lattice3(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v1_xboole_0(u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v8_pre_topc(A_128)
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_232,plain,(
    ! [C_51] :
      ( v4_pre_topc(k6_waybel_0('#skF_3',C_51),'#skF_3')
      | ~ v1_funct_1(k4_waybel_1('#skF_3',C_51))
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v8_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_51,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_40,c_229])).

tff(c_235,plain,(
    ! [C_51] :
      ( v4_pre_topc(k6_waybel_0('#skF_3',C_51),'#skF_3')
      | ~ v1_funct_1(k4_waybel_1('#skF_3',C_51))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_51,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68,c_56,c_63,c_54,c_50,c_46,c_232])).

tff(c_245,plain,(
    ! [C_133] :
      ( v4_pre_topc(k6_waybel_0('#skF_3',C_133),'#skF_3')
      | ~ v1_funct_1(k4_waybel_1('#skF_3',C_133))
      | ~ m1_subset_1(C_133,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_132,c_235])).

tff(c_38,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_248,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_245,c_38])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_97,c_248])).

tff(c_253,plain,(
    v1_xboole_0(k6_waybel_0('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( v4_pre_topc(B_10,A_8)
      | ~ v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_257,plain,(
    ! [A_139,B_140] :
      ( v4_pre_topc(k6_waybel_0(A_139,B_140),A_139)
      | ~ v1_xboole_0(k6_waybel_0(A_139,B_140))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_105,c_8])).

tff(c_260,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_257,c_38])).

tff(c_263,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_58,c_68,c_253,c_260])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  
% 2.70/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.70/1.35  
% 2.70/1.35  %Foreground sorts:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Background operators:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Foreground operators:
% 2.70/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.35  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.70/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.70/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.70/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.70/1.35  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.70/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.70/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.70/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.70/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.70/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.70/1.35  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.35  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.70/1.35  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.70/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.35  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.70/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.35  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.70/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.35  
% 2.83/1.37  tff(f_166, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.83/1.37  tff(f_112, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.83/1.37  tff(f_106, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.83/1.37  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.83/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.83/1.37  tff(f_93, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k6_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 2.83/1.37  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.83/1.37  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.83/1.37  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.83/1.37  tff(f_139, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.83/1.37  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.83/1.37  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.83/1.37  tff(c_44, plain, (l1_waybel_9('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_59, plain, (![A_52]: (l1_orders_2(A_52) | ~l1_waybel_9(A_52))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.83/1.37  tff(c_63, plain, (l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_44, c_59])).
% 2.83/1.37  tff(c_48, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_82, plain, (![A_64, B_65]: (v1_funct_1(k4_waybel_1(A_64, B_65)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.83/1.37  tff(c_85, plain, (v1_funct_1(k4_waybel_1('#skF_3', '#skF_4')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_82])).
% 2.83/1.37  tff(c_88, plain, (v1_funct_1(k4_waybel_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_85])).
% 2.83/1.37  tff(c_89, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_88])).
% 2.83/1.37  tff(c_20, plain, (![A_35]: (~v2_struct_0(A_35) | ~v1_lattice3(A_35) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.83/1.37  tff(c_92, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_89, c_20])).
% 2.83/1.37  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_92])).
% 2.83/1.37  tff(c_98, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_88])).
% 2.83/1.37  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_64, plain, (![A_53]: (l1_pre_topc(A_53) | ~l1_waybel_9(A_53))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.83/1.37  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_64])).
% 2.83/1.37  tff(c_97, plain, (v1_funct_1(k4_waybel_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 2.83/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.37  tff(c_105, plain, (![A_68, B_69]: (m1_subset_1(k6_waybel_0(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l1_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.37  tff(c_6, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.37  tff(c_114, plain, (![A_72, A_73, B_74]: (~v1_xboole_0(u1_struct_0(A_72)) | ~r2_hidden(A_73, k6_waybel_0(A_72, B_74)) | ~m1_subset_1(B_74, u1_struct_0(A_72)) | ~l1_orders_2(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_105, c_6])).
% 2.83/1.37  tff(c_124, plain, (![A_77, B_78]: (~v1_xboole_0(u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77) | v2_struct_0(A_77) | v1_xboole_0(k6_waybel_0(A_77, B_78)))), inference(resolution, [status(thm)], [c_4, c_114])).
% 2.83/1.37  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(k6_waybel_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_124])).
% 2.83/1.37  tff(c_130, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(k6_waybel_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_127])).
% 2.83/1.37  tff(c_131, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(k6_waybel_0('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_98, c_130])).
% 2.83/1.37  tff(c_132, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.83/1.37  tff(c_56, plain, (v8_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_46, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_40, plain, (![C_51]: (v5_pre_topc(k4_waybel_1('#skF_3', C_51), '#skF_3', '#skF_3') | ~m1_subset_1(C_51, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_34, plain, (![A_41, B_43]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_41), B_43), A_41) | ~v8_pre_topc(A_41) | ~m1_subset_1(B_43, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.83/1.37  tff(c_26, plain, (![A_38, B_39]: (v1_funct_2(k4_waybel_1(A_38, B_39), u1_struct_0(A_38), u1_struct_0(A_38)) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.83/1.37  tff(c_18, plain, (![A_33, B_34]: (m1_subset_1(k6_domain_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.83/1.37  tff(c_36, plain, (![A_44, B_46]: (k8_relset_1(u1_struct_0(A_44), u1_struct_0(A_44), k4_waybel_1(A_44, B_46), k6_domain_1(u1_struct_0(A_44), B_46))=k6_waybel_0(A_44, B_46) | ~m1_subset_1(B_46, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | ~v2_lattice3(A_44) | ~v5_orders_2(A_44) | ~v3_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.83/1.37  tff(c_24, plain, (![A_38, B_39]: (m1_subset_1(k4_waybel_1(A_38, B_39), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(A_38)))) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.83/1.37  tff(c_183, plain, (![A_105, B_106, C_107, D_108]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_105), u1_struct_0(B_106), C_107, D_108), A_105) | ~v4_pre_topc(D_108, B_106) | ~m1_subset_1(D_108, k1_zfmisc_1(u1_struct_0(B_106))) | ~v5_pre_topc(C_107, A_105, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), u1_struct_0(B_106)))) | ~v1_funct_2(C_107, u1_struct_0(A_105), u1_struct_0(B_106)) | ~v1_funct_1(C_107) | ~l1_pre_topc(B_106) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.83/1.37  tff(c_202, plain, (![A_116, B_117, D_118]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_116), u1_struct_0(A_116), k4_waybel_1(A_116, B_117), D_118), A_116) | ~v4_pre_topc(D_118, A_116) | ~m1_subset_1(D_118, k1_zfmisc_1(u1_struct_0(A_116))) | ~v5_pre_topc(k4_waybel_1(A_116, B_117), A_116, A_116) | ~v1_funct_2(k4_waybel_1(A_116, B_117), u1_struct_0(A_116), u1_struct_0(A_116)) | ~v1_funct_1(k4_waybel_1(A_116, B_117)) | ~l1_pre_topc(A_116) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_24, c_183])).
% 2.83/1.37  tff(c_212, plain, (![A_122, B_123]: (v4_pre_topc(k6_waybel_0(A_122, B_123), A_122) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_122), B_123), A_122) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_122), B_123), k1_zfmisc_1(u1_struct_0(A_122))) | ~v5_pre_topc(k4_waybel_1(A_122, B_123), A_122, A_122) | ~v1_funct_2(k4_waybel_1(A_122, B_123), u1_struct_0(A_122), u1_struct_0(A_122)) | ~v1_funct_1(k4_waybel_1(A_122, B_123)) | ~l1_pre_topc(A_122) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | v2_struct_0(A_122) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v2_lattice3(A_122) | ~v5_orders_2(A_122) | ~v3_orders_2(A_122))), inference(superposition, [status(thm), theory('equality')], [c_36, c_202])).
% 2.83/1.37  tff(c_217, plain, (![A_124, B_125]: (v4_pre_topc(k6_waybel_0(A_124, B_125), A_124) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_124), B_125), A_124) | ~v5_pre_topc(k4_waybel_1(A_124, B_125), A_124, A_124) | ~v1_funct_2(k4_waybel_1(A_124, B_125), u1_struct_0(A_124), u1_struct_0(A_124)) | ~v1_funct_1(k4_waybel_1(A_124, B_125)) | ~l1_pre_topc(A_124) | v2_struct_0(A_124) | ~l1_orders_2(A_124) | ~v2_lattice3(A_124) | ~v5_orders_2(A_124) | ~v3_orders_2(A_124) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | v1_xboole_0(u1_struct_0(A_124)))), inference(resolution, [status(thm)], [c_18, c_212])).
% 2.83/1.37  tff(c_222, plain, (![A_126, B_127]: (v4_pre_topc(k6_waybel_0(A_126, B_127), A_126) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_126), B_127), A_126) | ~v5_pre_topc(k4_waybel_1(A_126, B_127), A_126, A_126) | ~v1_funct_1(k4_waybel_1(A_126, B_127)) | ~l1_pre_topc(A_126) | ~v2_lattice3(A_126) | ~v5_orders_2(A_126) | ~v3_orders_2(A_126) | v1_xboole_0(u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_26, c_217])).
% 2.83/1.37  tff(c_229, plain, (![A_128, B_129]: (v4_pre_topc(k6_waybel_0(A_128, B_129), A_128) | ~v5_pre_topc(k4_waybel_1(A_128, B_129), A_128, A_128) | ~v1_funct_1(k4_waybel_1(A_128, B_129)) | ~v2_lattice3(A_128) | ~v5_orders_2(A_128) | ~v3_orders_2(A_128) | v1_xboole_0(u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v8_pre_topc(A_128) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_34, c_222])).
% 2.83/1.37  tff(c_232, plain, (![C_51]: (v4_pre_topc(k6_waybel_0('#skF_3', C_51), '#skF_3') | ~v1_funct_1(k4_waybel_1('#skF_3', C_51)) | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v8_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(C_51, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_40, c_229])).
% 2.83/1.37  tff(c_235, plain, (![C_51]: (v4_pre_topc(k6_waybel_0('#skF_3', C_51), '#skF_3') | ~v1_funct_1(k4_waybel_1('#skF_3', C_51)) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_51, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68, c_56, c_63, c_54, c_50, c_46, c_232])).
% 2.83/1.37  tff(c_245, plain, (![C_133]: (v4_pre_topc(k6_waybel_0('#skF_3', C_133), '#skF_3') | ~v1_funct_1(k4_waybel_1('#skF_3', C_133)) | ~m1_subset_1(C_133, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_98, c_132, c_235])).
% 2.83/1.37  tff(c_38, plain, (~v4_pre_topc(k6_waybel_0('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 2.83/1.37  tff(c_248, plain, (~v1_funct_1(k4_waybel_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_245, c_38])).
% 2.83/1.37  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_97, c_248])).
% 2.83/1.37  tff(c_253, plain, (v1_xboole_0(k6_waybel_0('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_131])).
% 2.83/1.37  tff(c_8, plain, (![B_10, A_8]: (v4_pre_topc(B_10, A_8) | ~v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.37  tff(c_257, plain, (![A_139, B_140]: (v4_pre_topc(k6_waybel_0(A_139, B_140), A_139) | ~v1_xboole_0(k6_waybel_0(A_139, B_140)) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_105, c_8])).
% 2.83/1.37  tff(c_260, plain, (~v1_xboole_0(k6_waybel_0('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_257, c_38])).
% 2.83/1.37  tff(c_263, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_58, c_68, c_253, c_260])).
% 2.83/1.37  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_263])).
% 2.83/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.37  
% 2.83/1.37  Inference rules
% 2.83/1.37  ----------------------
% 2.83/1.37  #Ref     : 0
% 2.83/1.37  #Sup     : 37
% 2.83/1.37  #Fact    : 0
% 2.83/1.37  #Define  : 0
% 2.83/1.37  #Split   : 2
% 2.83/1.37  #Chain   : 0
% 2.83/1.37  #Close   : 0
% 2.83/1.37  
% 2.83/1.37  Ordering : KBO
% 2.83/1.37  
% 2.83/1.37  Simplification rules
% 2.83/1.37  ----------------------
% 2.83/1.37  #Subsume      : 5
% 2.83/1.37  #Demod        : 22
% 2.83/1.37  #Tautology    : 5
% 2.83/1.37  #SimpNegUnit  : 4
% 2.83/1.37  #BackRed      : 0
% 2.83/1.37  
% 2.83/1.37  #Partial instantiations: 0
% 2.83/1.37  #Strategies tried      : 1
% 2.83/1.37  
% 2.83/1.37  Timing (in seconds)
% 2.83/1.37  ----------------------
% 2.83/1.37  Preprocessing        : 0.33
% 2.83/1.37  Parsing              : 0.18
% 2.83/1.37  CNF conversion       : 0.03
% 2.83/1.37  Main loop            : 0.27
% 2.83/1.37  Inferencing          : 0.12
% 2.83/1.37  Reduction            : 0.07
% 2.83/1.37  Demodulation         : 0.05
% 2.83/1.37  BG Simplification    : 0.02
% 2.83/1.37  Subsumption          : 0.05
% 2.83/1.37  Abstraction          : 0.01
% 2.83/1.37  MUC search           : 0.00
% 2.83/1.37  Cooper               : 0.00
% 2.83/1.37  Total                : 0.64
% 2.83/1.37  Index Insertion      : 0.00
% 2.83/1.37  Index Deletion       : 0.00
% 2.83/1.37  Index Matching       : 0.00
% 2.83/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
