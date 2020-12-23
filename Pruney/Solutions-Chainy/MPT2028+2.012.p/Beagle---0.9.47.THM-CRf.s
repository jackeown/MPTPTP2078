%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:19 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 382 expanded)
%              Number of leaves         :   47 ( 159 expanded)
%              Depth                    :   12
%              Number of atoms          :  239 (1560 expanded)
%              Number of equality atoms :    8 (  41 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_waybel_0 > v1_waybel_0 > v13_waybel_0 > v12_waybel_0 > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

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

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

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

tff(f_173,negated_conjecture,(
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

tff(f_119,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v1_waybel_0(B,A)
          & v2_waybel_0(B,A)
          & v12_waybel_0(B,A)
          & v13_waybel_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc11_waybel_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_46,plain,(
    ! [C_46] :
      ( v5_pre_topc(k4_waybel_1('#skF_3',C_46),'#skF_3','#skF_3')
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    l1_waybel_9('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_70,plain,(
    ! [A_48] :
      ( l1_orders_2(A_48)
      | ~ l1_waybel_9(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_74,plain,(
    l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_52,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_188,plain,(
    ! [A_77,B_78] :
      ( v1_funct_1(k4_waybel_1(A_77,B_78))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_191,plain,
    ( v1_funct_1(k4_waybel_1('#skF_3','#skF_4'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_194,plain,
    ( v1_funct_1(k4_waybel_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_191])).

tff(c_195,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_16,plain,(
    ! [A_30] :
      ( ~ v2_struct_0(A_30)
      | ~ v2_lattice3(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_199,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_195,c_16])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_52,c_199])).

tff(c_205,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_32,plain,(
    ! [A_33,B_34] :
      ( v1_funct_2(k4_waybel_1(A_33,B_34),u1_struct_0(A_33),u1_struct_0(A_33))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_65,plain,(
    ! [A_47] :
      ( l1_pre_topc(A_47)
      | ~ l1_waybel_9(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_69,plain,(
    l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_65])).

tff(c_204,plain,(
    v1_funct_1(k4_waybel_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_60,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_77,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_82,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_116,plain,(
    ! [A_66] :
      ( m1_subset_1('#skF_2'(A_66),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v2_lattice3(A_66)
      | ~ v1_lattice3(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_73] :
      ( v1_xboole_0('#skF_2'(A_73))
      | ~ v1_xboole_0(u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v2_lattice3(A_73)
      | ~ v1_lattice3(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_2'('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_144])).

tff(c_150,plain,(
    v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_74,c_147])).

tff(c_26,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0('#skF_2'(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v2_lattice3(A_31)
      | ~ v1_lattice3(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_153,plain,
    ( ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_26])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_74,c_153])).

tff(c_159,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_158,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_165,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k6_domain_1(A_75,B_76),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_174,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_165])).

tff(c_178,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_174])).

tff(c_179,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_178])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    v8_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_213,plain,(
    ! [A_87,B_88] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_87),B_88),A_87)
      | ~ v8_pre_topc(A_87)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_216,plain,
    ( v4_pre_topc(k1_tarski('#skF_4'),'#skF_3')
    | ~ v8_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_213])).

tff(c_218,plain,
    ( v4_pre_topc(k1_tarski('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_69,c_48,c_62,c_216])).

tff(c_219,plain,(
    v4_pre_topc(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_218])).

tff(c_279,plain,(
    ! [A_98,B_99] :
      ( k8_relset_1(u1_struct_0(A_98),u1_struct_0(A_98),k4_waybel_1(A_98,B_99),k6_domain_1(u1_struct_0(A_98),B_99)) = k6_waybel_0(A_98,B_99)
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v2_lattice3(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v3_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_288,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k4_waybel_1('#skF_3','#skF_4'),k1_tarski('#skF_4')) = k6_waybel_0('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_279])).

tff(c_292,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k4_waybel_1('#skF_3','#skF_4'),k1_tarski('#skF_4')) = k6_waybel_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_52,c_74,c_48,c_288])).

tff(c_30,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k4_waybel_1(A_33,B_34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33),u1_struct_0(A_33))))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_405,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_118),u1_struct_0(B_119),C_120,D_121),A_118)
      | ~ v4_pre_topc(D_121,B_119)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(u1_struct_0(B_119)))
      | ~ v5_pre_topc(C_120,A_118,B_119)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118),u1_struct_0(B_119))))
      | ~ v1_funct_2(C_120,u1_struct_0(A_118),u1_struct_0(B_119))
      | ~ v1_funct_1(C_120)
      | ~ l1_pre_topc(B_119)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_546,plain,(
    ! [A_137,B_138,D_139] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_137),u1_struct_0(A_137),k4_waybel_1(A_137,B_138),D_139),A_137)
      | ~ v4_pre_topc(D_139,A_137)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v5_pre_topc(k4_waybel_1(A_137,B_138),A_137,A_137)
      | ~ v1_funct_2(k4_waybel_1(A_137,B_138),u1_struct_0(A_137),u1_struct_0(A_137))
      | ~ v1_funct_1(k4_waybel_1(A_137,B_138))
      | ~ l1_pre_topc(A_137)
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_405])).

tff(c_553,plain,
    ( v4_pre_topc(k6_waybel_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v4_pre_topc(k1_tarski('#skF_4'),'#skF_3')
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v5_pre_topc(k4_waybel_1('#skF_3','#skF_4'),'#skF_3','#skF_3')
    | ~ v1_funct_2(k4_waybel_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_waybel_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_546])).

tff(c_559,plain,
    ( v4_pre_topc(k6_waybel_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v5_pre_topc(k4_waybel_1('#skF_3','#skF_4'),'#skF_3','#skF_3')
    | ~ v1_funct_2(k4_waybel_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48,c_69,c_204,c_179,c_219,c_553])).

tff(c_560,plain,
    ( ~ v5_pre_topc(k4_waybel_1('#skF_3','#skF_4'),'#skF_3','#skF_3')
    | ~ v1_funct_2(k4_waybel_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_44,c_559])).

tff(c_561,plain,(
    ~ v1_funct_2(k4_waybel_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_564,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_561])).

tff(c_567,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48,c_564])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_567])).

tff(c_570,plain,(
    ~ v5_pre_topc(k4_waybel_1('#skF_3','#skF_4'),'#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_574,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_570])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.64  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_waybel_0 > v1_waybel_0 > v13_waybel_0 > v12_waybel_0 > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.74/1.64  
% 3.74/1.64  %Foreground sorts:
% 3.74/1.64  
% 3.74/1.64  
% 3.74/1.64  %Background operators:
% 3.74/1.64  
% 3.74/1.64  
% 3.74/1.64  %Foreground operators:
% 3.74/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.74/1.64  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.74/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.74/1.64  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.74/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.64  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.74/1.64  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.74/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.74/1.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.74/1.64  tff(v12_waybel_0, type, v12_waybel_0: ($i * $i) > $o).
% 3.74/1.64  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.74/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.74/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.74/1.64  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.74/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.74/1.64  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.74/1.64  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 3.74/1.64  tff(v1_waybel_0, type, v1_waybel_0: ($i * $i) > $o).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.74/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.64  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 3.74/1.64  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.74/1.64  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.74/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.74/1.64  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.74/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.64  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 3.74/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.64  
% 3.74/1.66  tff(f_173, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_waybel_9)).
% 3.74/1.66  tff(f_119, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 3.74/1.66  tff(f_113, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 3.74/1.66  tff(f_74, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 3.74/1.66  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.74/1.66  tff(f_100, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (?[B]: (((((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v1_waybel_0(B, A)) & v2_waybel_0(B, A)) & v12_waybel_0(B, A)) & v13_waybel_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc11_waybel_0)).
% 3.74/1.66  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.74/1.66  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.74/1.66  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_pcomps_1)).
% 3.74/1.66  tff(f_146, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_9)).
% 3.74/1.66  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 3.74/1.66  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.66  tff(c_46, plain, (![C_46]: (v5_pre_topc(k4_waybel_1('#skF_3', C_46), '#skF_3', '#skF_3') | ~m1_subset_1(C_46, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.66  tff(c_50, plain, (l1_waybel_9('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.66  tff(c_70, plain, (![A_48]: (l1_orders_2(A_48) | ~l1_waybel_9(A_48))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.74/1.66  tff(c_74, plain, (l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_50, c_70])).
% 3.74/1.66  tff(c_52, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.66  tff(c_188, plain, (![A_77, B_78]: (v1_funct_1(k4_waybel_1(A_77, B_78)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.66  tff(c_191, plain, (v1_funct_1(k4_waybel_1('#skF_3', '#skF_4')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_188])).
% 3.74/1.67  tff(c_194, plain, (v1_funct_1(k4_waybel_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_191])).
% 3.74/1.67  tff(c_195, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_194])).
% 3.74/1.67  tff(c_16, plain, (![A_30]: (~v2_struct_0(A_30) | ~v2_lattice3(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.67  tff(c_199, plain, (~v2_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_195, c_16])).
% 3.74/1.67  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_52, c_199])).
% 3.74/1.67  tff(c_205, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_194])).
% 3.74/1.67  tff(c_32, plain, (![A_33, B_34]: (v1_funct_2(k4_waybel_1(A_33, B_34), u1_struct_0(A_33), u1_struct_0(A_33)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.67  tff(c_44, plain, (~v4_pre_topc(k6_waybel_0('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_65, plain, (![A_47]: (l1_pre_topc(A_47) | ~l1_waybel_9(A_47))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.74/1.67  tff(c_69, plain, (l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_65])).
% 3.74/1.67  tff(c_204, plain, (v1_funct_1(k4_waybel_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_194])).
% 3.74/1.67  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_58, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_54, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_77, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.74/1.67  tff(c_81, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_77])).
% 3.74/1.67  tff(c_82, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.74/1.67  tff(c_116, plain, (![A_66]: (m1_subset_1('#skF_2'(A_66), k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v2_lattice3(A_66) | ~v1_lattice3(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.74/1.67  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.67  tff(c_144, plain, (![A_73]: (v1_xboole_0('#skF_2'(A_73)) | ~v1_xboole_0(u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v2_lattice3(A_73) | ~v1_lattice3(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73))), inference(resolution, [status(thm)], [c_116, c_2])).
% 3.74/1.67  tff(c_147, plain, (v1_xboole_0('#skF_2'('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_82, c_144])).
% 3.74/1.67  tff(c_150, plain, (v1_xboole_0('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_74, c_147])).
% 3.74/1.67  tff(c_26, plain, (![A_31]: (~v1_xboole_0('#skF_2'(A_31)) | ~l1_orders_2(A_31) | ~v2_lattice3(A_31) | ~v1_lattice3(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.74/1.67  tff(c_153, plain, (~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_150, c_26])).
% 3.74/1.67  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_74, c_153])).
% 3.74/1.67  tff(c_159, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_81])).
% 3.74/1.67  tff(c_158, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_81])).
% 3.74/1.67  tff(c_165, plain, (![A_75, B_76]: (m1_subset_1(k6_domain_1(A_75, B_76), k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.74/1.67  tff(c_174, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_165])).
% 3.74/1.67  tff(c_178, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_174])).
% 3.74/1.67  tff(c_179, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_159, c_178])).
% 3.74/1.67  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_62, plain, (v8_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.74/1.67  tff(c_213, plain, (![A_87, B_88]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_87), B_88), A_87) | ~v8_pre_topc(A_87) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.67  tff(c_216, plain, (v4_pre_topc(k1_tarski('#skF_4'), '#skF_3') | ~v8_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_158, c_213])).
% 3.74/1.67  tff(c_218, plain, (v4_pre_topc(k1_tarski('#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_69, c_48, c_62, c_216])).
% 3.74/1.67  tff(c_219, plain, (v4_pre_topc(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_205, c_218])).
% 3.74/1.67  tff(c_279, plain, (![A_98, B_99]: (k8_relset_1(u1_struct_0(A_98), u1_struct_0(A_98), k4_waybel_1(A_98, B_99), k6_domain_1(u1_struct_0(A_98), B_99))=k6_waybel_0(A_98, B_99) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v2_lattice3(A_98) | ~v5_orders_2(A_98) | ~v3_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.74/1.67  tff(c_288, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k4_waybel_1('#skF_3', '#skF_4'), k1_tarski('#skF_4'))=k6_waybel_0('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_158, c_279])).
% 3.74/1.67  tff(c_292, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k4_waybel_1('#skF_3', '#skF_4'), k1_tarski('#skF_4'))=k6_waybel_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_52, c_74, c_48, c_288])).
% 3.74/1.67  tff(c_30, plain, (![A_33, B_34]: (m1_subset_1(k4_waybel_1(A_33, B_34), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33), u1_struct_0(A_33)))) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.74/1.67  tff(c_405, plain, (![A_118, B_119, C_120, D_121]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_118), u1_struct_0(B_119), C_120, D_121), A_118) | ~v4_pre_topc(D_121, B_119) | ~m1_subset_1(D_121, k1_zfmisc_1(u1_struct_0(B_119))) | ~v5_pre_topc(C_120, A_118, B_119) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118), u1_struct_0(B_119)))) | ~v1_funct_2(C_120, u1_struct_0(A_118), u1_struct_0(B_119)) | ~v1_funct_1(C_120) | ~l1_pre_topc(B_119) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.74/1.67  tff(c_546, plain, (![A_137, B_138, D_139]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_137), u1_struct_0(A_137), k4_waybel_1(A_137, B_138), D_139), A_137) | ~v4_pre_topc(D_139, A_137) | ~m1_subset_1(D_139, k1_zfmisc_1(u1_struct_0(A_137))) | ~v5_pre_topc(k4_waybel_1(A_137, B_138), A_137, A_137) | ~v1_funct_2(k4_waybel_1(A_137, B_138), u1_struct_0(A_137), u1_struct_0(A_137)) | ~v1_funct_1(k4_waybel_1(A_137, B_138)) | ~l1_pre_topc(A_137) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_30, c_405])).
% 3.74/1.67  tff(c_553, plain, (v4_pre_topc(k6_waybel_0('#skF_3', '#skF_4'), '#skF_3') | ~v4_pre_topc(k1_tarski('#skF_4'), '#skF_3') | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc(k4_waybel_1('#skF_3', '#skF_4'), '#skF_3', '#skF_3') | ~v1_funct_2(k4_waybel_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_waybel_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_292, c_546])).
% 3.74/1.67  tff(c_559, plain, (v4_pre_topc(k6_waybel_0('#skF_3', '#skF_4'), '#skF_3') | ~v5_pre_topc(k4_waybel_1('#skF_3', '#skF_4'), '#skF_3', '#skF_3') | ~v1_funct_2(k4_waybel_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48, c_69, c_204, c_179, c_219, c_553])).
% 3.74/1.67  tff(c_560, plain, (~v5_pre_topc(k4_waybel_1('#skF_3', '#skF_4'), '#skF_3', '#skF_3') | ~v1_funct_2(k4_waybel_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_205, c_44, c_559])).
% 3.74/1.67  tff(c_561, plain, (~v1_funct_2(k4_waybel_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_560])).
% 3.74/1.67  tff(c_564, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_561])).
% 3.74/1.67  tff(c_567, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48, c_564])).
% 3.74/1.67  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_567])).
% 3.74/1.67  tff(c_570, plain, (~v5_pre_topc(k4_waybel_1('#skF_3', '#skF_4'), '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_560])).
% 3.74/1.67  tff(c_574, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_570])).
% 3.74/1.67  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_574])).
% 3.74/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.67  
% 3.74/1.67  Inference rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Ref     : 0
% 3.74/1.67  #Sup     : 115
% 3.74/1.67  #Fact    : 0
% 3.74/1.67  #Define  : 0
% 3.74/1.67  #Split   : 5
% 3.74/1.67  #Chain   : 0
% 3.74/1.67  #Close   : 0
% 3.74/1.67  
% 3.74/1.67  Ordering : KBO
% 3.74/1.67  
% 3.74/1.67  Simplification rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Subsume      : 4
% 3.74/1.67  #Demod        : 61
% 3.74/1.67  #Tautology    : 32
% 3.74/1.67  #SimpNegUnit  : 9
% 3.74/1.67  #BackRed      : 0
% 3.74/1.67  
% 3.74/1.67  #Partial instantiations: 0
% 3.74/1.67  #Strategies tried      : 1
% 3.74/1.67  
% 3.74/1.67  Timing (in seconds)
% 3.74/1.67  ----------------------
% 3.74/1.67  Preprocessing        : 0.38
% 3.74/1.67  Parsing              : 0.20
% 3.74/1.67  CNF conversion       : 0.03
% 3.74/1.67  Main loop            : 0.45
% 3.74/1.67  Inferencing          : 0.18
% 3.74/1.67  Reduction            : 0.12
% 3.74/1.67  Demodulation         : 0.09
% 3.74/1.67  BG Simplification    : 0.03
% 3.74/1.67  Subsumption          : 0.08
% 3.74/1.67  Abstraction          : 0.03
% 3.74/1.67  MUC search           : 0.00
% 3.74/1.67  Cooper               : 0.00
% 3.74/1.67  Total                : 0.87
% 3.74/1.67  Index Insertion      : 0.00
% 3.74/1.67  Index Deletion       : 0.00
% 3.74/1.67  Index Matching       : 0.00
% 3.74/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
