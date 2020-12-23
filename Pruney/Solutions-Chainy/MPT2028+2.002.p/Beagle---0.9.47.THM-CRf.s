%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:18 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 179 expanded)
%              Number of leaves         :   42 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  246 ( 700 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_waybel_0 > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

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

tff(f_163,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k6_waybel_0(A,B))
        & v2_waybel_0(k6_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_waybel_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_136,axiom,(
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

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_42,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_57,plain,(
    ! [A_47] :
      ( l1_orders_2(A_47)
      | ~ l1_waybel_9(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_61,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_46,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_75,plain,(
    ! [A_55,B_56] :
      ( v1_funct_1(k4_waybel_1(A_55,B_56))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_78,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_81,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_78])).

tff(c_82,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_14,plain,(
    ! [A_28] :
      ( ~ v2_struct_0(A_28)
      | ~ v1_lattice3(A_28)
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_85,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_14])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_46,c_85])).

tff(c_90,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_91,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_52,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_92,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(k6_waybel_0(A_57,B_58))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_98,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_61,c_95])).

tff(c_99,plain,(
    ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_98])).

tff(c_100,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_waybel_0(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_63,B_64] :
      ( v1_xboole_0(k6_waybel_0(A_63,B_64))
      | ~ v1_xboole_0(u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_109,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_106])).

tff(c_112,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_109])).

tff(c_113,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_99,c_112])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    ! [A_48] :
      ( l1_pre_topc(A_48)
      | ~ l1_waybel_9(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_54,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    ! [C_46] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_46),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_32,plain,(
    ! [A_36,B_38] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_36),B_38),A_36)
      | ~ v8_pre_topc(A_36)
      | ~ m1_subset_1(B_38,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24,plain,(
    ! [A_33,B_34] :
      ( v1_funct_2(k4_waybel_1(A_33,B_34),u1_struct_0(A_33),u1_struct_0(A_33))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k6_domain_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_39,B_41] :
      ( k8_relset_1(u1_struct_0(A_39),u1_struct_0(A_39),k4_waybel_1(A_39,B_41),k6_domain_1(u1_struct_0(A_39),B_41)) = k6_waybel_0(A_39,B_41)
      | ~ m1_subset_1(B_41,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | ~ v2_lattice3(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v3_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_22,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k4_waybel_1(A_33,B_34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33),u1_struct_0(A_33))))
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_153,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_88),u1_struct_0(B_89),C_90,D_91),A_88)
      | ~ v4_pre_topc(D_91,B_89)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ v5_pre_topc(C_90,A_88,B_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88),u1_struct_0(B_89))))
      | ~ v1_funct_2(C_90,u1_struct_0(A_88),u1_struct_0(B_89))
      | ~ v1_funct_1(C_90)
      | ~ l1_pre_topc(B_89)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_172,plain,(
    ! [A_98,B_99,D_100] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_98),u1_struct_0(A_98),k4_waybel_1(A_98,B_99),D_100),A_98)
      | ~ v4_pre_topc(D_100,A_98)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ v5_pre_topc(k4_waybel_1(A_98,B_99),A_98,A_98)
      | ~ v1_funct_2(k4_waybel_1(A_98,B_99),u1_struct_0(A_98),u1_struct_0(A_98))
      | ~ v1_funct_1(k4_waybel_1(A_98,B_99))
      | ~ l1_pre_topc(A_98)
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_22,c_153])).

tff(c_187,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_34,c_172])).

tff(c_192,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_187])).

tff(c_197,plain,(
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
    inference(resolution,[status(thm)],[c_24,c_192])).

tff(c_201,plain,(
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
    inference(resolution,[status(thm)],[c_32,c_197])).

tff(c_204,plain,(
    ! [C_46] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_46),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_46))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_38,c_201])).

tff(c_207,plain,(
    ! [C_46] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_46),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_46))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66,c_54,c_61,c_52,c_48,c_44,c_204])).

tff(c_209,plain,(
    ! [C_115] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_115),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_115))
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_113,c_207])).

tff(c_36,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_212,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_209,c_36])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_90,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.35  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_waybel_0 > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.64/1.35  
% 2.64/1.35  %Foreground sorts:
% 2.64/1.35  
% 2.64/1.35  
% 2.64/1.35  %Background operators:
% 2.64/1.35  
% 2.64/1.35  
% 2.64/1.35  %Foreground operators:
% 2.64/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.35  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.64/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.64/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.64/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.64/1.35  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.64/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.64/1.35  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.64/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.64/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.64/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.64/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.64/1.35  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.35  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.64/1.35  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.64/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.35  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.64/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.35  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.64/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.35  
% 2.64/1.36  tff(f_163, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.64/1.36  tff(f_109, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.64/1.36  tff(f_103, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.64/1.36  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.64/1.36  tff(f_90, axiom, (![A, B]: ((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(k6_waybel_0(A, B)) & v2_waybel_0(k6_waybel_0(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_waybel_0)).
% 2.64/1.36  tff(f_76, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k6_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 2.64/1.36  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.64/1.36  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.64/1.36  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.64/1.36  tff(f_136, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.64/1.36  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.64/1.36  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_42, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_57, plain, (![A_47]: (l1_orders_2(A_47) | ~l1_waybel_9(A_47))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.64/1.36  tff(c_61, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_42, c_57])).
% 2.64/1.36  tff(c_46, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_75, plain, (![A_55, B_56]: (v1_funct_1(k4_waybel_1(A_55, B_56)) | ~m1_subset_1(B_56, u1_struct_0(A_55)) | ~l1_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.36  tff(c_78, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.64/1.36  tff(c_81, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_78])).
% 2.64/1.36  tff(c_82, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_81])).
% 2.64/1.36  tff(c_14, plain, (![A_28]: (~v2_struct_0(A_28) | ~v1_lattice3(A_28) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.64/1.36  tff(c_85, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_82, c_14])).
% 2.64/1.36  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_46, c_85])).
% 2.64/1.36  tff(c_90, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_81])).
% 2.64/1.36  tff(c_91, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_81])).
% 2.64/1.36  tff(c_52, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_92, plain, (![A_57, B_58]: (~v1_xboole_0(k6_waybel_0(A_57, B_58)) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.64/1.36  tff(c_95, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_92])).
% 2.64/1.36  tff(c_98, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_61, c_95])).
% 2.64/1.36  tff(c_99, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_91, c_98])).
% 2.64/1.36  tff(c_100, plain, (![A_59, B_60]: (m1_subset_1(k6_waybel_0(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.64/1.36  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.36  tff(c_106, plain, (![A_63, B_64]: (v1_xboole_0(k6_waybel_0(A_63, B_64)) | ~v1_xboole_0(u1_struct_0(A_63)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_orders_2(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.64/1.36  tff(c_109, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_106])).
% 2.64/1.36  tff(c_112, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_109])).
% 2.64/1.36  tff(c_113, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_91, c_99, c_112])).
% 2.64/1.36  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_62, plain, (![A_48]: (l1_pre_topc(A_48) | ~l1_waybel_9(A_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.64/1.36  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_62])).
% 2.64/1.36  tff(c_54, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_48, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_44, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_38, plain, (![C_46]: (v5_pre_topc(k4_waybel_1('#skF_2', C_46), '#skF_2', '#skF_2') | ~m1_subset_1(C_46, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_32, plain, (![A_36, B_38]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_36), B_38), A_36) | ~v8_pre_topc(A_36) | ~m1_subset_1(B_38, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.64/1.36  tff(c_24, plain, (![A_33, B_34]: (v1_funct_2(k4_waybel_1(A_33, B_34), u1_struct_0(A_33), u1_struct_0(A_33)) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.36  tff(c_12, plain, (![A_26, B_27]: (m1_subset_1(k6_domain_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.36  tff(c_34, plain, (![A_39, B_41]: (k8_relset_1(u1_struct_0(A_39), u1_struct_0(A_39), k4_waybel_1(A_39, B_41), k6_domain_1(u1_struct_0(A_39), B_41))=k6_waybel_0(A_39, B_41) | ~m1_subset_1(B_41, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | ~v2_lattice3(A_39) | ~v5_orders_2(A_39) | ~v3_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.64/1.36  tff(c_22, plain, (![A_33, B_34]: (m1_subset_1(k4_waybel_1(A_33, B_34), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33), u1_struct_0(A_33)))) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.36  tff(c_153, plain, (![A_88, B_89, C_90, D_91]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_88), u1_struct_0(B_89), C_90, D_91), A_88) | ~v4_pre_topc(D_91, B_89) | ~m1_subset_1(D_91, k1_zfmisc_1(u1_struct_0(B_89))) | ~v5_pre_topc(C_90, A_88, B_89) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88), u1_struct_0(B_89)))) | ~v1_funct_2(C_90, u1_struct_0(A_88), u1_struct_0(B_89)) | ~v1_funct_1(C_90) | ~l1_pre_topc(B_89) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.64/1.36  tff(c_172, plain, (![A_98, B_99, D_100]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_98), u1_struct_0(A_98), k4_waybel_1(A_98, B_99), D_100), A_98) | ~v4_pre_topc(D_100, A_98) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(A_98))) | ~v5_pre_topc(k4_waybel_1(A_98, B_99), A_98, A_98) | ~v1_funct_2(k4_waybel_1(A_98, B_99), u1_struct_0(A_98), u1_struct_0(A_98)) | ~v1_funct_1(k4_waybel_1(A_98, B_99)) | ~l1_pre_topc(A_98) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_22, c_153])).
% 2.64/1.36  tff(c_187, plain, (![A_107, B_108]: (v4_pre_topc(k6_waybel_0(A_107, B_108), A_107) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_107), B_108), A_107) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_107), B_108), k1_zfmisc_1(u1_struct_0(A_107))) | ~v5_pre_topc(k4_waybel_1(A_107, B_108), A_107, A_107) | ~v1_funct_2(k4_waybel_1(A_107, B_108), u1_struct_0(A_107), u1_struct_0(A_107)) | ~v1_funct_1(k4_waybel_1(A_107, B_108)) | ~l1_pre_topc(A_107) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | v2_struct_0(A_107) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | ~v2_lattice3(A_107) | ~v5_orders_2(A_107) | ~v3_orders_2(A_107))), inference(superposition, [status(thm), theory('equality')], [c_34, c_172])).
% 2.64/1.36  tff(c_192, plain, (![A_109, B_110]: (v4_pre_topc(k6_waybel_0(A_109, B_110), A_109) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_109), B_110), A_109) | ~v5_pre_topc(k4_waybel_1(A_109, B_110), A_109, A_109) | ~v1_funct_2(k4_waybel_1(A_109, B_110), u1_struct_0(A_109), u1_struct_0(A_109)) | ~v1_funct_1(k4_waybel_1(A_109, B_110)) | ~l1_pre_topc(A_109) | v2_struct_0(A_109) | ~l1_orders_2(A_109) | ~v2_lattice3(A_109) | ~v5_orders_2(A_109) | ~v3_orders_2(A_109) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | v1_xboole_0(u1_struct_0(A_109)))), inference(resolution, [status(thm)], [c_12, c_187])).
% 2.64/1.36  tff(c_197, plain, (![A_111, B_112]: (v4_pre_topc(k6_waybel_0(A_111, B_112), A_111) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_111), B_112), A_111) | ~v5_pre_topc(k4_waybel_1(A_111, B_112), A_111, A_111) | ~v1_funct_1(k4_waybel_1(A_111, B_112)) | ~l1_pre_topc(A_111) | ~v2_lattice3(A_111) | ~v5_orders_2(A_111) | ~v3_orders_2(A_111) | v1_xboole_0(u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_24, c_192])).
% 2.64/1.36  tff(c_201, plain, (![A_113, B_114]: (v4_pre_topc(k6_waybel_0(A_113, B_114), A_113) | ~v5_pre_topc(k4_waybel_1(A_113, B_114), A_113, A_113) | ~v1_funct_1(k4_waybel_1(A_113, B_114)) | ~v2_lattice3(A_113) | ~v5_orders_2(A_113) | ~v3_orders_2(A_113) | v1_xboole_0(u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v8_pre_topc(A_113) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_32, c_197])).
% 2.64/1.36  tff(c_204, plain, (![C_46]: (v4_pre_topc(k6_waybel_0('#skF_2', C_46), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_46)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_46, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_201])).
% 2.64/1.36  tff(c_207, plain, (![C_46]: (v4_pre_topc(k6_waybel_0('#skF_2', C_46), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_46)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_46, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66, c_54, c_61, c_52, c_48, c_44, c_204])).
% 2.64/1.36  tff(c_209, plain, (![C_115]: (v4_pre_topc(k6_waybel_0('#skF_2', C_115), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_115)) | ~m1_subset_1(C_115, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_91, c_113, c_207])).
% 2.64/1.36  tff(c_36, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.36  tff(c_212, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_209, c_36])).
% 2.64/1.36  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_90, c_212])).
% 2.64/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  Inference rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Ref     : 0
% 2.64/1.36  #Sup     : 28
% 2.64/1.36  #Fact    : 0
% 2.64/1.36  #Define  : 0
% 2.64/1.36  #Split   : 1
% 2.64/1.36  #Chain   : 0
% 2.64/1.36  #Close   : 0
% 2.64/1.36  
% 2.64/1.36  Ordering : KBO
% 2.64/1.36  
% 2.64/1.36  Simplification rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Subsume      : 3
% 2.64/1.36  #Demod        : 15
% 2.64/1.36  #Tautology    : 4
% 2.64/1.36  #SimpNegUnit  : 3
% 2.64/1.36  #BackRed      : 0
% 2.64/1.36  
% 2.64/1.36  #Partial instantiations: 0
% 2.64/1.36  #Strategies tried      : 1
% 2.64/1.36  
% 2.64/1.36  Timing (in seconds)
% 2.64/1.36  ----------------------
% 2.64/1.37  Preprocessing        : 0.33
% 2.64/1.37  Parsing              : 0.19
% 2.64/1.37  CNF conversion       : 0.03
% 2.64/1.37  Main loop            : 0.27
% 2.64/1.37  Inferencing          : 0.12
% 2.64/1.37  Reduction            : 0.07
% 2.64/1.37  Demodulation         : 0.05
% 2.64/1.37  BG Simplification    : 0.02
% 2.64/1.37  Subsumption          : 0.04
% 2.64/1.37  Abstraction          : 0.01
% 2.64/1.37  MUC search           : 0.00
% 2.64/1.37  Cooper               : 0.00
% 2.64/1.37  Total                : 0.64
% 2.64/1.37  Index Insertion      : 0.00
% 2.64/1.37  Index Deletion       : 0.00
% 2.64/1.37  Index Matching       : 0.00
% 2.64/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
