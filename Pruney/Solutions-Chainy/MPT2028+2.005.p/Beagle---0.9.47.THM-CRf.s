%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:18 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 731 expanded)
%              Number of leaves         :   43 ( 274 expanded)
%              Depth                    :   16
%              Number of atoms          :  256 (2270 expanded)
%              Number of equality atoms :    8 ( 180 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v8_pre_topc(A)
           => v4_pre_topc(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_pcomps_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_relset_1(u1_struct_0(A),u1_struct_0(A),k4_waybel_1(A,B),k6_domain_1(u1_struct_0(A),B)) = k6_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow_0)).

tff(c_40,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_61,plain,(
    ! [A_45] :
      ( l1_orders_2(A_45)
      | ~ l1_waybel_9(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_65,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_61])).

tff(c_14,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_72])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_77,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_38])).

tff(c_44,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_86,plain,(
    ! [A_53,B_54] :
      ( v1_funct_1(k4_waybel_1(A_53,B_54))
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89,plain,(
    ! [B_54] :
      ( v1_funct_1(k4_waybel_1('#skF_2',B_54))
      | ~ m1_subset_1(B_54,k2_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_86])).

tff(c_91,plain,(
    ! [B_54] :
      ( v1_funct_1(k4_waybel_1('#skF_2',B_54))
      | ~ m1_subset_1(B_54,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_89])).

tff(c_92,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_16,plain,(
    ! [A_27] :
      ( ~ v2_struct_0(A_27)
      | ~ v1_lattice3(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_16])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_106])).

tff(c_113,plain,(
    ! [B_57] :
      ( v1_funct_1(k4_waybel_1('#skF_2',B_57))
      | ~ m1_subset_1(B_57,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_117,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_77,c_113])).

tff(c_36,plain,(
    ! [C_42] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_42),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_42,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_82,plain,(
    ! [C_42] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_42),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_42,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_112,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    ! [A_44] :
      ( l1_pre_topc(A_44)
      | ~ l1_waybel_9(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_52,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_132,plain,(
    ! [A_61,B_62] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_61),B_62),A_61)
      | ~ v8_pre_topc(A_61)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_135,plain,(
    ! [B_62] :
      ( v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_62),'#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_132])).

tff(c_137,plain,(
    ! [B_62] :
      ( v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_62),'#skF_2')
      | ~ m1_subset_1(B_62,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60,c_76,c_52,c_135])).

tff(c_138,plain,(
    ! [B_62] :
      ( v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_62),'#skF_2')
      | ~ m1_subset_1(B_62,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_137])).

tff(c_118,plain,(
    ! [A_58,B_59] :
      ( v1_funct_2(k4_waybel_1(A_58,B_59),u1_struct_0(A_58),u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_121,plain,(
    ! [B_59] :
      ( v1_funct_2(k4_waybel_1('#skF_2',B_59),k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_118])).

tff(c_126,plain,(
    ! [B_59] :
      ( v1_funct_2(k4_waybel_1('#skF_2',B_59),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_59,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_76,c_76,c_121])).

tff(c_127,plain,(
    ! [B_59] :
      ( v1_funct_2(k4_waybel_1('#skF_2',B_59),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_59,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_126])).

tff(c_12,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k6_domain_1(A_24,B_25),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_154,plain,(
    ! [A_67,B_68] :
      ( k8_relset_1(u1_struct_0(A_67),u1_struct_0(A_67),k4_waybel_1(A_67,B_68),k6_domain_1(u1_struct_0(A_67),B_68)) = k6_waybel_0(A_67,B_68)
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67)
      | ~ v2_lattice3(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v3_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_163,plain,(
    ! [B_68] :
      ( k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2',B_68),k6_domain_1(u1_struct_0('#skF_2'),B_68)) = k6_waybel_0('#skF_2',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_154])).

tff(c_173,plain,(
    ! [B_68] :
      ( k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k4_waybel_1('#skF_2',B_68),k6_domain_1(k2_struct_0('#skF_2'),B_68)) = k6_waybel_0('#skF_2',B_68)
      | ~ m1_subset_1(B_68,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_65,c_76,c_76,c_76,c_163])).

tff(c_140,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k4_waybel_1(A_64,B_65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64),u1_struct_0(A_64))))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_143,plain,(
    ! [B_65] :
      ( m1_subset_1(k4_waybel_1('#skF_2',B_65),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_140])).

tff(c_148,plain,(
    ! [B_65] :
      ( m1_subset_1(k4_waybel_1('#skF_2',B_65),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_65,k2_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_76,c_76,c_143])).

tff(c_149,plain,(
    ! [B_65] :
      ( m1_subset_1(k4_waybel_1('#skF_2',B_65),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ m1_subset_1(B_65,k2_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_148])).

tff(c_317,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_96),u1_struct_0(B_97),C_98,D_99),A_96)
      | ~ v4_pre_topc(D_99,B_97)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ v5_pre_topc(C_98,A_96,B_97)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),u1_struct_0(B_97))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_96),u1_struct_0(B_97))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_97)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_324,plain,(
    ! [B_97,C_98,D_99] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_97),C_98,D_99),'#skF_2')
      | ~ v4_pre_topc(D_99,B_97)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ v5_pre_topc(C_98,'#skF_2',B_97)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_97))))
      | ~ v1_funct_2(C_98,u1_struct_0('#skF_2'),u1_struct_0(B_97))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_97)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_317])).

tff(c_341,plain,(
    ! [B_104,C_105,D_106] :
      ( v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_104),C_105,D_106),'#skF_2')
      | ~ v4_pre_topc(D_106,B_104)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(u1_struct_0(B_104)))
      | ~ v5_pre_topc(C_105,'#skF_2',B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,k2_struct_0('#skF_2'),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_pre_topc(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76,c_76,c_324])).

tff(c_346,plain,(
    ! [C_105,D_106] :
      ( v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_2'),C_105,D_106),'#skF_2')
      | ~ v4_pre_topc(D_106,'#skF_2')
      | ~ m1_subset_1(D_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_105,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_105,k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_105)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_341])).

tff(c_350,plain,(
    ! [C_107,D_108] :
      ( v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_107,D_108),'#skF_2')
      | ~ v4_pre_topc(D_108,'#skF_2')
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_107,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_107,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76,c_76,c_76,c_346])).

tff(c_367,plain,(
    ! [B_112,D_113] :
      ( v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k4_waybel_1('#skF_2',B_112),D_113),'#skF_2')
      | ~ v4_pre_topc(D_113,'#skF_2')
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2',B_112),'#skF_2','#skF_2')
      | ~ v1_funct_2(k4_waybel_1('#skF_2',B_112),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_112))
      | ~ m1_subset_1(B_112,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_149,c_350])).

tff(c_376,plain,(
    ! [B_114] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',B_114),'#skF_2')
      | ~ v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_114),'#skF_2')
      | ~ m1_subset_1(k6_domain_1(k2_struct_0('#skF_2'),B_114),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(k4_waybel_1('#skF_2',B_114),'#skF_2','#skF_2')
      | ~ v1_funct_2(k4_waybel_1('#skF_2',B_114),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_114))
      | ~ m1_subset_1(B_114,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_114,k2_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_367])).

tff(c_381,plain,(
    ! [B_25] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',B_25),'#skF_2')
      | ~ v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_25),'#skF_2')
      | ~ v5_pre_topc(k4_waybel_1('#skF_2',B_25),'#skF_2','#skF_2')
      | ~ v1_funct_2(k4_waybel_1('#skF_2',B_25),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_25))
      | ~ m1_subset_1(B_25,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_376])).

tff(c_382,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_18,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k2_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_385,plain,
    ( ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_382,c_18])).

tff(c_388,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_385])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_388])).

tff(c_414,plain,(
    ! [B_118] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',B_118),'#skF_2')
      | ~ v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_118),'#skF_2')
      | ~ v5_pre_topc(k4_waybel_1('#skF_2',B_118),'#skF_2','#skF_2')
      | ~ v1_funct_2(k4_waybel_1('#skF_2',B_118),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_118))
      | ~ m1_subset_1(B_118,k2_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_419,plain,(
    ! [B_119] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',B_119),'#skF_2')
      | ~ v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'),B_119),'#skF_2')
      | ~ v5_pre_topc(k4_waybel_1('#skF_2',B_119),'#skF_2','#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_119))
      | ~ m1_subset_1(B_119,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_127,c_414])).

tff(c_425,plain,(
    ! [B_120] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',B_120),'#skF_2')
      | ~ v5_pre_topc(k4_waybel_1('#skF_2',B_120),'#skF_2','#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',B_120))
      | ~ m1_subset_1(B_120,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_138,c_419])).

tff(c_430,plain,(
    ! [C_121] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_121),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_121))
      | ~ m1_subset_1(C_121,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_82,c_425])).

tff(c_34,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_433,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_430,c_34])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_117,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.49  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.19/1.49  
% 3.19/1.49  %Foreground sorts:
% 3.19/1.49  
% 3.19/1.49  
% 3.19/1.49  %Background operators:
% 3.19/1.49  
% 3.19/1.49  
% 3.19/1.49  %Foreground operators:
% 3.19/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.19/1.49  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.19/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.19/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.19/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.19/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.19/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.19/1.49  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.19/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.19/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.19/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.19/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.19/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.19/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.19/1.49  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.49  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 3.19/1.49  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.19/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.19/1.49  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.19/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.19/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.19/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.49  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 3.19/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.49  
% 3.40/1.51  tff(f_149, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_waybel_9)).
% 3.40/1.51  tff(f_95, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 3.40/1.51  tff(f_61, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.40/1.51  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.40/1.51  tff(f_89, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 3.40/1.51  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.40/1.51  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_pcomps_1)).
% 3.40/1.51  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.40/1.51  tff(f_122, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_9)).
% 3.40/1.51  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 3.40/1.51  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_yellow_0)).
% 3.40/1.51  tff(c_40, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_61, plain, (![A_45]: (l1_orders_2(A_45) | ~l1_waybel_9(A_45))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.51  tff(c_65, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_40, c_61])).
% 3.40/1.51  tff(c_14, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.51  tff(c_67, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.51  tff(c_72, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_14, c_67])).
% 3.40/1.51  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_65, c_72])).
% 3.40/1.51  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_77, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_38])).
% 3.40/1.51  tff(c_44, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_86, plain, (![A_53, B_54]: (v1_funct_1(k4_waybel_1(A_53, B_54)) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l1_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.40/1.51  tff(c_89, plain, (![B_54]: (v1_funct_1(k4_waybel_1('#skF_2', B_54)) | ~m1_subset_1(B_54, k2_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_86])).
% 3.40/1.51  tff(c_91, plain, (![B_54]: (v1_funct_1(k4_waybel_1('#skF_2', B_54)) | ~m1_subset_1(B_54, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_89])).
% 3.40/1.51  tff(c_92, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_91])).
% 3.40/1.51  tff(c_16, plain, (![A_27]: (~v2_struct_0(A_27) | ~v1_lattice3(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.51  tff(c_106, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_92, c_16])).
% 3.40/1.51  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_106])).
% 3.40/1.51  tff(c_113, plain, (![B_57]: (v1_funct_1(k4_waybel_1('#skF_2', B_57)) | ~m1_subset_1(B_57, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_91])).
% 3.40/1.51  tff(c_117, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_77, c_113])).
% 3.40/1.51  tff(c_36, plain, (![C_42]: (v5_pre_topc(k4_waybel_1('#skF_2', C_42), '#skF_2', '#skF_2') | ~m1_subset_1(C_42, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_82, plain, (![C_42]: (v5_pre_topc(k4_waybel_1('#skF_2', C_42), '#skF_2', '#skF_2') | ~m1_subset_1(C_42, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36])).
% 3.40/1.51  tff(c_112, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_91])).
% 3.40/1.51  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_56, plain, (![A_44]: (l1_pre_topc(A_44) | ~l1_waybel_9(A_44))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.51  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_56])).
% 3.40/1.51  tff(c_52, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_132, plain, (![A_61, B_62]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_61), B_62), A_61) | ~v8_pre_topc(A_61) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.40/1.51  tff(c_135, plain, (![B_62]: (v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_62), '#skF_2') | ~v8_pre_topc('#skF_2') | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_132])).
% 3.40/1.51  tff(c_137, plain, (![B_62]: (v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_62), '#skF_2') | ~m1_subset_1(B_62, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_60, c_76, c_52, c_135])).
% 3.40/1.51  tff(c_138, plain, (![B_62]: (v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_62), '#skF_2') | ~m1_subset_1(B_62, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_137])).
% 3.40/1.51  tff(c_118, plain, (![A_58, B_59]: (v1_funct_2(k4_waybel_1(A_58, B_59), u1_struct_0(A_58), u1_struct_0(A_58)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.40/1.51  tff(c_121, plain, (![B_59]: (v1_funct_2(k4_waybel_1('#skF_2', B_59), k2_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_59, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_118])).
% 3.40/1.51  tff(c_126, plain, (![B_59]: (v1_funct_2(k4_waybel_1('#skF_2', B_59), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1(B_59, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_76, c_76, c_121])).
% 3.40/1.51  tff(c_127, plain, (![B_59]: (v1_funct_2(k4_waybel_1('#skF_2', B_59), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1(B_59, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_126])).
% 3.40/1.51  tff(c_12, plain, (![A_24, B_25]: (m1_subset_1(k6_domain_1(A_24, B_25), k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.51  tff(c_50, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_46, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_42, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_154, plain, (![A_67, B_68]: (k8_relset_1(u1_struct_0(A_67), u1_struct_0(A_67), k4_waybel_1(A_67, B_68), k6_domain_1(u1_struct_0(A_67), B_68))=k6_waybel_0(A_67, B_68) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_orders_2(A_67) | ~v2_lattice3(A_67) | ~v5_orders_2(A_67) | ~v3_orders_2(A_67))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.40/1.51  tff(c_163, plain, (![B_68]: (k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', B_68), k6_domain_1(u1_struct_0('#skF_2'), B_68))=k6_waybel_0('#skF_2', B_68) | ~m1_subset_1(B_68, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_154])).
% 3.40/1.51  tff(c_173, plain, (![B_68]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k4_waybel_1('#skF_2', B_68), k6_domain_1(k2_struct_0('#skF_2'), B_68))=k6_waybel_0('#skF_2', B_68) | ~m1_subset_1(B_68, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_42, c_65, c_76, c_76, c_76, c_163])).
% 3.40/1.51  tff(c_140, plain, (![A_64, B_65]: (m1_subset_1(k4_waybel_1(A_64, B_65), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64), u1_struct_0(A_64)))) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.40/1.51  tff(c_143, plain, (![B_65]: (m1_subset_1(k4_waybel_1('#skF_2', B_65), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_2')))) | ~m1_subset_1(B_65, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_140])).
% 3.40/1.51  tff(c_148, plain, (![B_65]: (m1_subset_1(k4_waybel_1('#skF_2', B_65), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1(B_65, k2_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_76, c_76, c_143])).
% 3.40/1.51  tff(c_149, plain, (![B_65]: (m1_subset_1(k4_waybel_1('#skF_2', B_65), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1(B_65, k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_148])).
% 3.40/1.51  tff(c_317, plain, (![A_96, B_97, C_98, D_99]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_96), u1_struct_0(B_97), C_98, D_99), A_96) | ~v4_pre_topc(D_99, B_97) | ~m1_subset_1(D_99, k1_zfmisc_1(u1_struct_0(B_97))) | ~v5_pre_topc(C_98, A_96, B_97) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96), u1_struct_0(B_97)))) | ~v1_funct_2(C_98, u1_struct_0(A_96), u1_struct_0(B_97)) | ~v1_funct_1(C_98) | ~l1_pre_topc(B_97) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.51  tff(c_324, plain, (![B_97, C_98, D_99]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_97), C_98, D_99), '#skF_2') | ~v4_pre_topc(D_99, B_97) | ~m1_subset_1(D_99, k1_zfmisc_1(u1_struct_0(B_97))) | ~v5_pre_topc(C_98, '#skF_2', B_97) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_97)))) | ~v1_funct_2(C_98, u1_struct_0('#skF_2'), u1_struct_0(B_97)) | ~v1_funct_1(C_98) | ~l1_pre_topc(B_97) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_317])).
% 3.40/1.51  tff(c_341, plain, (![B_104, C_105, D_106]: (v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_104), C_105, D_106), '#skF_2') | ~v4_pre_topc(D_106, B_104) | ~m1_subset_1(D_106, k1_zfmisc_1(u1_struct_0(B_104))) | ~v5_pre_topc(C_105, '#skF_2', B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, k2_struct_0('#skF_2'), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_pre_topc(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_76, c_76, c_324])).
% 3.40/1.51  tff(c_346, plain, (![C_105, D_106]: (v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'), C_105, D_106), '#skF_2') | ~v4_pre_topc(D_106, '#skF_2') | ~m1_subset_1(D_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v5_pre_topc(C_105, '#skF_2', '#skF_2') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_105, k2_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_105) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_341])).
% 3.40/1.51  tff(c_350, plain, (![C_107, D_108]: (v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_107, D_108), '#skF_2') | ~v4_pre_topc(D_108, '#skF_2') | ~m1_subset_1(D_108, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(C_107, '#skF_2', '#skF_2') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_107, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_76, c_76, c_76, c_346])).
% 3.40/1.51  tff(c_367, plain, (![B_112, D_113]: (v4_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k4_waybel_1('#skF_2', B_112), D_113), '#skF_2') | ~v4_pre_topc(D_113, '#skF_2') | ~m1_subset_1(D_113, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(k4_waybel_1('#skF_2', B_112), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', B_112), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_112)) | ~m1_subset_1(B_112, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_149, c_350])).
% 3.40/1.51  tff(c_376, plain, (![B_114]: (v4_pre_topc(k6_waybel_0('#skF_2', B_114), '#skF_2') | ~v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_114), '#skF_2') | ~m1_subset_1(k6_domain_1(k2_struct_0('#skF_2'), B_114), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(k4_waybel_1('#skF_2', B_114), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', B_114), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_114)) | ~m1_subset_1(B_114, k2_struct_0('#skF_2')) | ~m1_subset_1(B_114, k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_173, c_367])).
% 3.40/1.51  tff(c_381, plain, (![B_25]: (v4_pre_topc(k6_waybel_0('#skF_2', B_25), '#skF_2') | ~v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_25), '#skF_2') | ~v5_pre_topc(k4_waybel_1('#skF_2', B_25), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', B_25), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_25)) | ~m1_subset_1(B_25, k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_376])).
% 3.40/1.51  tff(c_382, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_381])).
% 3.40/1.51  tff(c_18, plain, (![A_28]: (~v1_xboole_0(k2_struct_0(A_28)) | ~l1_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.51  tff(c_385, plain, (~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_382, c_18])).
% 3.40/1.51  tff(c_388, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_385])).
% 3.40/1.51  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_388])).
% 3.40/1.51  tff(c_414, plain, (![B_118]: (v4_pre_topc(k6_waybel_0('#skF_2', B_118), '#skF_2') | ~v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_118), '#skF_2') | ~v5_pre_topc(k4_waybel_1('#skF_2', B_118), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', B_118), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', B_118)) | ~m1_subset_1(B_118, k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_381])).
% 3.40/1.51  tff(c_419, plain, (![B_119]: (v4_pre_topc(k6_waybel_0('#skF_2', B_119), '#skF_2') | ~v4_pre_topc(k6_domain_1(k2_struct_0('#skF_2'), B_119), '#skF_2') | ~v5_pre_topc(k4_waybel_1('#skF_2', B_119), '#skF_2', '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', B_119)) | ~m1_subset_1(B_119, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_127, c_414])).
% 3.40/1.51  tff(c_425, plain, (![B_120]: (v4_pre_topc(k6_waybel_0('#skF_2', B_120), '#skF_2') | ~v5_pre_topc(k4_waybel_1('#skF_2', B_120), '#skF_2', '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', B_120)) | ~m1_subset_1(B_120, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_138, c_419])).
% 3.40/1.51  tff(c_430, plain, (![C_121]: (v4_pre_topc(k6_waybel_0('#skF_2', C_121), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_121)) | ~m1_subset_1(C_121, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_82, c_425])).
% 3.40/1.51  tff(c_34, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.40/1.51  tff(c_433, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_430, c_34])).
% 3.40/1.51  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_117, c_433])).
% 3.40/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.51  
% 3.40/1.51  Inference rules
% 3.40/1.51  ----------------------
% 3.40/1.51  #Ref     : 0
% 3.40/1.51  #Sup     : 73
% 3.40/1.51  #Fact    : 0
% 3.40/1.51  #Define  : 0
% 3.40/1.51  #Split   : 3
% 3.40/1.51  #Chain   : 0
% 3.40/1.51  #Close   : 0
% 3.40/1.51  
% 3.40/1.51  Ordering : KBO
% 3.40/1.51  
% 3.40/1.51  Simplification rules
% 3.40/1.51  ----------------------
% 3.40/1.51  #Subsume      : 21
% 3.40/1.51  #Demod        : 122
% 3.40/1.51  #Tautology    : 7
% 3.40/1.51  #SimpNegUnit  : 11
% 3.40/1.51  #BackRed      : 1
% 3.40/1.51  
% 3.40/1.51  #Partial instantiations: 0
% 3.40/1.51  #Strategies tried      : 1
% 3.40/1.51  
% 3.40/1.51  Timing (in seconds)
% 3.40/1.51  ----------------------
% 3.40/1.52  Preprocessing        : 0.35
% 3.40/1.52  Parsing              : 0.19
% 3.40/1.52  CNF conversion       : 0.03
% 3.40/1.52  Main loop            : 0.37
% 3.40/1.52  Inferencing          : 0.14
% 3.40/1.52  Reduction            : 0.11
% 3.40/1.52  Demodulation         : 0.08
% 3.40/1.52  BG Simplification    : 0.02
% 3.40/1.52  Subsumption          : 0.06
% 3.40/1.52  Abstraction          : 0.02
% 3.40/1.52  MUC search           : 0.00
% 3.40/1.52  Cooper               : 0.00
% 3.40/1.52  Total                : 0.77
% 3.40/1.52  Index Insertion      : 0.00
% 3.40/1.52  Index Deletion       : 0.00
% 3.40/1.52  Index Matching       : 0.00
% 3.40/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
