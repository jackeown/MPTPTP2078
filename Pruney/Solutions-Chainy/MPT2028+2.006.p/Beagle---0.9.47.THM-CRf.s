%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:19 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 213 expanded)
%              Number of leaves         :   46 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  290 ( 850 expanded)
%              Number of equality atoms :    2 (   2 expanded)
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

tff(f_192,negated_conjecture,(
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

tff(f_138,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( v1_funct_1(k4_waybel_1(A,B))
        & v1_funct_2(k4_waybel_1(A,B),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k4_waybel_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_119,axiom,(
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

tff(f_104,axiom,(
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

tff(f_152,axiom,(
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

tff(f_165,axiom,(
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

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_48,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    ! [A_59] :
      ( l1_orders_2(A_59)
      | ~ l1_waybel_9(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_52,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_80,plain,(
    ! [A_67,B_68] :
      ( v1_funct_1(k4_waybel_1(A_67,B_68))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

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

tff(c_20,plain,(
    ! [A_34] :
      ( ~ v2_struct_0(A_34)
      | ~ v1_lattice3(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_90,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_20])).

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
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_108,plain,(
    ! [A_80,B_81,C_82] :
      ( r3_orders_2(A_80,B_81,B_81)
      | ~ m1_subset_1(C_82,u1_struct_0(A_80))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ l1_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_110,plain,(
    ! [B_81] :
      ( r3_orders_2('#skF_2',B_81,B_81)
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_108])).

tff(c_113,plain,(
    ! [B_81] :
      ( r3_orders_2('#skF_2',B_81,B_81)
      | ~ m1_subset_1(B_81,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72,c_110])).

tff(c_115,plain,(
    ! [B_83] :
      ( r3_orders_2('#skF_2',B_83,B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_113])).

tff(c_118,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_131,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_orders_2(A_96,B_97,C_98)
      | ~ r3_orders_2(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_133,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_131])).

tff(c_136,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72,c_46,c_133])).

tff(c_137,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_136])).

tff(c_120,plain,(
    ! [C_87,A_88,B_89] :
      ( r2_hidden(C_87,k6_waybel_0(A_88,B_89))
      | ~ r1_orders_2(A_88,B_89,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_97,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k6_waybel_0(A_69,B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_69,A_1,B_70] :
      ( ~ v1_xboole_0(u1_struct_0(A_69))
      | ~ r2_hidden(A_1,k6_waybel_0(A_69,B_70))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_124,plain,(
    ! [A_88,B_89,C_87] :
      ( ~ v1_xboole_0(u1_struct_0(A_88))
      | ~ r1_orders_2(A_88,B_89,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_120,c_100])).

tff(c_139,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_137,c_124])).

tff(c_142,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46,c_139])).

tff(c_143,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_142])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_63,plain,(
    ! [A_58] :
      ( l1_pre_topc(A_58)
      | ~ l1_waybel_9(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_67,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_60,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_54,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_50,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_44,plain,(
    ! [C_57] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_57),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_38,plain,(
    ! [A_47,B_49] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_47),B_49),A_47)
      | ~ v8_pre_topc(A_47)
      | ~ m1_subset_1(B_49,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30,plain,(
    ! [A_44,B_45] :
      ( v1_funct_2(k4_waybel_1(A_44,B_45),u1_struct_0(A_44),u1_struct_0(A_44))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k6_domain_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_50,B_52] :
      ( k8_relset_1(u1_struct_0(A_50),u1_struct_0(A_50),k4_waybel_1(A_50,B_52),k6_domain_1(u1_struct_0(A_50),B_52)) = k6_waybel_0(A_50,B_52)
      | ~ m1_subset_1(B_52,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50)
      | ~ v2_lattice3(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v3_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_28,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k4_waybel_1(A_44,B_45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44),u1_struct_0(A_44))))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_188,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_116),u1_struct_0(B_117),C_118,D_119),A_116)
      | ~ v4_pre_topc(D_119,B_117)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ v5_pre_topc(C_118,A_116,B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),u1_struct_0(B_117))))
      | ~ v1_funct_2(C_118,u1_struct_0(A_116),u1_struct_0(B_117))
      | ~ v1_funct_1(C_118)
      | ~ l1_pre_topc(B_117)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,(
    ! [A_127,B_128,D_129] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_127),u1_struct_0(A_127),k4_waybel_1(A_127,B_128),D_129),A_127)
      | ~ v4_pre_topc(D_129,A_127)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v5_pre_topc(k4_waybel_1(A_127,B_128),A_127,A_127)
      | ~ v1_funct_2(k4_waybel_1(A_127,B_128),u1_struct_0(A_127),u1_struct_0(A_127))
      | ~ v1_funct_1(k4_waybel_1(A_127,B_128))
      | ~ l1_pre_topc(A_127)
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_28,c_188])).

tff(c_212,plain,(
    ! [A_133,B_134] :
      ( v4_pre_topc(k6_waybel_0(A_133,B_134),A_133)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_133),B_134),A_133)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_133),B_134),k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ v5_pre_topc(k4_waybel_1(A_133,B_134),A_133,A_133)
      | ~ v1_funct_2(k4_waybel_1(A_133,B_134),u1_struct_0(A_133),u1_struct_0(A_133))
      | ~ v1_funct_1(k4_waybel_1(A_133,B_134))
      | ~ l1_pre_topc(A_133)
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | v2_struct_0(A_133)
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v2_lattice3(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v3_orders_2(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_202])).

tff(c_217,plain,(
    ! [A_135,B_136] :
      ( v4_pre_topc(k6_waybel_0(A_135,B_136),A_135)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_135),B_136),A_135)
      | ~ v5_pre_topc(k4_waybel_1(A_135,B_136),A_135,A_135)
      | ~ v1_funct_2(k4_waybel_1(A_135,B_136),u1_struct_0(A_135),u1_struct_0(A_135))
      | ~ v1_funct_1(k4_waybel_1(A_135,B_136))
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135)
      | ~ l1_orders_2(A_135)
      | ~ v2_lattice3(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | v1_xboole_0(u1_struct_0(A_135)) ) ),
    inference(resolution,[status(thm)],[c_12,c_212])).

tff(c_222,plain,(
    ! [A_137,B_138] :
      ( v4_pre_topc(k6_waybel_0(A_137,B_138),A_137)
      | ~ v4_pre_topc(k6_domain_1(u1_struct_0(A_137),B_138),A_137)
      | ~ v5_pre_topc(k4_waybel_1(A_137,B_138),A_137,A_137)
      | ~ v1_funct_1(k4_waybel_1(A_137,B_138))
      | ~ l1_pre_topc(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | v1_xboole_0(u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_217])).

tff(c_226,plain,(
    ! [A_139,B_140] :
      ( v4_pre_topc(k6_waybel_0(A_139,B_140),A_139)
      | ~ v5_pre_topc(k4_waybel_1(A_139,B_140),A_139,A_139)
      | ~ v1_funct_1(k4_waybel_1(A_139,B_140))
      | ~ v2_lattice3(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v1_xboole_0(u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v8_pre_topc(A_139)
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_38,c_222])).

tff(c_229,plain,(
    ! [C_57] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_57),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_57))
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_226])).

tff(c_232,plain,(
    ! [C_57] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_57),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_57))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_67,c_60,c_72,c_58,c_54,c_50,c_229])).

tff(c_238,plain,(
    ! [C_144] :
      ( v4_pre_topc(k6_waybel_0('#skF_2',C_144),'#skF_2')
      | ~ v1_funct_1(k4_waybel_1('#skF_2',C_144))
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_143,c_232])).

tff(c_42,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_241,plain,
    ( ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_238,c_42])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_95,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:15:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.38  
% 2.83/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.39  %$ v5_pre_topc > v1_funct_2 > r3_orders_2 > r1_orders_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.83/1.39  
% 2.83/1.39  %Foreground sorts:
% 2.83/1.39  
% 2.83/1.39  
% 2.83/1.39  %Background operators:
% 2.83/1.39  
% 2.83/1.39  
% 2.83/1.39  %Foreground operators:
% 2.83/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.39  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.83/1.39  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.83/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.83/1.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.83/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.83/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.83/1.39  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.83/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.83/1.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.83/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.83/1.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.83/1.39  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.39  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 2.83/1.39  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.83/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.39  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.83/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.39  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 2.83/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.39  
% 2.97/1.41  tff(f_192, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_waybel_9)).
% 2.97/1.41  tff(f_138, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 2.97/1.41  tff(f_132, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 2.97/1.41  tff(f_95, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.97/1.41  tff(f_88, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 2.97/1.41  tff(f_75, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.97/1.41  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k6_waybel_0(A, B)) <=> r1_orders_2(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_waybel_0)).
% 2.97/1.41  tff(f_104, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k6_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 2.97/1.41  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.97/1.41  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_pcomps_1)).
% 2.97/1.41  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.97/1.41  tff(f_165, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_waybel_9)).
% 2.97/1.41  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.97/1.41  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_48, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_68, plain, (![A_59]: (l1_orders_2(A_59) | ~l1_waybel_9(A_59))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.97/1.41  tff(c_72, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_48, c_68])).
% 2.97/1.41  tff(c_52, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_80, plain, (![A_67, B_68]: (v1_funct_1(k4_waybel_1(A_67, B_68)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_orders_2(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.97/1.41  tff(c_83, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_80])).
% 2.97/1.41  tff(c_86, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_83])).
% 2.97/1.41  tff(c_87, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_86])).
% 2.97/1.41  tff(c_20, plain, (![A_34]: (~v2_struct_0(A_34) | ~v1_lattice3(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.97/1.41  tff(c_90, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_87, c_20])).
% 2.97/1.41  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_52, c_90])).
% 2.97/1.41  tff(c_95, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_86])).
% 2.97/1.41  tff(c_96, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 2.97/1.41  tff(c_58, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_108, plain, (![A_80, B_81, C_82]: (r3_orders_2(A_80, B_81, B_81) | ~m1_subset_1(C_82, u1_struct_0(A_80)) | ~m1_subset_1(B_81, u1_struct_0(A_80)) | ~l1_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.41  tff(c_110, plain, (![B_81]: (r3_orders_2('#skF_2', B_81, B_81) | ~m1_subset_1(B_81, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_108])).
% 2.97/1.41  tff(c_113, plain, (![B_81]: (r3_orders_2('#skF_2', B_81, B_81) | ~m1_subset_1(B_81, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72, c_110])).
% 2.97/1.41  tff(c_115, plain, (![B_83]: (r3_orders_2('#skF_2', B_83, B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_96, c_113])).
% 2.97/1.41  tff(c_118, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_115])).
% 2.97/1.41  tff(c_131, plain, (![A_96, B_97, C_98]: (r1_orders_2(A_96, B_97, C_98) | ~r3_orders_2(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.41  tff(c_133, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_118, c_131])).
% 2.97/1.41  tff(c_136, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72, c_46, c_133])).
% 2.97/1.41  tff(c_137, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_96, c_136])).
% 2.97/1.41  tff(c_120, plain, (![C_87, A_88, B_89]: (r2_hidden(C_87, k6_waybel_0(A_88, B_89)) | ~r1_orders_2(A_88, B_89, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.97/1.41  tff(c_97, plain, (![A_69, B_70]: (m1_subset_1(k6_waybel_0(A_69, B_70), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.97/1.41  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.41  tff(c_100, plain, (![A_69, A_1, B_70]: (~v1_xboole_0(u1_struct_0(A_69)) | ~r2_hidden(A_1, k6_waybel_0(A_69, B_70)) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.97/1.41  tff(c_124, plain, (![A_88, B_89, C_87]: (~v1_xboole_0(u1_struct_0(A_88)) | ~r1_orders_2(A_88, B_89, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_120, c_100])).
% 2.97/1.41  tff(c_139, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_137, c_124])).
% 2.97/1.41  tff(c_142, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46, c_139])).
% 2.97/1.41  tff(c_143, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_96, c_142])).
% 2.97/1.41  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_63, plain, (![A_58]: (l1_pre_topc(A_58) | ~l1_waybel_9(A_58))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.97/1.41  tff(c_67, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_63])).
% 2.97/1.41  tff(c_60, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_54, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_50, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_44, plain, (![C_57]: (v5_pre_topc(k4_waybel_1('#skF_2', C_57), '#skF_2', '#skF_2') | ~m1_subset_1(C_57, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_38, plain, (![A_47, B_49]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_47), B_49), A_47) | ~v8_pre_topc(A_47) | ~m1_subset_1(B_49, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.97/1.41  tff(c_30, plain, (![A_44, B_45]: (v1_funct_2(k4_waybel_1(A_44, B_45), u1_struct_0(A_44), u1_struct_0(A_44)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.97/1.41  tff(c_12, plain, (![A_26, B_27]: (m1_subset_1(k6_domain_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.41  tff(c_40, plain, (![A_50, B_52]: (k8_relset_1(u1_struct_0(A_50), u1_struct_0(A_50), k4_waybel_1(A_50, B_52), k6_domain_1(u1_struct_0(A_50), B_52))=k6_waybel_0(A_50, B_52) | ~m1_subset_1(B_52, u1_struct_0(A_50)) | ~l1_orders_2(A_50) | ~v2_lattice3(A_50) | ~v5_orders_2(A_50) | ~v3_orders_2(A_50))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.97/1.41  tff(c_28, plain, (![A_44, B_45]: (m1_subset_1(k4_waybel_1(A_44, B_45), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44), u1_struct_0(A_44)))) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.97/1.41  tff(c_188, plain, (![A_116, B_117, C_118, D_119]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_116), u1_struct_0(B_117), C_118, D_119), A_116) | ~v4_pre_topc(D_119, B_117) | ~m1_subset_1(D_119, k1_zfmisc_1(u1_struct_0(B_117))) | ~v5_pre_topc(C_118, A_116, B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(B_117)))) | ~v1_funct_2(C_118, u1_struct_0(A_116), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~l1_pre_topc(B_117) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.41  tff(c_202, plain, (![A_127, B_128, D_129]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_127), u1_struct_0(A_127), k4_waybel_1(A_127, B_128), D_129), A_127) | ~v4_pre_topc(D_129, A_127) | ~m1_subset_1(D_129, k1_zfmisc_1(u1_struct_0(A_127))) | ~v5_pre_topc(k4_waybel_1(A_127, B_128), A_127, A_127) | ~v1_funct_2(k4_waybel_1(A_127, B_128), u1_struct_0(A_127), u1_struct_0(A_127)) | ~v1_funct_1(k4_waybel_1(A_127, B_128)) | ~l1_pre_topc(A_127) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_28, c_188])).
% 2.97/1.41  tff(c_212, plain, (![A_133, B_134]: (v4_pre_topc(k6_waybel_0(A_133, B_134), A_133) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_133), B_134), A_133) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_133), B_134), k1_zfmisc_1(u1_struct_0(A_133))) | ~v5_pre_topc(k4_waybel_1(A_133, B_134), A_133, A_133) | ~v1_funct_2(k4_waybel_1(A_133, B_134), u1_struct_0(A_133), u1_struct_0(A_133)) | ~v1_funct_1(k4_waybel_1(A_133, B_134)) | ~l1_pre_topc(A_133) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | v2_struct_0(A_133) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v2_lattice3(A_133) | ~v5_orders_2(A_133) | ~v3_orders_2(A_133))), inference(superposition, [status(thm), theory('equality')], [c_40, c_202])).
% 2.97/1.41  tff(c_217, plain, (![A_135, B_136]: (v4_pre_topc(k6_waybel_0(A_135, B_136), A_135) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_135), B_136), A_135) | ~v5_pre_topc(k4_waybel_1(A_135, B_136), A_135, A_135) | ~v1_funct_2(k4_waybel_1(A_135, B_136), u1_struct_0(A_135), u1_struct_0(A_135)) | ~v1_funct_1(k4_waybel_1(A_135, B_136)) | ~l1_pre_topc(A_135) | v2_struct_0(A_135) | ~l1_orders_2(A_135) | ~v2_lattice3(A_135) | ~v5_orders_2(A_135) | ~v3_orders_2(A_135) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | v1_xboole_0(u1_struct_0(A_135)))), inference(resolution, [status(thm)], [c_12, c_212])).
% 2.97/1.41  tff(c_222, plain, (![A_137, B_138]: (v4_pre_topc(k6_waybel_0(A_137, B_138), A_137) | ~v4_pre_topc(k6_domain_1(u1_struct_0(A_137), B_138), A_137) | ~v5_pre_topc(k4_waybel_1(A_137, B_138), A_137, A_137) | ~v1_funct_1(k4_waybel_1(A_137, B_138)) | ~l1_pre_topc(A_137) | ~v2_lattice3(A_137) | ~v5_orders_2(A_137) | ~v3_orders_2(A_137) | v1_xboole_0(u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_30, c_217])).
% 2.97/1.41  tff(c_226, plain, (![A_139, B_140]: (v4_pre_topc(k6_waybel_0(A_139, B_140), A_139) | ~v5_pre_topc(k4_waybel_1(A_139, B_140), A_139, A_139) | ~v1_funct_1(k4_waybel_1(A_139, B_140)) | ~v2_lattice3(A_139) | ~v5_orders_2(A_139) | ~v3_orders_2(A_139) | v1_xboole_0(u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v8_pre_topc(A_139) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_38, c_222])).
% 2.97/1.41  tff(c_229, plain, (![C_57]: (v4_pre_topc(k6_waybel_0('#skF_2', C_57), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_57)) | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_57, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_226])).
% 2.97/1.41  tff(c_232, plain, (![C_57]: (v4_pre_topc(k6_waybel_0('#skF_2', C_57), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_57)) | v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_57, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_67, c_60, c_72, c_58, c_54, c_50, c_229])).
% 2.97/1.41  tff(c_238, plain, (![C_144]: (v4_pre_topc(k6_waybel_0('#skF_2', C_144), '#skF_2') | ~v1_funct_1(k4_waybel_1('#skF_2', C_144)) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_96, c_143, c_232])).
% 2.97/1.41  tff(c_42, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.97/1.41  tff(c_241, plain, (~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_238, c_42])).
% 2.97/1.41  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_95, c_241])).
% 2.97/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.41  
% 2.97/1.41  Inference rules
% 2.97/1.41  ----------------------
% 2.97/1.41  #Ref     : 0
% 2.97/1.41  #Sup     : 33
% 2.97/1.41  #Fact    : 0
% 2.97/1.41  #Define  : 0
% 2.97/1.41  #Split   : 1
% 2.97/1.41  #Chain   : 0
% 2.97/1.41  #Close   : 0
% 2.97/1.41  
% 2.97/1.41  Ordering : KBO
% 2.97/1.41  
% 2.97/1.41  Simplification rules
% 2.97/1.41  ----------------------
% 2.97/1.41  #Subsume      : 2
% 2.97/1.41  #Demod        : 23
% 2.97/1.41  #Tautology    : 6
% 2.97/1.41  #SimpNegUnit  : 5
% 2.97/1.41  #BackRed      : 0
% 2.97/1.41  
% 2.97/1.41  #Partial instantiations: 0
% 2.97/1.41  #Strategies tried      : 1
% 2.97/1.41  
% 2.97/1.41  Timing (in seconds)
% 2.97/1.41  ----------------------
% 2.97/1.41  Preprocessing        : 0.35
% 2.97/1.41  Parsing              : 0.19
% 2.97/1.41  CNF conversion       : 0.03
% 2.97/1.41  Main loop            : 0.28
% 2.97/1.41  Inferencing          : 0.12
% 2.97/1.41  Reduction            : 0.08
% 2.97/1.41  Demodulation         : 0.05
% 2.97/1.41  BG Simplification    : 0.02
% 2.97/1.41  Subsumption          : 0.04
% 2.97/1.41  Abstraction          : 0.01
% 2.97/1.41  MUC search           : 0.00
% 2.97/1.41  Cooper               : 0.00
% 2.97/1.41  Total                : 0.67
% 2.97/1.41  Index Insertion      : 0.00
% 2.97/1.41  Index Deletion       : 0.00
% 2.97/1.41  Index Matching       : 0.00
% 2.97/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
