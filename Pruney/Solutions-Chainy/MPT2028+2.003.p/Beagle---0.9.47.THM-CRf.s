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
% DateTime   : Thu Dec  3 10:31:18 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 498 expanded)
%              Number of leaves         :   46 ( 195 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 (2029 expanded)
%              Number of equality atoms :    8 (  42 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_waybel_0 > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

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

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k6_waybel_0(A,B))
        & v2_waybel_0(k6_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_waybel_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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

tff(f_63,axiom,(
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

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_42,plain,(
    ! [C_50] :
      ( v5_pre_topc(k4_waybel_1('#skF_2',C_50),'#skF_2','#skF_2')
      | ~ m1_subset_1(C_50,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_46,plain,(
    l1_waybel_9('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_61,plain,(
    ! [A_51] :
      ( l1_orders_2(A_51)
      | ~ l1_waybel_9(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_65,plain,(
    l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_50,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_94,plain,(
    ! [A_65,B_66] :
      ( v1_funct_1(k4_waybel_1(A_65,B_66))
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_97,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_100,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_97])).

tff(c_101,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_18,plain,(
    ! [A_32] :
      ( ~ v2_struct_0(A_32)
      | ~ v1_lattice3(A_32)
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_111,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_101,c_18])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_111])).

tff(c_117,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_56,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_118,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(k6_waybel_0(A_69,B_70))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_121,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_124,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_65,c_121])).

tff(c_125,plain,(
    ~ v1_xboole_0(k6_waybel_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_124])).

tff(c_84,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_93,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_135,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k6_waybel_0(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [B_5,A_3] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_145,plain,(
    ! [A_77,B_78] :
      ( v1_xboole_0(k6_waybel_0(A_77,B_78))
      | ~ v1_xboole_0(u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_135,c_4])).

tff(c_148,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_145])).

tff(c_151,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_93,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_125,c_151])).

tff(c_155,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_79,B_80] :
      ( v1_funct_1(k4_waybel_1(A_79,B_80))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_159,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_156])).

tff(c_162,plain,
    ( v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_159])).

tff(c_167,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_170,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_167,c_18])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_170])).

tff(c_176,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_28,plain,(
    ! [A_37,B_38] :
      ( v1_funct_2(k4_waybel_1(A_37,B_38),u1_struct_0(A_37),u1_struct_0(A_37))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    ~ v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    ! [A_52] :
      ( l1_pre_topc(A_52)
      | ~ l1_waybel_9(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_175,plain,(
    v1_funct_1(k4_waybel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_154,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_222,plain,(
    ! [A_95,B_96] :
      ( v4_pre_topc(k6_domain_1(u1_struct_0(A_95),B_96),A_95)
      | ~ v8_pre_topc(A_95)
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_225,plain,
    ( v4_pre_topc(k1_tarski('#skF_3'),'#skF_2')
    | ~ v8_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_222])).

tff(c_227,plain,
    ( v4_pre_topc(k1_tarski('#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_70,c_44,c_58,c_225])).

tff(c_228,plain,(
    v4_pre_topc(k1_tarski('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_227])).

tff(c_52,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_48,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_239,plain,(
    ! [A_101,B_102] :
      ( k8_relset_1(u1_struct_0(A_101),u1_struct_0(A_101),k4_waybel_1(A_101,B_102),k6_domain_1(u1_struct_0(A_101),B_102)) = k6_waybel_0(A_101,B_102)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v2_lattice3(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v3_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_248,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_3'),k1_tarski('#skF_3')) = k6_waybel_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_239])).

tff(c_252,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k4_waybel_1('#skF_2','#skF_3'),k1_tarski('#skF_3')) = k6_waybel_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_48,c_65,c_44,c_248])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k4_waybel_1(A_37,B_38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(A_37))))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_299,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_127),u1_struct_0(B_128),C_129,D_130),A_127)
      | ~ v4_pre_topc(D_130,B_128)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(u1_struct_0(B_128)))
      | ~ v5_pre_topc(C_129,A_127,B_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127),u1_struct_0(B_128))))
      | ~ v1_funct_2(C_129,u1_struct_0(A_127),u1_struct_0(B_128))
      | ~ v1_funct_1(C_129)
      | ~ l1_pre_topc(B_128)
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_337,plain,(
    ! [A_144,B_145,D_146] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_144),u1_struct_0(A_144),k4_waybel_1(A_144,B_145),D_146),A_144)
      | ~ v4_pre_topc(D_146,A_144)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v5_pre_topc(k4_waybel_1(A_144,B_145),A_144,A_144)
      | ~ v1_funct_2(k4_waybel_1(A_144,B_145),u1_struct_0(A_144),u1_struct_0(A_144))
      | ~ v1_funct_1(k4_waybel_1(A_144,B_145))
      | ~ l1_pre_topc(A_144)
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_26,c_299])).

tff(c_344,plain,
    ( v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k1_tarski('#skF_3'),'#skF_2')
    | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_waybel_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_337])).

tff(c_350,plain,
    ( v4_pre_topc(k6_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_70,c_175,c_228,c_344])).

tff(c_351,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_40,c_350])).

tff(c_352,plain,(
    ~ v1_funct_2(k4_waybel_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_355,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_352])).

tff(c_358,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_355])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_358])).

tff(c_361,plain,
    ( ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_372,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_376,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_372])).

tff(c_379,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_382,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_379])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_382])).

tff(c_385,plain,(
    ~ v5_pre_topc(k4_waybel_1('#skF_2','#skF_3'),'#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_389,plain,(
    ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_385])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:51:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.53  
% 3.25/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.53  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_waybel_0 > r2_hidden > m1_subset_1 > v8_pre_topc > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_xboole_0 > v1_lattice3 > v1_funct_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k8_relset_1 > k6_waybel_0 > k6_domain_1 > k4_waybel_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 3.25/1.53  
% 3.25/1.53  %Foreground sorts:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Background operators:
% 3.25/1.53  
% 3.25/1.53  
% 3.25/1.53  %Foreground operators:
% 3.25/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.53  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.25/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.25/1.53  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.25/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.25/1.53  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.25/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.25/1.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.25/1.53  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.25/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.53  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.25/1.53  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.25/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.25/1.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.25/1.53  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.53  tff(k6_waybel_0, type, k6_waybel_0: ($i * $i) > $i).
% 3.25/1.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.25/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.25/1.53  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.25/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.53  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 3.25/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.53  
% 3.32/1.55  tff(f_173, negated_conjecture, ~(![A]: ((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, C), A, A))) => v4_pre_topc(k6_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_waybel_9)).
% 3.32/1.55  tff(f_119, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 3.32/1.55  tff(f_113, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => ((v1_funct_1(k4_waybel_1(A, B)) & v1_funct_2(k4_waybel_1(A, B), u1_struct_0(A), u1_struct_0(A))) & m1_subset_1(k4_waybel_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 3.32/1.55  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.32/1.55  tff(f_100, axiom, (![A, B]: ((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(k6_waybel_0(A, B)) & v2_waybel_0(k6_waybel_0(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_waybel_0)).
% 3.32/1.55  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.32/1.55  tff(f_86, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k6_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_waybel_0)).
% 3.32/1.55  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.32/1.55  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.32/1.55  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.32/1.55  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v8_pre_topc(A) => v4_pre_topc(k6_domain_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_pcomps_1)).
% 3.32/1.55  tff(f_146, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(A), k4_waybel_1(A, B), k6_domain_1(u1_struct_0(A), B)) = k6_waybel_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_waybel_9)).
% 3.32/1.55  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 3.32/1.55  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_42, plain, (![C_50]: (v5_pre_topc(k4_waybel_1('#skF_2', C_50), '#skF_2', '#skF_2') | ~m1_subset_1(C_50, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_46, plain, (l1_waybel_9('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_61, plain, (![A_51]: (l1_orders_2(A_51) | ~l1_waybel_9(A_51))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.55  tff(c_65, plain, (l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_46, c_61])).
% 3.32/1.55  tff(c_50, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_94, plain, (![A_65, B_66]: (v1_funct_1(k4_waybel_1(A_65, B_66)) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l1_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.55  tff(c_97, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_94])).
% 3.32/1.55  tff(c_100, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_97])).
% 3.32/1.55  tff(c_101, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_100])).
% 3.32/1.55  tff(c_18, plain, (![A_32]: (~v2_struct_0(A_32) | ~v1_lattice3(A_32) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.55  tff(c_111, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_101, c_18])).
% 3.32/1.55  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_50, c_111])).
% 3.32/1.55  tff(c_117, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_100])).
% 3.32/1.55  tff(c_56, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_118, plain, (![A_69, B_70]: (~v1_xboole_0(k6_waybel_0(A_69, B_70)) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.55  tff(c_121, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_118])).
% 3.32/1.55  tff(c_124, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_65, c_121])).
% 3.32/1.55  tff(c_125, plain, (~v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_117, c_124])).
% 3.32/1.55  tff(c_84, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.32/1.55  tff(c_92, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_84])).
% 3.32/1.55  tff(c_93, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_92])).
% 3.32/1.55  tff(c_135, plain, (![A_73, B_74]: (m1_subset_1(k6_waybel_0(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.55  tff(c_4, plain, (![B_5, A_3]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.32/1.55  tff(c_145, plain, (![A_77, B_78]: (v1_xboole_0(k6_waybel_0(A_77, B_78)) | ~v1_xboole_0(u1_struct_0(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_135, c_4])).
% 3.32/1.55  tff(c_148, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_145])).
% 3.32/1.55  tff(c_151, plain, (v1_xboole_0(k6_waybel_0('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_93, c_148])).
% 3.32/1.55  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_125, c_151])).
% 3.32/1.55  tff(c_155, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_92])).
% 3.32/1.55  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.32/1.55  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.55  tff(c_156, plain, (![A_79, B_80]: (v1_funct_1(k4_waybel_1(A_79, B_80)) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l1_orders_2(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.55  tff(c_159, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_156])).
% 3.32/1.55  tff(c_162, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_159])).
% 3.32/1.55  tff(c_167, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_162])).
% 3.32/1.55  tff(c_170, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_167, c_18])).
% 3.32/1.55  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_50, c_170])).
% 3.32/1.55  tff(c_176, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_162])).
% 3.32/1.55  tff(c_28, plain, (![A_37, B_38]: (v1_funct_2(k4_waybel_1(A_37, B_38), u1_struct_0(A_37), u1_struct_0(A_37)) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.55  tff(c_40, plain, (~v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_66, plain, (![A_52]: (l1_pre_topc(A_52) | ~l1_waybel_9(A_52))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.55  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_66])).
% 3.32/1.55  tff(c_175, plain, (v1_funct_1(k4_waybel_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_162])).
% 3.32/1.55  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_58, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_154, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 3.32/1.55  tff(c_222, plain, (![A_95, B_96]: (v4_pre_topc(k6_domain_1(u1_struct_0(A_95), B_96), A_95) | ~v8_pre_topc(A_95) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.32/1.55  tff(c_225, plain, (v4_pre_topc(k1_tarski('#skF_3'), '#skF_2') | ~v8_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_222])).
% 3.32/1.55  tff(c_227, plain, (v4_pre_topc(k1_tarski('#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_70, c_44, c_58, c_225])).
% 3.32/1.55  tff(c_228, plain, (v4_pre_topc(k1_tarski('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_176, c_227])).
% 3.32/1.55  tff(c_52, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_48, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.32/1.55  tff(c_239, plain, (![A_101, B_102]: (k8_relset_1(u1_struct_0(A_101), u1_struct_0(A_101), k4_waybel_1(A_101, B_102), k6_domain_1(u1_struct_0(A_101), B_102))=k6_waybel_0(A_101, B_102) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v2_lattice3(A_101) | ~v5_orders_2(A_101) | ~v3_orders_2(A_101))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.32/1.55  tff(c_248, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_3'), k1_tarski('#skF_3'))=k6_waybel_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_239])).
% 3.32/1.55  tff(c_252, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), k4_waybel_1('#skF_2', '#skF_3'), k1_tarski('#skF_3'))=k6_waybel_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_48, c_65, c_44, c_248])).
% 3.32/1.55  tff(c_26, plain, (![A_37, B_38]: (m1_subset_1(k4_waybel_1(A_37, B_38), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37), u1_struct_0(A_37)))) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.55  tff(c_299, plain, (![A_127, B_128, C_129, D_130]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_127), u1_struct_0(B_128), C_129, D_130), A_127) | ~v4_pre_topc(D_130, B_128) | ~m1_subset_1(D_130, k1_zfmisc_1(u1_struct_0(B_128))) | ~v5_pre_topc(C_129, A_127, B_128) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127), u1_struct_0(B_128)))) | ~v1_funct_2(C_129, u1_struct_0(A_127), u1_struct_0(B_128)) | ~v1_funct_1(C_129) | ~l1_pre_topc(B_128) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.55  tff(c_337, plain, (![A_144, B_145, D_146]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_144), u1_struct_0(A_144), k4_waybel_1(A_144, B_145), D_146), A_144) | ~v4_pre_topc(D_146, A_144) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_144))) | ~v5_pre_topc(k4_waybel_1(A_144, B_145), A_144, A_144) | ~v1_funct_2(k4_waybel_1(A_144, B_145), u1_struct_0(A_144), u1_struct_0(A_144)) | ~v1_funct_1(k4_waybel_1(A_144, B_145)) | ~l1_pre_topc(A_144) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l1_orders_2(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_26, c_299])).
% 3.32/1.55  tff(c_344, plain, (v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v4_pre_topc(k1_tarski('#skF_3'), '#skF_2') | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_waybel_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_252, c_337])).
% 3.32/1.55  tff(c_350, plain, (v4_pre_topc(k6_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_70, c_175, c_228, c_344])).
% 3.32/1.55  tff(c_351, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k4_waybel_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_176, c_40, c_350])).
% 3.32/1.55  tff(c_352, plain, (~v1_funct_2(k4_waybel_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_351])).
% 3.32/1.55  tff(c_355, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_352])).
% 3.32/1.55  tff(c_358, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_355])).
% 3.32/1.55  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_358])).
% 3.32/1.55  tff(c_361, plain, (~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_351])).
% 3.32/1.55  tff(c_372, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_361])).
% 3.32/1.55  tff(c_376, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_372])).
% 3.32/1.55  tff(c_379, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_376])).
% 3.32/1.55  tff(c_382, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_379])).
% 3.32/1.55  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_382])).
% 3.32/1.55  tff(c_385, plain, (~v5_pre_topc(k4_waybel_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_361])).
% 3.32/1.55  tff(c_389, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_385])).
% 3.32/1.55  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_389])).
% 3.32/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.55  
% 3.32/1.55  Inference rules
% 3.32/1.55  ----------------------
% 3.32/1.55  #Ref     : 0
% 3.32/1.55  #Sup     : 61
% 3.32/1.55  #Fact    : 0
% 3.32/1.55  #Define  : 0
% 3.32/1.55  #Split   : 5
% 3.32/1.55  #Chain   : 0
% 3.32/1.55  #Close   : 0
% 3.32/1.55  
% 3.32/1.55  Ordering : KBO
% 3.32/1.55  
% 3.32/1.55  Simplification rules
% 3.32/1.55  ----------------------
% 3.32/1.55  #Subsume      : 3
% 3.32/1.55  #Demod        : 33
% 3.32/1.55  #Tautology    : 21
% 3.32/1.55  #SimpNegUnit  : 8
% 3.32/1.55  #BackRed      : 0
% 3.32/1.55  
% 3.32/1.55  #Partial instantiations: 0
% 3.32/1.55  #Strategies tried      : 1
% 3.32/1.55  
% 3.32/1.55  Timing (in seconds)
% 3.32/1.55  ----------------------
% 3.32/1.56  Preprocessing        : 0.39
% 3.32/1.56  Parsing              : 0.20
% 3.32/1.56  CNF conversion       : 0.03
% 3.32/1.56  Main loop            : 0.36
% 3.32/1.56  Inferencing          : 0.15
% 3.32/1.56  Reduction            : 0.10
% 3.32/1.56  Demodulation         : 0.07
% 3.32/1.56  BG Simplification    : 0.03
% 3.32/1.56  Subsumption          : 0.05
% 3.32/1.56  Abstraction          : 0.02
% 3.32/1.56  MUC search           : 0.00
% 3.32/1.56  Cooper               : 0.00
% 3.32/1.56  Total                : 0.81
% 3.32/1.56  Index Insertion      : 0.00
% 3.32/1.56  Index Deletion       : 0.00
% 3.32/1.56  Index Matching       : 0.00
% 3.32/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
