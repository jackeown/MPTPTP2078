%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 184 expanded)
%              Number of leaves         :   40 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 ( 874 expanded)
%              Number of equality atoms :   22 ( 119 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_46,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_28,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_57,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_74,plain,(
    ! [A_84,B_85] :
      ( k6_domain_1(A_84,B_85) = k1_tarski(B_85)
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_57,c_74])).

tff(c_107,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( m1_subset_1(u1_struct_0(B_10),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_210,plain,(
    ! [B_104,A_105] :
      ( v3_tex_2(u1_struct_0(B_104),A_105)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v4_tex_2(B_104,A_105)
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_215,plain,(
    ! [B_106,A_107] :
      ( v3_tex_2(u1_struct_0(B_106),A_107)
      | ~ v4_tex_2(B_106,A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_12,c_210])).

tff(c_142,plain,(
    ! [B_94,A_95] :
      ( ~ v3_tex_2(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v1_xboole_0(B_94)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_153,plain,(
    ! [B_10,A_8] :
      ( ~ v3_tex_2(u1_struct_0(B_10),A_8)
      | ~ v1_xboole_0(u1_struct_0(B_10))
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_220,plain,(
    ! [B_108,A_109] :
      ( ~ v1_xboole_0(u1_struct_0(B_108))
      | ~ v2_pre_topc(A_109)
      | ~ v4_tex_2(B_108,A_109)
      | v2_struct_0(A_109)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_215,c_153])).

tff(c_224,plain,(
    ! [A_110] :
      ( ~ v2_pre_topc(A_110)
      | ~ v4_tex_2('#skF_3',A_110)
      | v2_struct_0(A_110)
      | ~ m1_pre_topc('#skF_3',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_107,c_220])).

tff(c_231,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_224])).

tff(c_235,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_54,c_231])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_235])).

tff(c_238,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_85,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_87,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_6,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_6])).

tff(c_93,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_90])).

tff(c_96,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_96])).

tff(c_101,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_240,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_58])).

tff(c_241,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_240])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_38,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_239,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_246,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k6_domain_1(A_111,B_112),k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,A_111)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_252,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_246])).

tff(c_258,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_252])).

tff(c_259,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_258])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_102,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_255,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_246])).

tff(c_261,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_255])).

tff(c_262,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_261])).

tff(c_370,plain,(
    ! [A_133,B_134,C_135,E_136] :
      ( k8_relset_1(u1_struct_0(A_133),u1_struct_0(B_134),C_135,E_136) = k2_pre_topc(A_133,E_136)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(u1_struct_0(B_134)))
      | ~ v3_borsuk_1(C_135,A_133,B_134)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_133),u1_struct_0(B_134))))
      | ~ v5_pre_topc(C_135,A_133,B_134)
      | ~ v1_funct_2(C_135,u1_struct_0(A_133),u1_struct_0(B_134))
      | ~ v1_funct_1(C_135)
      | ~ m1_pre_topc(B_134,A_133)
      | ~ v4_tex_2(B_134,A_133)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_133)
      | ~ v3_tdlat_3(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_376,plain,(
    ! [B_134,C_135] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_134),C_135,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_134)))
      | ~ v3_borsuk_1(C_135,'#skF_2',B_134)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_134))))
      | ~ v5_pre_topc(C_135,'#skF_2',B_134)
      | ~ v1_funct_2(C_135,u1_struct_0('#skF_2'),u1_struct_0(B_134))
      | ~ v1_funct_1(C_135)
      | ~ m1_pre_topc(B_134,'#skF_2')
      | ~ v4_tex_2(B_134,'#skF_2')
      | v2_struct_0(B_134)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_262,c_370])).

tff(c_386,plain,(
    ! [B_134,C_135] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_134),C_135,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_134)))
      | ~ v3_borsuk_1(C_135,'#skF_2',B_134)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_134))))
      | ~ v5_pre_topc(C_135,'#skF_2',B_134)
      | ~ v1_funct_2(C_135,u1_struct_0('#skF_2'),u1_struct_0(B_134))
      | ~ v1_funct_1(C_135)
      | ~ m1_pre_topc(B_134,'#skF_2')
      | ~ v4_tex_2(B_134,'#skF_2')
      | v2_struct_0(B_134)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_376])).

tff(c_421,plain,(
    ! [B_143,C_144] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_143),C_144,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_143)))
      | ~ v3_borsuk_1(C_144,'#skF_2',B_143)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_143))))
      | ~ v5_pre_topc(C_144,'#skF_2',B_143)
      | ~ v1_funct_2(C_144,u1_struct_0('#skF_2'),u1_struct_0(B_143))
      | ~ v1_funct_1(C_144)
      | ~ m1_pre_topc(B_143,'#skF_2')
      | ~ v4_tex_2(B_143,'#skF_2')
      | v2_struct_0(B_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_386])).

tff(c_428,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_421])).

tff(c_432,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_34,c_259,c_428])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_241,c_432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.40  
% 2.91/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.41  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.41  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.91/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.91/1.41  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.91/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.91/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.91/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.41  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.91/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.91/1.41  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.91/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.91/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.91/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.91/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.41  
% 2.91/1.42  tff(f_169, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 2.91/1.42  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.91/1.42  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.91/1.42  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 2.91/1.42  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 2.91/1.42  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.91/1.42  tff(f_39, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.91/1.42  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.91/1.42  tff(f_130, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 2.91/1.42  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_46, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_28, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_57, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.91/1.42  tff(c_74, plain, (![A_84, B_85]: (k6_domain_1(A_84, B_85)=k1_tarski(B_85) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.91/1.42  tff(c_86, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_57, c_74])).
% 2.91/1.42  tff(c_107, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_86])).
% 2.91/1.42  tff(c_12, plain, (![B_10, A_8]: (m1_subset_1(u1_struct_0(B_10), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.91/1.42  tff(c_210, plain, (![B_104, A_105]: (v3_tex_2(u1_struct_0(B_104), A_105) | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(u1_struct_0(A_105))) | ~v4_tex_2(B_104, A_105) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.91/1.42  tff(c_215, plain, (![B_106, A_107]: (v3_tex_2(u1_struct_0(B_106), A_107) | ~v4_tex_2(B_106, A_107) | v2_struct_0(A_107) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_12, c_210])).
% 2.91/1.42  tff(c_142, plain, (![B_94, A_95]: (~v3_tex_2(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~v1_xboole_0(B_94) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.91/1.42  tff(c_153, plain, (![B_10, A_8]: (~v3_tex_2(u1_struct_0(B_10), A_8) | ~v1_xboole_0(u1_struct_0(B_10)) | ~v2_pre_topc(A_8) | v2_struct_0(A_8) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_12, c_142])).
% 2.91/1.42  tff(c_220, plain, (![B_108, A_109]: (~v1_xboole_0(u1_struct_0(B_108)) | ~v2_pre_topc(A_109) | ~v4_tex_2(B_108, A_109) | v2_struct_0(A_109) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_215, c_153])).
% 2.91/1.42  tff(c_224, plain, (![A_110]: (~v2_pre_topc(A_110) | ~v4_tex_2('#skF_3', A_110) | v2_struct_0(A_110) | ~m1_pre_topc('#skF_3', A_110) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_107, c_220])).
% 2.91/1.42  tff(c_231, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_224])).
% 2.91/1.42  tff(c_235, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_54, c_231])).
% 2.91/1.42  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_235])).
% 2.91/1.42  tff(c_238, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 2.91/1.42  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.42  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_85, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.91/1.42  tff(c_87, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.91/1.42  tff(c_6, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.42  tff(c_90, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_87, c_6])).
% 2.91/1.42  tff(c_93, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_90])).
% 2.91/1.42  tff(c_96, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_93])).
% 2.91/1.42  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_96])).
% 2.91/1.42  tff(c_101, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_85])).
% 2.91/1.42  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.91/1.42  tff(c_240, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_58])).
% 2.91/1.42  tff(c_241, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_240])).
% 2.91/1.42  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_38, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_34, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_239, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_86])).
% 2.91/1.42  tff(c_246, plain, (![A_111, B_112]: (m1_subset_1(k6_domain_1(A_111, B_112), k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, A_111) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.91/1.42  tff(c_252, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_246])).
% 2.91/1.42  tff(c_258, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_252])).
% 2.91/1.42  tff(c_259, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_239, c_258])).
% 2.91/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_52, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.91/1.42  tff(c_102, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_85])).
% 2.91/1.42  tff(c_255, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_246])).
% 2.91/1.42  tff(c_261, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_255])).
% 2.91/1.42  tff(c_262, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_102, c_261])).
% 2.91/1.42  tff(c_370, plain, (![A_133, B_134, C_135, E_136]: (k8_relset_1(u1_struct_0(A_133), u1_struct_0(B_134), C_135, E_136)=k2_pre_topc(A_133, E_136) | ~m1_subset_1(E_136, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(E_136, k1_zfmisc_1(u1_struct_0(B_134))) | ~v3_borsuk_1(C_135, A_133, B_134) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_133), u1_struct_0(B_134)))) | ~v5_pre_topc(C_135, A_133, B_134) | ~v1_funct_2(C_135, u1_struct_0(A_133), u1_struct_0(B_134)) | ~v1_funct_1(C_135) | ~m1_pre_topc(B_134, A_133) | ~v4_tex_2(B_134, A_133) | v2_struct_0(B_134) | ~l1_pre_topc(A_133) | ~v3_tdlat_3(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.91/1.42  tff(c_376, plain, (![B_134, C_135]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_134), C_135, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_134))) | ~v3_borsuk_1(C_135, '#skF_2', B_134) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_134)))) | ~v5_pre_topc(C_135, '#skF_2', B_134) | ~v1_funct_2(C_135, u1_struct_0('#skF_2'), u1_struct_0(B_134)) | ~v1_funct_1(C_135) | ~m1_pre_topc(B_134, '#skF_2') | ~v4_tex_2(B_134, '#skF_2') | v2_struct_0(B_134) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_262, c_370])).
% 2.91/1.42  tff(c_386, plain, (![B_134, C_135]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_134), C_135, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_134))) | ~v3_borsuk_1(C_135, '#skF_2', B_134) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_134)))) | ~v5_pre_topc(C_135, '#skF_2', B_134) | ~v1_funct_2(C_135, u1_struct_0('#skF_2'), u1_struct_0(B_134)) | ~v1_funct_1(C_135) | ~m1_pre_topc(B_134, '#skF_2') | ~v4_tex_2(B_134, '#skF_2') | v2_struct_0(B_134) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_376])).
% 2.91/1.42  tff(c_421, plain, (![B_143, C_144]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_143), C_144, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_143))) | ~v3_borsuk_1(C_144, '#skF_2', B_143) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_143)))) | ~v5_pre_topc(C_144, '#skF_2', B_143) | ~v1_funct_2(C_144, u1_struct_0('#skF_2'), u1_struct_0(B_143)) | ~v1_funct_1(C_144) | ~m1_pre_topc(B_143, '#skF_2') | ~v4_tex_2(B_143, '#skF_2') | v2_struct_0(B_143))), inference(negUnitSimplification, [status(thm)], [c_56, c_386])).
% 2.91/1.42  tff(c_428, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_421])).
% 2.91/1.42  tff(c_432, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_34, c_259, c_428])).
% 2.91/1.42  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_241, c_432])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 77
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 9
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.43  Ordering : KBO
% 2.91/1.43  
% 2.91/1.43  Simplification rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Subsume      : 7
% 2.91/1.43  #Demod        : 41
% 2.91/1.43  #Tautology    : 21
% 2.91/1.43  #SimpNegUnit  : 17
% 2.91/1.43  #BackRed      : 1
% 2.91/1.43  
% 2.91/1.43  #Partial instantiations: 0
% 2.91/1.43  #Strategies tried      : 1
% 2.91/1.43  
% 2.91/1.43  Timing (in seconds)
% 2.91/1.43  ----------------------
% 2.91/1.43  Preprocessing        : 0.35
% 2.91/1.43  Parsing              : 0.19
% 2.91/1.43  CNF conversion       : 0.03
% 2.91/1.43  Main loop            : 0.30
% 2.91/1.43  Inferencing          : 0.11
% 2.91/1.43  Reduction            : 0.09
% 2.91/1.43  Demodulation         : 0.06
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.05
% 2.91/1.43  Abstraction          : 0.01
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.69
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
