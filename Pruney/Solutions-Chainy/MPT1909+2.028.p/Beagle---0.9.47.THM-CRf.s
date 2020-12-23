%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:41 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 536 expanded)
%              Number of leaves         :   38 ( 204 expanded)
%              Depth                    :   14
%              Number of atoms          :  236 (2137 expanded)
%              Number of equality atoms :   32 ( 336 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_102,axiom,(
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

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_65,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_72] :
      ( u1_struct_0(A_72) = k2_struct_0(A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_74,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_20,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_49])).

tff(c_94,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,
    ( k6_domain_1(k2_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_94])).

tff(c_160,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_10,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_164,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_160,c_10])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_164])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_170])).

tff(c_175,plain,(
    k6_domain_1(k2_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_83,plain,(
    ! [B_74,A_75] :
      ( l1_pre_topc(B_74)
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_89,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_69,plain,(
    ! [A_3] :
      ( u1_struct_0(A_3) = k2_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_69])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_106,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_118,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_106])).

tff(c_119,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_122,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_10])).

tff(c_125,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_122])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_128])).

tff(c_133,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_18,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_191,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_74,c_74,c_133,c_93,c_93,c_50])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_75,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_32])).

tff(c_107,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_75])).

tff(c_30,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_26,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_81,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_28])).

tff(c_108,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_81])).

tff(c_176,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k6_domain_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_180,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_12])).

tff(c_184,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_180])).

tff(c_185,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_184])).

tff(c_134,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_109,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_24])).

tff(c_143,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k6_domain_1(A_78,B_79),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_143])).

tff(c_152,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_149])).

tff(c_153,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_152])).

tff(c_38,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_247,plain,(
    ! [A_84,B_85,C_86,E_87] :
      ( k8_relset_1(u1_struct_0(A_84),u1_struct_0(B_85),C_86,E_87) = k2_pre_topc(A_84,E_87)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(E_87,k1_zfmisc_1(u1_struct_0(B_85)))
      | ~ v3_borsuk_1(C_86,A_84,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),u1_struct_0(B_85))))
      | ~ v5_pre_topc(C_86,A_84,B_85)
      | ~ v1_funct_2(C_86,u1_struct_0(A_84),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ m1_pre_topc(B_85,A_84)
      | ~ v4_tex_2(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | ~ v3_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_254,plain,(
    ! [B_85,C_86,E_87] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_85),C_86,E_87) = k2_pre_topc('#skF_1',E_87)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(E_87,k1_zfmisc_1(u1_struct_0(B_85)))
      | ~ v3_borsuk_1(C_86,'#skF_1',B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_85))))
      | ~ v5_pre_topc(C_86,'#skF_1',B_85)
      | ~ v1_funct_2(C_86,u1_struct_0('#skF_1'),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ v4_tex_2(B_85,'#skF_1')
      | v2_struct_0(B_85)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_247])).

tff(c_260,plain,(
    ! [B_85,C_86,E_87] :
      ( k8_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_85),C_86,E_87) = k2_pre_topc('#skF_1',E_87)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(E_87,k1_zfmisc_1(u1_struct_0(B_85)))
      | ~ v3_borsuk_1(C_86,'#skF_1',B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_85))))
      | ~ v5_pre_topc(C_86,'#skF_1',B_85)
      | ~ v1_funct_2(C_86,k2_struct_0('#skF_1'),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ v4_tex_2(B_85,'#skF_1')
      | v2_struct_0(B_85)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_74,c_74,c_74,c_254])).

tff(c_352,plain,(
    ! [B_92,C_93,E_94] :
      ( k8_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_92),C_93,E_94) = k2_pre_topc('#skF_1',E_94)
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(E_94,k1_zfmisc_1(u1_struct_0(B_92)))
      | ~ v3_borsuk_1(C_93,'#skF_1',B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_92))))
      | ~ v5_pre_topc(C_93,'#skF_1',B_92)
      | ~ v1_funct_2(C_93,k2_struct_0('#skF_1'),u1_struct_0(B_92))
      | ~ v1_funct_1(C_93)
      | ~ m1_pre_topc(B_92,'#skF_1')
      | ~ v4_tex_2(B_92,'#skF_1')
      | v2_struct_0(B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_260])).

tff(c_357,plain,(
    ! [C_93,E_94] :
      ( k8_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_93,E_94) = k2_pre_topc('#skF_1',E_94)
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_borsuk_1(C_93,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(C_93,'#skF_1','#skF_2')
      | ~ v1_funct_2(C_93,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_352])).

tff(c_362,plain,(
    ! [C_93,E_94] :
      ( k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_93,E_94) = k2_pre_topc('#skF_1',E_94)
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_borsuk_1(C_93,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v5_pre_topc(C_93,'#skF_1','#skF_2')
      | ~ v1_funct_2(C_93,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_93,c_93,c_93,c_357])).

tff(c_392,plain,(
    ! [C_97,E_98] :
      ( k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_97,E_98) = k2_pre_topc('#skF_1',E_98)
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_borsuk_1(C_97,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v5_pre_topc(C_97,'#skF_1','#skF_2')
      | ~ v1_funct_2(C_97,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_362])).

tff(c_394,plain,(
    ! [C_97] :
      ( k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_97,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v3_borsuk_1(C_97,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v5_pre_topc(C_97,'#skF_1','#skF_2')
      | ~ v1_funct_2(C_97,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_153,c_392])).

tff(c_404,plain,(
    ! [C_99] :
      ( k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_99,k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
      | ~ v3_borsuk_1(C_99,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v5_pre_topc(C_99,'#skF_1','#skF_2')
      | ~ v1_funct_2(C_99,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_394])).

tff(c_411,plain,
    ( k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4'))
    | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_404])).

tff(c_415,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) = k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_107,c_30,c_26,c_411])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.39  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.39  
% 2.86/1.39  %Foreground sorts:
% 2.86/1.39  
% 2.86/1.39  
% 2.86/1.39  %Background operators:
% 2.86/1.39  
% 2.86/1.39  
% 2.86/1.39  %Foreground operators:
% 2.86/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.86/1.39  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.86/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.86/1.39  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.86/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.86/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.86/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.86/1.39  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.39  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.86/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.86/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.86/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.86/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.86/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.86/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.39  
% 2.86/1.41  tff(f_141, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 2.86/1.41  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.86/1.41  tff(f_31, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.86/1.41  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.86/1.41  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.86/1.41  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.86/1.41  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.86/1.41  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 2.86/1.41  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.41  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_65, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.41  tff(c_70, plain, (![A_72]: (u1_struct_0(A_72)=k2_struct_0(A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_6, c_65])).
% 2.86/1.41  tff(c_74, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_70])).
% 2.86/1.41  tff(c_20, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_22, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_49, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.86/1.41  tff(c_76, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_49])).
% 2.86/1.41  tff(c_94, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.41  tff(c_104, plain, (k6_domain_1(k2_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_76, c_94])).
% 2.86/1.41  tff(c_160, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_104])).
% 2.86/1.41  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k2_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.41  tff(c_164, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_160, c_10])).
% 2.86/1.41  tff(c_167, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_164])).
% 2.86/1.41  tff(c_170, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_167])).
% 2.86/1.41  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_170])).
% 2.86/1.41  tff(c_175, plain, (k6_domain_1(k2_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_104])).
% 2.86/1.41  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_83, plain, (![B_74, A_75]: (l1_pre_topc(B_74) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.41  tff(c_86, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_83])).
% 2.86/1.41  tff(c_89, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_86])).
% 2.86/1.41  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_69, plain, (![A_3]: (u1_struct_0(A_3)=k2_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(resolution, [status(thm)], [c_6, c_65])).
% 2.86/1.41  tff(c_93, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_89, c_69])).
% 2.86/1.41  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_94])).
% 2.86/1.41  tff(c_118, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_106])).
% 2.86/1.41  tff(c_119, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 2.86/1.41  tff(c_122, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_119, c_10])).
% 2.86/1.41  tff(c_125, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_122])).
% 2.86/1.41  tff(c_128, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_125])).
% 2.86/1.41  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_128])).
% 2.86/1.41  tff(c_133, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_118])).
% 2.86/1.41  tff(c_18, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_50, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 2.86/1.41  tff(c_191, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_74, c_74, c_133, c_93, c_93, c_50])).
% 2.86/1.41  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_32, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_75, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_32])).
% 2.86/1.41  tff(c_107, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_75])).
% 2.86/1.41  tff(c_30, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_26, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_81, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_28])).
% 2.86/1.41  tff(c_108, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_81])).
% 2.86/1.41  tff(c_176, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_104])).
% 2.86/1.41  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(k6_domain_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.41  tff(c_180, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_12])).
% 2.86/1.41  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_180])).
% 2.86/1.41  tff(c_185, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_176, c_184])).
% 2.86/1.41  tff(c_134, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_118])).
% 2.86/1.41  tff(c_109, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_24])).
% 2.86/1.41  tff(c_143, plain, (![A_78, B_79]: (m1_subset_1(k6_domain_1(A_78, B_79), k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.41  tff(c_149, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_143])).
% 2.86/1.41  tff(c_152, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_149])).
% 2.86/1.41  tff(c_153, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_134, c_152])).
% 2.86/1.41  tff(c_38, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_44, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.86/1.41  tff(c_247, plain, (![A_84, B_85, C_86, E_87]: (k8_relset_1(u1_struct_0(A_84), u1_struct_0(B_85), C_86, E_87)=k2_pre_topc(A_84, E_87) | ~m1_subset_1(E_87, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(E_87, k1_zfmisc_1(u1_struct_0(B_85))) | ~v3_borsuk_1(C_86, A_84, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), u1_struct_0(B_85)))) | ~v5_pre_topc(C_86, A_84, B_85) | ~v1_funct_2(C_86, u1_struct_0(A_84), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~m1_pre_topc(B_85, A_84) | ~v4_tex_2(B_85, A_84) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | ~v3_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.86/1.41  tff(c_254, plain, (![B_85, C_86, E_87]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_85), C_86, E_87)=k2_pre_topc('#skF_1', E_87) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(E_87, k1_zfmisc_1(u1_struct_0(B_85))) | ~v3_borsuk_1(C_86, '#skF_1', B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_85)))) | ~v5_pre_topc(C_86, '#skF_1', B_85) | ~v1_funct_2(C_86, u1_struct_0('#skF_1'), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~m1_pre_topc(B_85, '#skF_1') | ~v4_tex_2(B_85, '#skF_1') | v2_struct_0(B_85) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_247])).
% 2.86/1.41  tff(c_260, plain, (![B_85, C_86, E_87]: (k8_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_85), C_86, E_87)=k2_pre_topc('#skF_1', E_87) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(E_87, k1_zfmisc_1(u1_struct_0(B_85))) | ~v3_borsuk_1(C_86, '#skF_1', B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_85)))) | ~v5_pre_topc(C_86, '#skF_1', B_85) | ~v1_funct_2(C_86, k2_struct_0('#skF_1'), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~m1_pre_topc(B_85, '#skF_1') | ~v4_tex_2(B_85, '#skF_1') | v2_struct_0(B_85) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_74, c_74, c_74, c_254])).
% 2.86/1.41  tff(c_352, plain, (![B_92, C_93, E_94]: (k8_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_92), C_93, E_94)=k2_pre_topc('#skF_1', E_94) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(E_94, k1_zfmisc_1(u1_struct_0(B_92))) | ~v3_borsuk_1(C_93, '#skF_1', B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_92)))) | ~v5_pre_topc(C_93, '#skF_1', B_92) | ~v1_funct_2(C_93, k2_struct_0('#skF_1'), u1_struct_0(B_92)) | ~v1_funct_1(C_93) | ~m1_pre_topc(B_92, '#skF_1') | ~v4_tex_2(B_92, '#skF_1') | v2_struct_0(B_92))), inference(negUnitSimplification, [status(thm)], [c_48, c_260])).
% 2.86/1.41  tff(c_357, plain, (![C_93, E_94]: (k8_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_93, E_94)=k2_pre_topc('#skF_1', E_94) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_borsuk_1(C_93, '#skF_1', '#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(C_93, '#skF_1', '#skF_2') | ~v1_funct_2(C_93, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_352])).
% 2.86/1.41  tff(c_362, plain, (![C_93, E_94]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_93, E_94)=k2_pre_topc('#skF_1', E_94) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_borsuk_1(C_93, '#skF_1', '#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v5_pre_topc(C_93, '#skF_1', '#skF_2') | ~v1_funct_2(C_93, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_93) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_93, c_93, c_93, c_357])).
% 2.86/1.41  tff(c_392, plain, (![C_97, E_98]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_97, E_98)=k2_pre_topc('#skF_1', E_98) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_borsuk_1(C_97, '#skF_1', '#skF_2') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v5_pre_topc(C_97, '#skF_1', '#skF_2') | ~v1_funct_2(C_97, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_97))), inference(negUnitSimplification, [status(thm)], [c_40, c_362])).
% 2.86/1.41  tff(c_394, plain, (![C_97]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_97, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v3_borsuk_1(C_97, '#skF_1', '#skF_2') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v5_pre_topc(C_97, '#skF_1', '#skF_2') | ~v1_funct_2(C_97, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_97))), inference(resolution, [status(thm)], [c_153, c_392])).
% 2.86/1.41  tff(c_404, plain, (![C_99]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_99, k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~v3_borsuk_1(C_99, '#skF_1', '#skF_2') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v5_pre_topc(C_99, '#skF_1', '#skF_2') | ~v1_funct_2(C_99, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_394])).
% 2.86/1.41  tff(c_411, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4')) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_404])).
% 2.86/1.41  tff(c_415, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_107, c_30, c_26, c_411])).
% 2.86/1.41  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_415])).
% 2.86/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  Inference rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Ref     : 0
% 2.86/1.41  #Sup     : 81
% 2.86/1.41  #Fact    : 0
% 2.86/1.41  #Define  : 0
% 2.86/1.41  #Split   : 5
% 2.86/1.41  #Chain   : 0
% 2.86/1.41  #Close   : 0
% 2.86/1.41  
% 2.86/1.41  Ordering : KBO
% 2.86/1.41  
% 2.86/1.41  Simplification rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Subsume      : 1
% 2.86/1.41  #Demod        : 101
% 2.86/1.41  #Tautology    : 30
% 2.86/1.41  #SimpNegUnit  : 21
% 2.86/1.41  #BackRed      : 5
% 2.86/1.41  
% 2.86/1.41  #Partial instantiations: 0
% 2.86/1.41  #Strategies tried      : 1
% 2.86/1.41  
% 2.86/1.41  Timing (in seconds)
% 2.86/1.41  ----------------------
% 2.86/1.42  Preprocessing        : 0.33
% 2.86/1.42  Parsing              : 0.17
% 2.86/1.42  CNF conversion       : 0.03
% 2.86/1.42  Main loop            : 0.30
% 2.86/1.42  Inferencing          : 0.10
% 2.86/1.42  Reduction            : 0.10
% 2.86/1.42  Demodulation         : 0.07
% 2.86/1.42  BG Simplification    : 0.02
% 2.86/1.42  Subsumption          : 0.05
% 2.86/1.42  Abstraction          : 0.02
% 2.86/1.42  MUC search           : 0.00
% 2.86/1.42  Cooper               : 0.00
% 2.86/1.42  Total                : 0.67
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
