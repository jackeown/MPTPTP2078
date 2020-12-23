%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 220 expanded)
%              Number of leaves         :   35 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 (1080 expanded)
%              Number of equality atoms :   27 (  89 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E),u1_struct_0(C))
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_50,plain,(
    ! [B_67,A_68] :
      ( l1_pre_topc(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_53])).

tff(c_10,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_108,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( v1_funct_1(k2_tmap_1(A_85,B_86,C_87,D_88))
      | ~ l1_struct_0(D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85),u1_struct_0(B_86))))
      | ~ v1_funct_2(C_87,u1_struct_0(A_85),u1_struct_0(B_86))
      | ~ v1_funct_1(C_87)
      | ~ l1_struct_0(B_86)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_110,plain,(
    ! [D_88] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_88))
      | ~ l1_struct_0(D_88)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_113,plain,(
    ! [D_88] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_88))
      | ~ l1_struct_0(D_88)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_110])).

tff(c_114,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_117,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117])).

tff(c_123,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_122,plain,(
    ! [D_88] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_88))
      | ~ l1_struct_0(D_88) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_124,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_127,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_127])).

tff(c_133,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_144,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( m1_subset_1(k2_tmap_1(A_95,B_96,C_97,D_98),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_98),u1_struct_0(B_96))))
      | ~ l1_struct_0(D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),u1_struct_0(B_96))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_95),u1_struct_0(B_96))
      | ~ v1_funct_1(C_97)
      | ~ l1_struct_0(B_96)
      | ~ l1_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( k8_relset_1(A_4,B_5,C_6,D_7) = k10_relat_1(C_6,D_7)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_171,plain,(
    ! [C_104,D_108,A_105,D_107,B_106] :
      ( k8_relset_1(u1_struct_0(D_108),u1_struct_0(B_106),k2_tmap_1(A_105,B_106,C_104,D_108),D_107) = k10_relat_1(k2_tmap_1(A_105,B_106,C_104,D_108),D_107)
      | ~ l1_struct_0(D_108)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_104)
      | ~ l1_struct_0(B_106)
      | ~ l1_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_175,plain,(
    ! [D_108,D_107] :
      ( k8_relset_1(u1_struct_0(D_108),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_108),D_107) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_108),D_107)
      | ~ l1_struct_0(D_108)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_180,plain,(
    ! [D_109,D_110] :
      ( k8_relset_1(u1_struct_0(D_109),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_109),D_110) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_109),D_110)
      | ~ l1_struct_0(D_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_133,c_32,c_30,c_175])).

tff(c_62,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k8_relset_1(A_72,B_73,C_74,D_75) = k10_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [D_75] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_75) = k10_relat_1('#skF_4',D_75) ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_22,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_22])).

tff(c_186,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_66])).

tff(c_192,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_205,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_192])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_205])).

tff(c_210,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_77,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k2_partfun1(A_77,B_78,C_79,D_80) = k7_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [D_80] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_80) = k7_relat_1('#skF_4',D_80)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_82,plain,(
    ! [D_80] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_80) = k7_relat_1('#skF_4',D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_212,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k2_partfun1(u1_struct_0(A_115),u1_struct_0(B_116),C_117,u1_struct_0(D_118)) = k2_tmap_1(A_115,B_116,C_117,D_118)
      | ~ m1_pre_topc(D_118,A_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_115),u1_struct_0(B_116))))
      | ~ v1_funct_2(C_117,u1_struct_0(A_115),u1_struct_0(B_116))
      | ~ v1_funct_1(C_117)
      | ~ l1_pre_topc(B_116)
      | ~ v2_pre_topc(B_116)
      | v2_struct_0(B_116)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_216,plain,(
    ! [D_118] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_118)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_118)
      | ~ m1_pre_topc(D_118,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_212])).

tff(c_220,plain,(
    ! [D_118] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_118)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_118)
      | ~ m1_pre_topc(D_118,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_32,c_30,c_82,c_216])).

tff(c_222,plain,(
    ! [D_119] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_119)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_119)
      | ~ m1_pre_topc(D_119,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_220])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_24,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_67,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_24])).

tff(c_92,plain,(
    ! [A_82,B_83,C_84] :
      ( k10_relat_1(k7_relat_1(A_82,B_83),C_84) = k10_relat_1(A_82,C_84)
      | ~ r1_tarski(k10_relat_1(A_82,C_84),B_83)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_67,c_92])).

tff(c_98,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_32,c_95])).

tff(c_231,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_98])).

tff(c_239,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_231])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.35  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.46/1.35  
% 2.46/1.35  %Foreground sorts:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Background operators:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Foreground operators:
% 2.46/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.46/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.46/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.46/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.46/1.35  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.46/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.46/1.35  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.46/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.35  
% 2.46/1.37  tff(f_140, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tmap_1)).
% 2.46/1.37  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.46/1.37  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.46/1.37  tff(f_104, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 2.46/1.37  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.46/1.37  tff(f_39, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.46/1.37  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.46/1.37  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.37  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.46/1.37  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_50, plain, (![B_67, A_68]: (l1_pre_topc(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.46/1.37  tff(c_53, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.46/1.37  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_53])).
% 2.46/1.37  tff(c_10, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.37  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_30, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_108, plain, (![A_85, B_86, C_87, D_88]: (v1_funct_1(k2_tmap_1(A_85, B_86, C_87, D_88)) | ~l1_struct_0(D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85), u1_struct_0(B_86)))) | ~v1_funct_2(C_87, u1_struct_0(A_85), u1_struct_0(B_86)) | ~v1_funct_1(C_87) | ~l1_struct_0(B_86) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.46/1.37  tff(c_110, plain, (![D_88]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_88)) | ~l1_struct_0(D_88) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_108])).
% 2.46/1.37  tff(c_113, plain, (![D_88]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_88)) | ~l1_struct_0(D_88) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_110])).
% 2.46/1.37  tff(c_114, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_113])).
% 2.46/1.37  tff(c_117, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_114])).
% 2.46/1.37  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_117])).
% 2.46/1.37  tff(c_123, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_113])).
% 2.46/1.37  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_122, plain, (![D_88]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_88)) | ~l1_struct_0(D_88))), inference(splitRight, [status(thm)], [c_113])).
% 2.46/1.37  tff(c_124, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_122])).
% 2.46/1.37  tff(c_127, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_124])).
% 2.46/1.37  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_127])).
% 2.46/1.37  tff(c_133, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_122])).
% 2.46/1.37  tff(c_144, plain, (![A_95, B_96, C_97, D_98]: (m1_subset_1(k2_tmap_1(A_95, B_96, C_97, D_98), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_98), u1_struct_0(B_96)))) | ~l1_struct_0(D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), u1_struct_0(B_96)))) | ~v1_funct_2(C_97, u1_struct_0(A_95), u1_struct_0(B_96)) | ~v1_funct_1(C_97) | ~l1_struct_0(B_96) | ~l1_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.46/1.37  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k8_relset_1(A_4, B_5, C_6, D_7)=k10_relat_1(C_6, D_7) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.37  tff(c_171, plain, (![C_104, D_108, A_105, D_107, B_106]: (k8_relset_1(u1_struct_0(D_108), u1_struct_0(B_106), k2_tmap_1(A_105, B_106, C_104, D_108), D_107)=k10_relat_1(k2_tmap_1(A_105, B_106, C_104, D_108), D_107) | ~l1_struct_0(D_108) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), u1_struct_0(B_106)))) | ~v1_funct_2(C_104, u1_struct_0(A_105), u1_struct_0(B_106)) | ~v1_funct_1(C_104) | ~l1_struct_0(B_106) | ~l1_struct_0(A_105))), inference(resolution, [status(thm)], [c_144, c_4])).
% 2.46/1.37  tff(c_175, plain, (![D_108, D_107]: (k8_relset_1(u1_struct_0(D_108), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_108), D_107)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_108), D_107) | ~l1_struct_0(D_108) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_171])).
% 2.46/1.37  tff(c_180, plain, (![D_109, D_110]: (k8_relset_1(u1_struct_0(D_109), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_109), D_110)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_109), D_110) | ~l1_struct_0(D_109))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_133, c_32, c_30, c_175])).
% 2.46/1.37  tff(c_62, plain, (![A_72, B_73, C_74, D_75]: (k8_relset_1(A_72, B_73, C_74, D_75)=k10_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.37  tff(c_65, plain, (![D_75]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_75)=k10_relat_1('#skF_4', D_75))), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.46/1.37  tff(c_22, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_66, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_22])).
% 2.46/1.37  tff(c_186, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_66])).
% 2.46/1.37  tff(c_192, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_186])).
% 2.46/1.37  tff(c_205, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_192])).
% 2.46/1.37  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_205])).
% 2.46/1.37  tff(c_210, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_186])).
% 2.46/1.37  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_77, plain, (![A_77, B_78, C_79, D_80]: (k2_partfun1(A_77, B_78, C_79, D_80)=k7_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.37  tff(c_79, plain, (![D_80]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_80)=k7_relat_1('#skF_4', D_80) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_77])).
% 2.46/1.37  tff(c_82, plain, (![D_80]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_80)=k7_relat_1('#skF_4', D_80))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_79])).
% 2.46/1.37  tff(c_212, plain, (![A_115, B_116, C_117, D_118]: (k2_partfun1(u1_struct_0(A_115), u1_struct_0(B_116), C_117, u1_struct_0(D_118))=k2_tmap_1(A_115, B_116, C_117, D_118) | ~m1_pre_topc(D_118, A_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_115), u1_struct_0(B_116)))) | ~v1_funct_2(C_117, u1_struct_0(A_115), u1_struct_0(B_116)) | ~v1_funct_1(C_117) | ~l1_pre_topc(B_116) | ~v2_pre_topc(B_116) | v2_struct_0(B_116) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.46/1.37  tff(c_216, plain, (![D_118]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_118))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_118) | ~m1_pre_topc(D_118, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_212])).
% 2.46/1.37  tff(c_220, plain, (![D_118]: (k7_relat_1('#skF_4', u1_struct_0(D_118))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_118) | ~m1_pre_topc(D_118, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_32, c_30, c_82, c_216])).
% 2.46/1.37  tff(c_222, plain, (![D_119]: (k7_relat_1('#skF_4', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_119) | ~m1_pre_topc(D_119, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_220])).
% 2.46/1.37  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.37  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_2])).
% 2.46/1.37  tff(c_24, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.46/1.37  tff(c_67, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_24])).
% 2.46/1.37  tff(c_92, plain, (![A_82, B_83, C_84]: (k10_relat_1(k7_relat_1(A_82, B_83), C_84)=k10_relat_1(A_82, C_84) | ~r1_tarski(k10_relat_1(A_82, C_84), B_83) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.37  tff(c_95, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_67, c_92])).
% 2.46/1.37  tff(c_98, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_32, c_95])).
% 2.46/1.37  tff(c_231, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_222, c_98])).
% 2.46/1.37  tff(c_239, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_231])).
% 2.46/1.37  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_239])).
% 2.46/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.37  
% 2.46/1.37  Inference rules
% 2.46/1.37  ----------------------
% 2.46/1.37  #Ref     : 0
% 2.46/1.37  #Sup     : 37
% 2.46/1.37  #Fact    : 0
% 2.46/1.37  #Define  : 0
% 2.46/1.37  #Split   : 4
% 2.46/1.37  #Chain   : 0
% 2.46/1.37  #Close   : 0
% 2.46/1.37  
% 2.46/1.37  Ordering : KBO
% 2.46/1.37  
% 2.46/1.37  Simplification rules
% 2.46/1.37  ----------------------
% 2.46/1.37  #Subsume      : 0
% 2.46/1.37  #Demod        : 40
% 2.46/1.37  #Tautology    : 9
% 2.46/1.37  #SimpNegUnit  : 3
% 2.46/1.37  #BackRed      : 2
% 2.46/1.37  
% 2.46/1.37  #Partial instantiations: 0
% 2.46/1.37  #Strategies tried      : 1
% 2.46/1.37  
% 2.46/1.37  Timing (in seconds)
% 2.46/1.37  ----------------------
% 2.72/1.37  Preprocessing        : 0.35
% 2.72/1.37  Parsing              : 0.19
% 2.72/1.37  CNF conversion       : 0.03
% 2.72/1.37  Main loop            : 0.22
% 2.72/1.37  Inferencing          : 0.08
% 2.72/1.37  Reduction            : 0.07
% 2.72/1.37  Demodulation         : 0.05
% 2.72/1.37  BG Simplification    : 0.02
% 2.72/1.37  Subsumption          : 0.04
% 2.72/1.37  Abstraction          : 0.02
% 2.72/1.37  MUC search           : 0.00
% 2.72/1.37  Cooper               : 0.00
% 2.72/1.37  Total                : 0.61
% 2.72/1.37  Index Insertion      : 0.00
% 2.72/1.37  Index Deletion       : 0.00
% 2.72/1.37  Index Matching       : 0.00
% 2.72/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
