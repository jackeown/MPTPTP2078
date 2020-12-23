%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 212 expanded)
%              Number of leaves         :   35 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 (1045 expanded)
%              Number of equality atoms :   27 (  84 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_138,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_102,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_84,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    ! [B_67,A_68] :
      ( l1_pre_topc(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_53])).

tff(c_10,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_100,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( v1_funct_1(k2_tmap_1(A_85,B_86,C_87,D_88))
      | ~ l1_struct_0(D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85),u1_struct_0(B_86))))
      | ~ v1_funct_2(C_87,u1_struct_0(A_85),u1_struct_0(B_86))
      | ~ v1_funct_1(C_87)
      | ~ l1_struct_0(B_86)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_102,plain,(
    ! [D_88] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_88))
      | ~ l1_struct_0(D_88)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_105,plain,(
    ! [D_88] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_88))
      | ~ l1_struct_0(D_88)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_102])).

tff(c_106,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_109,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109])).

tff(c_115,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_114,plain,(
    ! [D_88] :
      ( ~ l1_struct_0('#skF_1')
      | v1_funct_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_88))
      | ~ l1_struct_0(D_88) ) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_119])).

tff(c_125,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_134,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( m1_subset_1(k2_tmap_1(A_95,B_96,C_97,D_98),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_98),u1_struct_0(B_96))))
      | ~ l1_struct_0(D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),u1_struct_0(B_96))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_95),u1_struct_0(B_96))
      | ~ v1_funct_1(C_97)
      | ~ l1_struct_0(B_96)
      | ~ l1_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_161,plain,(
    ! [C_104,D_108,A_105,D_107,B_106] :
      ( k7_relset_1(u1_struct_0(D_108),u1_struct_0(B_106),k2_tmap_1(A_105,B_106,C_104,D_108),D_107) = k9_relat_1(k2_tmap_1(A_105,B_106,C_104,D_108),D_107)
      | ~ l1_struct_0(D_108)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_104)
      | ~ l1_struct_0(B_106)
      | ~ l1_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_134,c_6])).

tff(c_165,plain,(
    ! [D_108,D_107] :
      ( k7_relset_1(u1_struct_0(D_108),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_108),D_107) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_108),D_107)
      | ~ l1_struct_0(D_108)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_161])).

tff(c_170,plain,(
    ! [D_109,D_110] :
      ( k7_relset_1(u1_struct_0(D_109),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_109),D_110) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_109),D_110)
      | ~ l1_struct_0(D_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_125,c_32,c_30,c_165])).

tff(c_71,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_relset_1(A_75,B_76,C_77,D_78) = k9_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [D_78] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_78) = k9_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_22,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_75,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22])).

tff(c_176,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_75])).

tff(c_182,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_185,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_185])).

tff(c_190,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_24,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_85,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    ! [D_83] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_90,plain,(
    ! [D_83] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87])).

tff(c_192,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k2_partfun1(u1_struct_0(A_111),u1_struct_0(B_112),C_113,u1_struct_0(D_114)) = k2_tmap_1(A_111,B_112,C_113,D_114)
      | ~ m1_pre_topc(D_114,A_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_196,plain,(
    ! [D_114] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_114)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_114)
      | ~ m1_pre_topc(D_114,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_192])).

tff(c_200,plain,(
    ! [D_114] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_114)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_114)
      | ~ m1_pre_topc(D_114,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_46,c_44,c_32,c_30,c_90,c_196])).

tff(c_202,plain,(
    ! [D_115] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_115)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_115)
      | ~ m1_pre_topc(D_115,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48,c_200])).

tff(c_2,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [D_115,B_4] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_115),B_4) = k9_relat_1('#skF_4',B_4)
      | ~ r1_tarski(B_4,u1_struct_0(D_115))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_115,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2])).

tff(c_216,plain,(
    ! [D_116,B_117] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_116),B_117) = k9_relat_1('#skF_4',B_117)
      | ~ r1_tarski(B_117,u1_struct_0(D_116))
      | ~ m1_pre_topc(D_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_208])).

tff(c_219,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_216])).

tff(c_222,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_219])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:57:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.40  
% 2.37/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.40  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.40  
% 2.37/1.40  %Foreground sorts:
% 2.37/1.40  
% 2.37/1.40  
% 2.37/1.40  %Background operators:
% 2.37/1.40  
% 2.37/1.40  
% 2.37/1.40  %Foreground operators:
% 2.37/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.37/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.40  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.37/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.40  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.37/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.37/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.40  
% 2.37/1.42  tff(f_138, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 2.37/1.42  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.37/1.42  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.37/1.42  tff(f_102, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 2.37/1.42  tff(f_40, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.37/1.42  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.37/1.42  tff(f_46, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.37/1.42  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.37/1.42  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.37/1.42  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_50, plain, (![B_67, A_68]: (l1_pre_topc(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.42  tff(c_53, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.37/1.42  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_53])).
% 2.37/1.42  tff(c_10, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.42  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_30, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_100, plain, (![A_85, B_86, C_87, D_88]: (v1_funct_1(k2_tmap_1(A_85, B_86, C_87, D_88)) | ~l1_struct_0(D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85), u1_struct_0(B_86)))) | ~v1_funct_2(C_87, u1_struct_0(A_85), u1_struct_0(B_86)) | ~v1_funct_1(C_87) | ~l1_struct_0(B_86) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.37/1.42  tff(c_102, plain, (![D_88]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_88)) | ~l1_struct_0(D_88) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.37/1.42  tff(c_105, plain, (![D_88]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_88)) | ~l1_struct_0(D_88) | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_102])).
% 2.37/1.42  tff(c_106, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_105])).
% 2.37/1.42  tff(c_109, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_106])).
% 2.37/1.42  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_109])).
% 2.37/1.42  tff(c_115, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_105])).
% 2.37/1.42  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_114, plain, (![D_88]: (~l1_struct_0('#skF_1') | v1_funct_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_88)) | ~l1_struct_0(D_88))), inference(splitRight, [status(thm)], [c_105])).
% 2.37/1.42  tff(c_116, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 2.37/1.42  tff(c_119, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_116])).
% 2.37/1.42  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_119])).
% 2.37/1.42  tff(c_125, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_114])).
% 2.37/1.42  tff(c_134, plain, (![A_95, B_96, C_97, D_98]: (m1_subset_1(k2_tmap_1(A_95, B_96, C_97, D_98), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_98), u1_struct_0(B_96)))) | ~l1_struct_0(D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), u1_struct_0(B_96)))) | ~v1_funct_2(C_97, u1_struct_0(A_95), u1_struct_0(B_96)) | ~v1_funct_1(C_97) | ~l1_struct_0(B_96) | ~l1_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.37/1.42  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.42  tff(c_161, plain, (![C_104, D_108, A_105, D_107, B_106]: (k7_relset_1(u1_struct_0(D_108), u1_struct_0(B_106), k2_tmap_1(A_105, B_106, C_104, D_108), D_107)=k9_relat_1(k2_tmap_1(A_105, B_106, C_104, D_108), D_107) | ~l1_struct_0(D_108) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), u1_struct_0(B_106)))) | ~v1_funct_2(C_104, u1_struct_0(A_105), u1_struct_0(B_106)) | ~v1_funct_1(C_104) | ~l1_struct_0(B_106) | ~l1_struct_0(A_105))), inference(resolution, [status(thm)], [c_134, c_6])).
% 2.37/1.42  tff(c_165, plain, (![D_108, D_107]: (k7_relset_1(u1_struct_0(D_108), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_108), D_107)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_108), D_107) | ~l1_struct_0(D_108) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_161])).
% 2.37/1.42  tff(c_170, plain, (![D_109, D_110]: (k7_relset_1(u1_struct_0(D_109), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_109), D_110)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_109), D_110) | ~l1_struct_0(D_109))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_125, c_32, c_30, c_165])).
% 2.37/1.42  tff(c_71, plain, (![A_75, B_76, C_77, D_78]: (k7_relset_1(A_75, B_76, C_77, D_78)=k9_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.37/1.42  tff(c_74, plain, (![D_78]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_78)=k9_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_28, c_71])).
% 2.37/1.42  tff(c_22, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_75, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22])).
% 2.37/1.42  tff(c_176, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_170, c_75])).
% 2.37/1.42  tff(c_182, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_176])).
% 2.37/1.42  tff(c_185, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_182])).
% 2.37/1.42  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_185])).
% 2.37/1.42  tff(c_190, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_176])).
% 2.37/1.42  tff(c_24, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_4, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.42  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_4])).
% 2.37/1.42  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.37/1.42  tff(c_85, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.42  tff(c_87, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_85])).
% 2.37/1.42  tff(c_90, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_87])).
% 2.37/1.42  tff(c_192, plain, (![A_111, B_112, C_113, D_114]: (k2_partfun1(u1_struct_0(A_111), u1_struct_0(B_112), C_113, u1_struct_0(D_114))=k2_tmap_1(A_111, B_112, C_113, D_114) | ~m1_pre_topc(D_114, A_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0(A_111), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.37/1.42  tff(c_196, plain, (![D_114]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_114))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_114) | ~m1_pre_topc(D_114, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_192])).
% 2.37/1.42  tff(c_200, plain, (![D_114]: (k7_relat_1('#skF_4', u1_struct_0(D_114))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_114) | ~m1_pre_topc(D_114, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_46, c_44, c_32, c_30, c_90, c_196])).
% 2.37/1.42  tff(c_202, plain, (![D_115]: (k7_relat_1('#skF_4', u1_struct_0(D_115))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_115) | ~m1_pre_topc(D_115, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_48, c_200])).
% 2.37/1.42  tff(c_2, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.42  tff(c_208, plain, (![D_115, B_4]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_115), B_4)=k9_relat_1('#skF_4', B_4) | ~r1_tarski(B_4, u1_struct_0(D_115)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_115, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_2])).
% 2.37/1.42  tff(c_216, plain, (![D_116, B_117]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_116), B_117)=k9_relat_1('#skF_4', B_117) | ~r1_tarski(B_117, u1_struct_0(D_116)) | ~m1_pre_topc(D_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_208])).
% 2.37/1.42  tff(c_219, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_216])).
% 2.37/1.42  tff(c_222, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_219])).
% 2.37/1.42  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_222])).
% 2.37/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.42  
% 2.37/1.42  Inference rules
% 2.37/1.42  ----------------------
% 2.37/1.42  #Ref     : 0
% 2.37/1.42  #Sup     : 33
% 2.37/1.42  #Fact    : 0
% 2.37/1.42  #Define  : 0
% 2.37/1.42  #Split   : 3
% 2.37/1.42  #Chain   : 0
% 2.37/1.42  #Close   : 0
% 2.37/1.42  
% 2.37/1.42  Ordering : KBO
% 2.37/1.42  
% 2.37/1.42  Simplification rules
% 2.37/1.42  ----------------------
% 2.37/1.42  #Subsume      : 0
% 2.37/1.42  #Demod        : 29
% 2.37/1.42  #Tautology    : 10
% 2.37/1.42  #SimpNegUnit  : 2
% 2.37/1.42  #BackRed      : 1
% 2.37/1.42  
% 2.37/1.42  #Partial instantiations: 0
% 2.37/1.42  #Strategies tried      : 1
% 2.37/1.42  
% 2.37/1.42  Timing (in seconds)
% 2.37/1.42  ----------------------
% 2.37/1.42  Preprocessing        : 0.34
% 2.37/1.42  Parsing              : 0.19
% 2.37/1.42  CNF conversion       : 0.03
% 2.37/1.43  Main loop            : 0.23
% 2.37/1.43  Inferencing          : 0.09
% 2.37/1.43  Reduction            : 0.07
% 2.37/1.43  Demodulation         : 0.05
% 2.37/1.43  BG Simplification    : 0.02
% 2.37/1.43  Subsumption          : 0.04
% 2.37/1.43  Abstraction          : 0.02
% 2.37/1.43  MUC search           : 0.00
% 2.37/1.43  Cooper               : 0.00
% 2.37/1.43  Total                : 0.61
% 2.37/1.43  Index Insertion      : 0.00
% 2.37/1.43  Index Deletion       : 0.00
% 2.37/1.43  Index Matching       : 0.00
% 2.37/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
