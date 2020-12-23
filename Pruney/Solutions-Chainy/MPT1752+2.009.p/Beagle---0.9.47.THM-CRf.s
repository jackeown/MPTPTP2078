%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 223 expanded)
%              Number of leaves         :   36 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 (1086 expanded)
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

tff(f_145,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_109,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_91,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_53,plain,(
    ! [B_71,A_72] :
      ( l1_pre_topc(B_71)
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_59,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_12,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_353,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( v1_funct_1(k2_tmap_1(A_141,B_142,C_143,D_144))
      | ~ l1_struct_0(D_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,u1_struct_0(A_141),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_struct_0(B_142)
      | ~ l1_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_355,plain,(
    ! [D_144] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_144))
      | ~ l1_struct_0(D_144)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_353])).

tff(c_358,plain,(
    ! [D_144] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_144))
      | ~ l1_struct_0(D_144)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_355])).

tff(c_359,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_362,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_362])).

tff(c_368,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_367,plain,(
    ! [D_144] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_144))
      | ~ l1_struct_0(D_144) ) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_369,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_372,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_369])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_372])).

tff(c_378,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_398,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( m1_subset_1(k2_tmap_1(A_151,B_152,C_153,D_154),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_154),u1_struct_0(B_152))))
      | ~ l1_struct_0(D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151),u1_struct_0(B_152))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_151),u1_struct_0(B_152))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0(B_152)
      | ~ l1_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k8_relset_1(A_6,B_7,C_8,D_9) = k10_relat_1(C_8,D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_440,plain,(
    ! [D_166,B_163,A_165,C_167,D_164] :
      ( k8_relset_1(u1_struct_0(D_166),u1_struct_0(B_163),k2_tmap_1(A_165,B_163,C_167,D_166),D_164) = k10_relat_1(k2_tmap_1(A_165,B_163,C_167,D_166),D_164)
      | ~ l1_struct_0(D_166)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165),u1_struct_0(B_163))))
      | ~ v1_funct_2(C_167,u1_struct_0(A_165),u1_struct_0(B_163))
      | ~ v1_funct_1(C_167)
      | ~ l1_struct_0(B_163)
      | ~ l1_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_398,c_6])).

tff(c_444,plain,(
    ! [D_166,D_164] :
      ( k8_relset_1(u1_struct_0(D_166),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_166),D_164) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_166),D_164)
      | ~ l1_struct_0(D_166)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_440])).

tff(c_449,plain,(
    ! [D_168,D_169] :
      ( k8_relset_1(u1_struct_0(D_168),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_168),D_169) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_168),D_169)
      | ~ l1_struct_0(D_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_378,c_34,c_32,c_444])).

tff(c_72,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k8_relset_1(A_75,B_76,C_77,D_78) = k10_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [D_78] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_78) = k10_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_24,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_116,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_24])).

tff(c_455,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_116])).

tff(c_461,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_464,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_461])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_464])).

tff(c_469,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_86,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,(
    ! [D_83] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_91,plain,(
    ! [D_83] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_88])).

tff(c_471,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k2_partfun1(u1_struct_0(A_170),u1_struct_0(B_171),C_172,u1_struct_0(D_173)) = k2_tmap_1(A_170,B_171,C_172,D_173)
      | ~ m1_pre_topc(D_173,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_170),u1_struct_0(B_171))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_170),u1_struct_0(B_171))
      | ~ v1_funct_1(C_172)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_475,plain,(
    ! [D_173] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_173)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_173)
      | ~ m1_pre_topc(D_173,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_471])).

tff(c_479,plain,(
    ! [D_173] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_173)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_173)
      | ~ m1_pre_topc(D_173,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_34,c_32,c_91,c_475])).

tff(c_481,plain,(
    ! [D_174] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_174)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_174)
      | ~ m1_pre_topc(D_174,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_479])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_26,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_76,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_26])).

tff(c_92,plain,(
    ! [A_84,B_85,C_86] :
      ( k10_relat_1(k7_relat_1(A_84,B_85),C_86) = k10_relat_1(A_84,C_86)
      | ~ r1_tarski(k10_relat_1(A_84,C_86),B_85)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_95,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_92])).

tff(c_98,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_34,c_95])).

tff(c_499,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_98])).

tff(c_513,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_499])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.57  
% 3.27/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.57  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.57  
% 3.27/1.57  %Foreground sorts:
% 3.27/1.57  
% 3.27/1.57  
% 3.27/1.57  %Background operators:
% 3.27/1.57  
% 3.27/1.57  
% 3.27/1.57  %Foreground operators:
% 3.27/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.27/1.57  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.27/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.27/1.57  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.27/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.27/1.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.27/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.57  
% 3.27/1.59  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tmap_1)).
% 3.27/1.59  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.27/1.59  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.27/1.59  tff(f_109, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.27/1.59  tff(f_38, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.27/1.59  tff(f_44, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.27/1.59  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.27/1.59  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.27/1.59  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.27/1.59  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.27/1.59  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_53, plain, (![B_71, A_72]: (l1_pre_topc(B_71) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.27/1.59  tff(c_56, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_53])).
% 3.27/1.59  tff(c_59, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 3.27/1.59  tff(c_12, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.59  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_353, plain, (![A_141, B_142, C_143, D_144]: (v1_funct_1(k2_tmap_1(A_141, B_142, C_143, D_144)) | ~l1_struct_0(D_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, u1_struct_0(A_141), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_struct_0(B_142) | ~l1_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.27/1.59  tff(c_355, plain, (![D_144]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_144)) | ~l1_struct_0(D_144) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_353])).
% 3.27/1.59  tff(c_358, plain, (![D_144]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_144)) | ~l1_struct_0(D_144) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_355])).
% 3.27/1.59  tff(c_359, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_358])).
% 3.27/1.59  tff(c_362, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_359])).
% 3.27/1.59  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_362])).
% 3.27/1.59  tff(c_368, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_358])).
% 3.27/1.59  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_367, plain, (![D_144]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_144)) | ~l1_struct_0(D_144))), inference(splitRight, [status(thm)], [c_358])).
% 3.27/1.59  tff(c_369, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_367])).
% 3.27/1.59  tff(c_372, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_369])).
% 3.27/1.59  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_372])).
% 3.27/1.59  tff(c_378, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_367])).
% 3.27/1.59  tff(c_398, plain, (![A_151, B_152, C_153, D_154]: (m1_subset_1(k2_tmap_1(A_151, B_152, C_153, D_154), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_154), u1_struct_0(B_152)))) | ~l1_struct_0(D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_151), u1_struct_0(B_152)))) | ~v1_funct_2(C_153, u1_struct_0(A_151), u1_struct_0(B_152)) | ~v1_funct_1(C_153) | ~l1_struct_0(B_152) | ~l1_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.27/1.59  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k8_relset_1(A_6, B_7, C_8, D_9)=k10_relat_1(C_8, D_9) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.27/1.59  tff(c_440, plain, (![D_166, B_163, A_165, C_167, D_164]: (k8_relset_1(u1_struct_0(D_166), u1_struct_0(B_163), k2_tmap_1(A_165, B_163, C_167, D_166), D_164)=k10_relat_1(k2_tmap_1(A_165, B_163, C_167, D_166), D_164) | ~l1_struct_0(D_166) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165), u1_struct_0(B_163)))) | ~v1_funct_2(C_167, u1_struct_0(A_165), u1_struct_0(B_163)) | ~v1_funct_1(C_167) | ~l1_struct_0(B_163) | ~l1_struct_0(A_165))), inference(resolution, [status(thm)], [c_398, c_6])).
% 3.27/1.59  tff(c_444, plain, (![D_166, D_164]: (k8_relset_1(u1_struct_0(D_166), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_166), D_164)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_166), D_164) | ~l1_struct_0(D_166) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_440])).
% 3.27/1.59  tff(c_449, plain, (![D_168, D_169]: (k8_relset_1(u1_struct_0(D_168), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_168), D_169)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_168), D_169) | ~l1_struct_0(D_168))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_378, c_34, c_32, c_444])).
% 3.27/1.59  tff(c_72, plain, (![A_75, B_76, C_77, D_78]: (k8_relset_1(A_75, B_76, C_77, D_78)=k10_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.27/1.59  tff(c_75, plain, (![D_78]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_78)=k10_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_30, c_72])).
% 3.27/1.59  tff(c_24, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_116, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_24])).
% 3.27/1.59  tff(c_455, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_449, c_116])).
% 3.27/1.59  tff(c_461, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_455])).
% 3.27/1.59  tff(c_464, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_461])).
% 3.27/1.59  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_464])).
% 3.27/1.59  tff(c_469, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_455])).
% 3.27/1.59  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_86, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.27/1.59  tff(c_88, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_86])).
% 3.27/1.59  tff(c_91, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_88])).
% 3.27/1.59  tff(c_471, plain, (![A_170, B_171, C_172, D_173]: (k2_partfun1(u1_struct_0(A_170), u1_struct_0(B_171), C_172, u1_struct_0(D_173))=k2_tmap_1(A_170, B_171, C_172, D_173) | ~m1_pre_topc(D_173, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_170), u1_struct_0(B_171)))) | ~v1_funct_2(C_172, u1_struct_0(A_170), u1_struct_0(B_171)) | ~v1_funct_1(C_172) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.59  tff(c_475, plain, (![D_173]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_173))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_173) | ~m1_pre_topc(D_173, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_471])).
% 3.27/1.59  tff(c_479, plain, (![D_173]: (k7_relat_1('#skF_4', u1_struct_0(D_173))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_173) | ~m1_pre_topc(D_173, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_34, c_32, c_91, c_475])).
% 3.27/1.59  tff(c_481, plain, (![D_174]: (k7_relat_1('#skF_4', u1_struct_0(D_174))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_174) | ~m1_pre_topc(D_174, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_479])).
% 3.27/1.59  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.27/1.59  tff(c_60, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.59  tff(c_63, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_60])).
% 3.27/1.59  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_63])).
% 3.27/1.59  tff(c_26, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.27/1.59  tff(c_76, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_26])).
% 3.27/1.59  tff(c_92, plain, (![A_84, B_85, C_86]: (k10_relat_1(k7_relat_1(A_84, B_85), C_86)=k10_relat_1(A_84, C_86) | ~r1_tarski(k10_relat_1(A_84, C_86), B_85) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.59  tff(c_95, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_92])).
% 3.27/1.59  tff(c_98, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_34, c_95])).
% 3.27/1.59  tff(c_499, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_481, c_98])).
% 3.27/1.59  tff(c_513, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_499])).
% 3.27/1.59  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_513])).
% 3.27/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.59  
% 3.27/1.59  Inference rules
% 3.27/1.59  ----------------------
% 3.27/1.59  #Ref     : 0
% 3.27/1.59  #Sup     : 86
% 3.27/1.59  #Fact    : 0
% 3.27/1.59  #Define  : 0
% 3.27/1.59  #Split   : 11
% 3.27/1.59  #Chain   : 0
% 3.27/1.59  #Close   : 0
% 3.27/1.59  
% 3.27/1.59  Ordering : KBO
% 3.27/1.59  
% 3.27/1.59  Simplification rules
% 3.27/1.59  ----------------------
% 3.27/1.59  #Subsume      : 0
% 3.27/1.59  #Demod        : 90
% 3.27/1.59  #Tautology    : 18
% 3.27/1.59  #SimpNegUnit  : 4
% 3.27/1.59  #BackRed      : 1
% 3.27/1.59  
% 3.27/1.59  #Partial instantiations: 0
% 3.27/1.59  #Strategies tried      : 1
% 3.27/1.59  
% 3.27/1.59  Timing (in seconds)
% 3.27/1.59  ----------------------
% 3.27/1.60  Preprocessing        : 0.46
% 3.27/1.60  Parsing              : 0.25
% 3.27/1.60  CNF conversion       : 0.03
% 3.27/1.60  Main loop            : 0.36
% 3.27/1.60  Inferencing          : 0.14
% 3.27/1.60  Reduction            : 0.11
% 3.27/1.60  Demodulation         : 0.08
% 3.27/1.60  BG Simplification    : 0.03
% 3.27/1.60  Subsumption          : 0.06
% 3.27/1.60  Abstraction          : 0.02
% 3.27/1.60  MUC search           : 0.00
% 3.27/1.60  Cooper               : 0.00
% 3.27/1.60  Total                : 0.86
% 3.27/1.60  Index Insertion      : 0.00
% 3.27/1.60  Index Deletion       : 0.00
% 3.27/1.60  Index Matching       : 0.00
% 3.27/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
