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
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 225 expanded)
%              Number of leaves         :   42 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 864 expanded)
%              Number of equality atoms :   33 ( 108 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_107,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_12])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_102,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k8_relset_1(A_96,B_97,C_98,D_99) = k10_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    ! [D_99] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_99) = k10_relat_1('#skF_4',D_99) ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_30,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_118,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_30])).

tff(c_300,plain,(
    ! [A_153,B_154,C_155] :
      ( k10_relat_1(k7_relat_1(A_153,B_154),C_155) = k10_relat_1(A_153,C_155)
      | ~ r1_tarski(k10_relat_1(A_153,C_155),B_154)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_303,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_300])).

tff(c_306,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_38,c_303])).

tff(c_24,plain,(
    ! [A_31,B_34,C_35] :
      ( k10_relat_1(k7_relat_1(A_31,B_34),C_35) = k10_relat_1(A_31,C_35)
      | ~ r1_tarski(k10_relat_1(A_31,C_35),B_34)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_329,plain,(
    ! [B_34] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),B_34),'#skF_5') = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5')
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),B_34)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_24])).

tff(c_332,plain,(
    ! [B_34] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),B_34),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),B_34)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_329])).

tff(c_441,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_447,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_441])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_447])).

tff(c_455,plain,(
    v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_238,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k2_partfun1(A_134,B_135,C_136,D_137) = k7_relat_1(C_136,D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_245,plain,(
    ! [D_137] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_137) = k7_relat_1('#skF_4',D_137)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_238])).

tff(c_253,plain,(
    ! [D_137] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_137) = k7_relat_1('#skF_4',D_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_245])).

tff(c_307,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k2_partfun1(u1_struct_0(A_156),u1_struct_0(B_157),C_158,u1_struct_0(D_159)) = k2_tmap_1(A_156,B_157,C_158,D_159)
      | ~ m1_pre_topc(D_159,A_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0(A_156),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_315,plain,(
    ! [D_159] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_307])).

tff(c_323,plain,(
    ! [D_159] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_38,c_36,c_253,c_315])).

tff(c_324,plain,(
    ! [D_159] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_323])).

tff(c_110,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,(
    ! [D_103] : k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_103) = k9_relat_1('#skF_4',D_103) ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_156,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( m1_subset_1(k7_relset_1(A_114,B_115,C_116,D_117),k1_zfmisc_1(B_115))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [D_103] :
      ( m1_subset_1(k9_relat_1('#skF_4',D_103),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_156])).

tff(c_179,plain,(
    ! [D_118] : m1_subset_1(k9_relat_1('#skF_4',D_118),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_172])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_183,plain,(
    ! [D_118] : r1_tarski(k9_relat_1('#skF_4',D_118),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_8,A_7)),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    ! [C_120,A_121,B_122] :
      ( m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ r1_tarski(k2_relat_1(C_120),B_122)
      | ~ r1_tarski(k1_relat_1(C_120),A_121)
      | ~ v1_relat_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_235,plain,(
    ! [C_131,A_132,B_133] :
      ( r1_tarski(C_131,k2_zfmisc_1(A_132,B_133))
      | ~ r1_tarski(k2_relat_1(C_131),B_133)
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_599,plain,(
    ! [B_245,A_246,A_247,B_248] :
      ( r1_tarski(k7_relat_1(B_245,A_246),k2_zfmisc_1(A_247,B_248))
      | ~ r1_tarski(k9_relat_1(B_245,A_246),B_248)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_245,A_246)),A_247)
      | ~ v1_relat_1(k7_relat_1(B_245,A_246))
      | ~ v1_relat_1(B_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_235])).

tff(c_607,plain,(
    ! [B_249,A_250,B_251] :
      ( r1_tarski(k7_relat_1(B_249,A_250),k2_zfmisc_1(A_250,B_251))
      | ~ r1_tarski(k9_relat_1(B_249,A_250),B_251)
      | ~ v1_relat_1(k7_relat_1(B_249,A_250))
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_10,c_599])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_96,B_97,A_1,D_99] :
      ( k8_relset_1(A_96,B_97,A_1,D_99) = k10_relat_1(A_1,D_99)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_636,plain,(
    ! [A_257,B_258,B_259,D_260] :
      ( k8_relset_1(A_257,B_258,k7_relat_1(B_259,A_257),D_260) = k10_relat_1(k7_relat_1(B_259,A_257),D_260)
      | ~ r1_tarski(k9_relat_1(B_259,A_257),B_258)
      | ~ v1_relat_1(k7_relat_1(B_259,A_257))
      | ~ v1_relat_1(B_259) ) ),
    inference(resolution,[status(thm)],[c_607,c_109])).

tff(c_642,plain,(
    ! [D_118,D_260] :
      ( k8_relset_1(D_118,u1_struct_0('#skF_2'),k7_relat_1('#skF_4',D_118),D_260) = k10_relat_1(k7_relat_1('#skF_4',D_118),D_260)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_118))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_183,c_636])).

tff(c_649,plain,(
    ! [D_261,D_262] :
      ( k8_relset_1(D_261,u1_struct_0('#skF_2'),k7_relat_1('#skF_4',D_261),D_262) = k10_relat_1(k7_relat_1('#skF_4',D_261),D_262)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_642])).

tff(c_708,plain,(
    ! [D_277,D_278] :
      ( k8_relset_1(u1_struct_0(D_277),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_277),D_278) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_277)),D_278)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_277)))
      | ~ m1_pre_topc(D_277,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_649])).

tff(c_28,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_137,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_28])).

tff(c_714,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_137])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_455,c_306,c_714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:03:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.49  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.35/1.49  
% 3.35/1.49  %Foreground sorts:
% 3.35/1.49  
% 3.35/1.49  
% 3.35/1.49  %Background operators:
% 3.35/1.49  
% 3.35/1.49  
% 3.35/1.49  %Foreground operators:
% 3.35/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.35/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.35/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.35/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.35/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.35/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.35/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.35/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.35/1.49  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.35/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.35/1.49  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.35/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.49  
% 3.35/1.51  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tmap_1)).
% 3.35/1.51  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.35/1.51  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.35/1.51  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.35/1.51  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.35/1.51  tff(f_71, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.35/1.51  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.35/1.51  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.35/1.51  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.35/1.51  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.35/1.51  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.35/1.51  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.35/1.51  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.35/1.51  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_12, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.51  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_12])).
% 3.35/1.51  tff(c_6, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.35/1.51  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_102, plain, (![A_96, B_97, C_98, D_99]: (k8_relset_1(A_96, B_97, C_98, D_99)=k10_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.51  tff(c_108, plain, (![D_99]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_99)=k10_relat_1('#skF_4', D_99))), inference(resolution, [status(thm)], [c_34, c_102])).
% 3.35/1.51  tff(c_30, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_118, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_30])).
% 3.35/1.51  tff(c_300, plain, (![A_153, B_154, C_155]: (k10_relat_1(k7_relat_1(A_153, B_154), C_155)=k10_relat_1(A_153, C_155) | ~r1_tarski(k10_relat_1(A_153, C_155), B_154) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.51  tff(c_303, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_118, c_300])).
% 3.35/1.51  tff(c_306, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_38, c_303])).
% 3.35/1.51  tff(c_24, plain, (![A_31, B_34, C_35]: (k10_relat_1(k7_relat_1(A_31, B_34), C_35)=k10_relat_1(A_31, C_35) | ~r1_tarski(k10_relat_1(A_31, C_35), B_34) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.51  tff(c_329, plain, (![B_34]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), B_34), '#skF_5')=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_5'), B_34) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_306, c_24])).
% 3.35/1.51  tff(c_332, plain, (![B_34]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), B_34), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_5'), B_34) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_329])).
% 3.35/1.51  tff(c_441, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_332])).
% 3.35/1.51  tff(c_447, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_441])).
% 3.35/1.51  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_447])).
% 3.35/1.51  tff(c_455, plain, (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_332])).
% 3.35/1.51  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_238, plain, (![A_134, B_135, C_136, D_137]: (k2_partfun1(A_134, B_135, C_136, D_137)=k7_relat_1(C_136, D_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.35/1.51  tff(c_245, plain, (![D_137]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_137)=k7_relat_1('#skF_4', D_137) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_238])).
% 3.35/1.51  tff(c_253, plain, (![D_137]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_137)=k7_relat_1('#skF_4', D_137))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_245])).
% 3.35/1.51  tff(c_307, plain, (![A_156, B_157, C_158, D_159]: (k2_partfun1(u1_struct_0(A_156), u1_struct_0(B_157), C_158, u1_struct_0(D_159))=k2_tmap_1(A_156, B_157, C_158, D_159) | ~m1_pre_topc(D_159, A_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0(A_156), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.35/1.51  tff(c_315, plain, (![D_159]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_307])).
% 3.35/1.51  tff(c_323, plain, (![D_159]: (k7_relat_1('#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_38, c_36, c_253, c_315])).
% 3.35/1.51  tff(c_324, plain, (![D_159]: (k7_relat_1('#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_323])).
% 3.35/1.51  tff(c_110, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.51  tff(c_116, plain, (![D_103]: (k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_103)=k9_relat_1('#skF_4', D_103))), inference(resolution, [status(thm)], [c_34, c_110])).
% 3.35/1.51  tff(c_156, plain, (![A_114, B_115, C_116, D_117]: (m1_subset_1(k7_relset_1(A_114, B_115, C_116, D_117), k1_zfmisc_1(B_115)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.51  tff(c_172, plain, (![D_103]: (m1_subset_1(k9_relat_1('#skF_4', D_103), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_156])).
% 3.35/1.51  tff(c_179, plain, (![D_118]: (m1_subset_1(k9_relat_1('#skF_4', D_118), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_172])).
% 3.35/1.51  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.51  tff(c_183, plain, (![D_118]: (r1_tarski(k9_relat_1('#skF_4', D_118), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_179, c_2])).
% 3.35/1.51  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(k7_relat_1(B_8, A_7)), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.51  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.51  tff(c_185, plain, (![C_120, A_121, B_122]: (m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~r1_tarski(k2_relat_1(C_120), B_122) | ~r1_tarski(k1_relat_1(C_120), A_121) | ~v1_relat_1(C_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.35/1.51  tff(c_235, plain, (![C_131, A_132, B_133]: (r1_tarski(C_131, k2_zfmisc_1(A_132, B_133)) | ~r1_tarski(k2_relat_1(C_131), B_133) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_185, c_2])).
% 3.35/1.51  tff(c_599, plain, (![B_245, A_246, A_247, B_248]: (r1_tarski(k7_relat_1(B_245, A_246), k2_zfmisc_1(A_247, B_248)) | ~r1_tarski(k9_relat_1(B_245, A_246), B_248) | ~r1_tarski(k1_relat_1(k7_relat_1(B_245, A_246)), A_247) | ~v1_relat_1(k7_relat_1(B_245, A_246)) | ~v1_relat_1(B_245))), inference(superposition, [status(thm), theory('equality')], [c_8, c_235])).
% 3.35/1.51  tff(c_607, plain, (![B_249, A_250, B_251]: (r1_tarski(k7_relat_1(B_249, A_250), k2_zfmisc_1(A_250, B_251)) | ~r1_tarski(k9_relat_1(B_249, A_250), B_251) | ~v1_relat_1(k7_relat_1(B_249, A_250)) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_10, c_599])).
% 3.35/1.51  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.51  tff(c_109, plain, (![A_96, B_97, A_1, D_99]: (k8_relset_1(A_96, B_97, A_1, D_99)=k10_relat_1(A_1, D_99) | ~r1_tarski(A_1, k2_zfmisc_1(A_96, B_97)))), inference(resolution, [status(thm)], [c_4, c_102])).
% 3.35/1.51  tff(c_636, plain, (![A_257, B_258, B_259, D_260]: (k8_relset_1(A_257, B_258, k7_relat_1(B_259, A_257), D_260)=k10_relat_1(k7_relat_1(B_259, A_257), D_260) | ~r1_tarski(k9_relat_1(B_259, A_257), B_258) | ~v1_relat_1(k7_relat_1(B_259, A_257)) | ~v1_relat_1(B_259))), inference(resolution, [status(thm)], [c_607, c_109])).
% 3.35/1.51  tff(c_642, plain, (![D_118, D_260]: (k8_relset_1(D_118, u1_struct_0('#skF_2'), k7_relat_1('#skF_4', D_118), D_260)=k10_relat_1(k7_relat_1('#skF_4', D_118), D_260) | ~v1_relat_1(k7_relat_1('#skF_4', D_118)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_183, c_636])).
% 3.35/1.51  tff(c_649, plain, (![D_261, D_262]: (k8_relset_1(D_261, u1_struct_0('#skF_2'), k7_relat_1('#skF_4', D_261), D_262)=k10_relat_1(k7_relat_1('#skF_4', D_261), D_262) | ~v1_relat_1(k7_relat_1('#skF_4', D_261)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_642])).
% 3.35/1.51  tff(c_708, plain, (![D_277, D_278]: (k8_relset_1(u1_struct_0(D_277), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_277), D_278)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_277)), D_278) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_277))) | ~m1_pre_topc(D_277, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_649])).
% 3.35/1.51  tff(c_28, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.35/1.51  tff(c_137, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_28])).
% 3.35/1.51  tff(c_714, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_708, c_137])).
% 3.35/1.51  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_455, c_306, c_714])).
% 3.35/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.51  
% 3.35/1.51  Inference rules
% 3.35/1.51  ----------------------
% 3.35/1.51  #Ref     : 0
% 3.35/1.51  #Sup     : 154
% 3.35/1.51  #Fact    : 0
% 3.35/1.51  #Define  : 0
% 3.35/1.51  #Split   : 2
% 3.35/1.51  #Chain   : 0
% 3.35/1.51  #Close   : 0
% 3.35/1.51  
% 3.35/1.51  Ordering : KBO
% 3.35/1.51  
% 3.35/1.51  Simplification rules
% 3.35/1.51  ----------------------
% 3.35/1.51  #Subsume      : 8
% 3.35/1.51  #Demod        : 47
% 3.35/1.51  #Tautology    : 34
% 3.35/1.51  #SimpNegUnit  : 1
% 3.35/1.51  #BackRed      : 1
% 3.35/1.51  
% 3.35/1.51  #Partial instantiations: 0
% 3.35/1.51  #Strategies tried      : 1
% 3.35/1.51  
% 3.35/1.51  Timing (in seconds)
% 3.35/1.51  ----------------------
% 3.35/1.52  Preprocessing        : 0.34
% 3.35/1.52  Parsing              : 0.18
% 3.35/1.52  CNF conversion       : 0.03
% 3.35/1.52  Main loop            : 0.41
% 3.35/1.52  Inferencing          : 0.17
% 3.35/1.52  Reduction            : 0.12
% 3.35/1.52  Demodulation         : 0.08
% 3.35/1.52  BG Simplification    : 0.03
% 3.35/1.52  Subsumption          : 0.07
% 3.35/1.52  Abstraction          : 0.03
% 3.35/1.52  MUC search           : 0.00
% 3.35/1.52  Cooper               : 0.00
% 3.35/1.52  Total                : 0.80
% 3.35/1.52  Index Insertion      : 0.00
% 3.35/1.52  Index Deletion       : 0.00
% 3.35/1.52  Index Matching       : 0.00
% 3.35/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
