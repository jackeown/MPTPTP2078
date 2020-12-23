%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 439 expanded)
%              Number of leaves         :   44 ( 178 expanded)
%              Depth                    :   15
%              Number of atoms          :  243 (1918 expanded)
%              Number of equality atoms :   30 ( 194 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

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

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_161,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_16,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42,c_6])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_88])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_300,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k8_relset_1(A_146,B_147,C_148,D_149) = k10_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_306,plain,(
    ! [D_149] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_149) = k10_relat_1('#skF_4',D_149) ),
    inference(resolution,[status(thm)],[c_42,c_300])).

tff(c_38,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_309,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_38])).

tff(c_451,plain,(
    ! [A_180,B_181,C_182] :
      ( k10_relat_1(k7_relat_1(A_180,B_181),C_182) = k10_relat_1(A_180,C_182)
      | ~ r1_tarski(k10_relat_1(A_180,C_182),B_181)
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_454,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_309,c_451])).

tff(c_457,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_46,c_454])).

tff(c_32,plain,(
    ! [A_34,B_37,C_38] :
      ( k10_relat_1(k7_relat_1(A_34,B_37),C_38) = k10_relat_1(A_34,C_38)
      | ~ r1_tarski(k10_relat_1(A_34,C_38),B_37)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_461,plain,(
    ! [B_37] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),B_37),'#skF_5') = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5')
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),B_37)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_32])).

tff(c_464,plain,(
    ! [B_37] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),B_37),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
      | ~ r1_tarski(k10_relat_1('#skF_4','#skF_5'),B_37)
      | ~ v1_funct_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_461])).

tff(c_474,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_477,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_474])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_477])).

tff(c_483,plain,(
    v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_116,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_124,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_116])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [C_134,A_135,B_136] :
      ( v5_relat_1(C_134,A_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(B_136))
      | ~ v5_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    ! [A_138,A_139,B_140] :
      ( v5_relat_1(A_138,A_139)
      | ~ v5_relat_1(B_140,A_139)
      | ~ v1_relat_1(B_140)
      | ~ r1_tarski(A_138,B_140) ) ),
    inference(resolution,[status(thm)],[c_4,c_234])).

tff(c_253,plain,(
    ! [A_138] :
      ( v5_relat_1(A_138,u1_struct_0('#skF_2'))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_138,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_124,c_247])).

tff(c_258,plain,(
    ! [A_138] :
      ( v5_relat_1(A_138,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_138,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_253])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_345,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k2_partfun1(A_155,B_156,C_157,D_158) = k7_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_347,plain,(
    ! [D_158] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_158) = k7_relat_1('#skF_4',D_158)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_345])).

tff(c_353,plain,(
    ! [D_158] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_158) = k7_relat_1('#skF_4',D_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_347])).

tff(c_507,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k2_partfun1(u1_struct_0(A_199),u1_struct_0(B_200),C_201,u1_struct_0(D_202)) = k2_tmap_1(A_199,B_200,C_201,D_202)
      | ~ m1_pre_topc(D_202,A_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_199),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_512,plain,(
    ! [D_202] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_507])).

tff(c_519,plain,(
    ! [D_202] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_46,c_44,c_353,c_512])).

tff(c_520,plain,(
    ! [D_202] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_519])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_413,plain,(
    ! [C_171,A_172,B_173] :
      ( m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ r1_tarski(k2_relat_1(C_171),B_173)
      | ~ r1_tarski(k1_relat_1(C_171),A_172)
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_466,plain,(
    ! [C_183,A_184,B_185] :
      ( r1_tarski(C_183,k2_zfmisc_1(A_184,B_185))
      | ~ r1_tarski(k2_relat_1(C_183),B_185)
      | ~ r1_tarski(k1_relat_1(C_183),A_184)
      | ~ v1_relat_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_413,c_2])).

tff(c_470,plain,(
    ! [B_186,A_187,A_188] :
      ( r1_tarski(B_186,k2_zfmisc_1(A_187,A_188))
      | ~ r1_tarski(k1_relat_1(B_186),A_187)
      | ~ v5_relat_1(B_186,A_188)
      | ~ v1_relat_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_12,c_466])).

tff(c_735,plain,(
    ! [B_251,A_252,A_253] :
      ( r1_tarski(k7_relat_1(B_251,A_252),k2_zfmisc_1(A_252,A_253))
      | ~ v5_relat_1(k7_relat_1(B_251,A_252),A_253)
      | ~ v1_relat_1(k7_relat_1(B_251,A_252))
      | ~ v1_relat_1(B_251) ) ),
    inference(resolution,[status(thm)],[c_18,c_470])).

tff(c_753,plain,(
    ! [D_202,A_253] :
      ( r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_202),k2_zfmisc_1(u1_struct_0(D_202),A_253))
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_202)),A_253)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_202)))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_202,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_735])).

tff(c_1024,plain,(
    ! [D_312,A_313] :
      ( r1_tarski(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_312),k2_zfmisc_1(u1_struct_0(D_312),A_313))
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_312)),A_313)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_312)))
      | ~ m1_pre_topc(D_312,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_753])).

tff(c_125,plain,(
    ! [A_1,B_97,A_98] :
      ( v5_relat_1(A_1,B_97)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_98,B_97)) ) ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_1060,plain,(
    ! [D_314,A_315] :
      ( v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_314),A_315)
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_314)),A_315)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_314)))
      | ~ m1_pre_topc(D_314,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1024,c_125])).

tff(c_1075,plain,(
    ! [D_314] :
      ( v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_314),u1_struct_0('#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_314)))
      | ~ m1_pre_topc(D_314,'#skF_1')
      | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0(D_314)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_258,c_1060])).

tff(c_522,plain,(
    ! [D_203] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_203)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_203)
      | ~ m1_pre_topc(D_203,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_519])).

tff(c_530,plain,
    ( v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_483])).

tff(c_559,plain,(
    v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_530])).

tff(c_533,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_457])).

tff(c_561,plain,(
    k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_533])).

tff(c_545,plain,(
    ! [D_203] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_203)),u1_struct_0(D_203))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_203,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_18])).

tff(c_569,plain,(
    ! [D_203] :
      ( r1_tarski(k1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_203)),u1_struct_0(D_203))
      | ~ m1_pre_topc(D_203,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_545])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k8_relset_1(A_23,B_24,C_25,D_26) = k10_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_691,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k8_relset_1(A_229,B_230,C_231,D_232) = k10_relat_1(C_231,D_232)
      | ~ r1_tarski(k2_relat_1(C_231),B_230)
      | ~ r1_tarski(k1_relat_1(C_231),A_229)
      | ~ v1_relat_1(C_231) ) ),
    inference(resolution,[status(thm)],[c_413,c_26])).

tff(c_699,plain,(
    ! [A_237,A_238,B_239,D_240] :
      ( k8_relset_1(A_237,A_238,B_239,D_240) = k10_relat_1(B_239,D_240)
      | ~ r1_tarski(k1_relat_1(B_239),A_237)
      | ~ v5_relat_1(B_239,A_238)
      | ~ v1_relat_1(B_239) ) ),
    inference(resolution,[status(thm)],[c_12,c_691])).

tff(c_2354,plain,(
    ! [D_524,A_525,D_526] :
      ( k8_relset_1(u1_struct_0(D_524),A_525,k2_tmap_1('#skF_1','#skF_2','#skF_4',D_524),D_526) = k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_524),D_526)
      | ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_524),A_525)
      | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4',D_524))
      | ~ m1_pre_topc(D_524,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_569,c_699])).

tff(c_36,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_308,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_36])).

tff(c_2360,plain,
    ( k10_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_308])).

tff(c_2366,plain,(
    ~ v5_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_559,c_561,c_2360])).

tff(c_2370,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1075,c_2366])).

tff(c_2376,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_483,c_2370])).

tff(c_2383,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2376])).

tff(c_2389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:25:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.13  
% 6.06/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.06/2.13  
% 6.06/2.13  %Foreground sorts:
% 6.06/2.13  
% 6.06/2.13  
% 6.06/2.13  %Background operators:
% 6.06/2.13  
% 6.06/2.13  
% 6.06/2.13  %Foreground operators:
% 6.06/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.06/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.06/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.06/2.13  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.06/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.06/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.06/2.13  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.06/2.13  tff('#skF_2', type, '#skF_2': $i).
% 6.06/2.13  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.13  tff('#skF_1', type, '#skF_1': $i).
% 6.06/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.06/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.06/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.06/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.06/2.13  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.13  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.06/2.13  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.06/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.06/2.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.06/2.13  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.06/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.06/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.06/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.13  
% 6.06/2.15  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.06/2.15  tff(f_161, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tmap_1)).
% 6.06/2.15  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.06/2.15  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.06/2.15  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.06/2.15  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.06/2.15  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 6.06/2.15  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.06/2.15  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.06/2.15  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 6.06/2.15  tff(f_89, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.06/2.15  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.06/2.15  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.06/2.15  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.06/2.15  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.06/2.15  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.06/2.15  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.06/2.15  tff(c_88, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42, c_6])).
% 6.06/2.15  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_88])).
% 6.06/2.15  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.06/2.15  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.06/2.15  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_300, plain, (![A_146, B_147, C_148, D_149]: (k8_relset_1(A_146, B_147, C_148, D_149)=k10_relat_1(C_148, D_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.06/2.15  tff(c_306, plain, (![D_149]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_149)=k10_relat_1('#skF_4', D_149))), inference(resolution, [status(thm)], [c_42, c_300])).
% 6.06/2.15  tff(c_38, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_309, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_38])).
% 6.06/2.15  tff(c_451, plain, (![A_180, B_181, C_182]: (k10_relat_1(k7_relat_1(A_180, B_181), C_182)=k10_relat_1(A_180, C_182) | ~r1_tarski(k10_relat_1(A_180, C_182), B_181) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.06/2.15  tff(c_454, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_309, c_451])).
% 6.06/2.15  tff(c_457, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_46, c_454])).
% 6.06/2.15  tff(c_32, plain, (![A_34, B_37, C_38]: (k10_relat_1(k7_relat_1(A_34, B_37), C_38)=k10_relat_1(A_34, C_38) | ~r1_tarski(k10_relat_1(A_34, C_38), B_37) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.06/2.15  tff(c_461, plain, (![B_37]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), B_37), '#skF_5')=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_5'), B_37) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_457, c_32])).
% 6.06/2.15  tff(c_464, plain, (![B_37]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), B_37), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_5'), B_37) | ~v1_funct_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_461])).
% 6.06/2.15  tff(c_474, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_464])).
% 6.06/2.15  tff(c_477, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_474])).
% 6.06/2.15  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_477])).
% 6.06/2.15  tff(c_483, plain, (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_464])).
% 6.06/2.15  tff(c_116, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.06/2.15  tff(c_124, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_116])).
% 6.06/2.15  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.15  tff(c_234, plain, (![C_134, A_135, B_136]: (v5_relat_1(C_134, A_135) | ~m1_subset_1(C_134, k1_zfmisc_1(B_136)) | ~v5_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.06/2.15  tff(c_247, plain, (![A_138, A_139, B_140]: (v5_relat_1(A_138, A_139) | ~v5_relat_1(B_140, A_139) | ~v1_relat_1(B_140) | ~r1_tarski(A_138, B_140))), inference(resolution, [status(thm)], [c_4, c_234])).
% 6.06/2.15  tff(c_253, plain, (![A_138]: (v5_relat_1(A_138, u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4') | ~r1_tarski(A_138, '#skF_4'))), inference(resolution, [status(thm)], [c_124, c_247])).
% 6.06/2.15  tff(c_258, plain, (![A_138]: (v5_relat_1(A_138, u1_struct_0('#skF_2')) | ~r1_tarski(A_138, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_253])).
% 6.06/2.15  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_345, plain, (![A_155, B_156, C_157, D_158]: (k2_partfun1(A_155, B_156, C_157, D_158)=k7_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.15  tff(c_347, plain, (![D_158]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_158)=k7_relat_1('#skF_4', D_158) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_345])).
% 6.06/2.15  tff(c_353, plain, (![D_158]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_158)=k7_relat_1('#skF_4', D_158))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_347])).
% 6.06/2.15  tff(c_507, plain, (![A_199, B_200, C_201, D_202]: (k2_partfun1(u1_struct_0(A_199), u1_struct_0(B_200), C_201, u1_struct_0(D_202))=k2_tmap_1(A_199, B_200, C_201, D_202) | ~m1_pre_topc(D_202, A_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0(A_199), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.06/2.15  tff(c_512, plain, (![D_202]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_507])).
% 6.06/2.15  tff(c_519, plain, (![D_202]: (k7_relat_1('#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_46, c_44, c_353, c_512])).
% 6.06/2.15  tff(c_520, plain, (![D_202]: (k7_relat_1('#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_519])).
% 6.06/2.15  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.06/2.15  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.06/2.15  tff(c_413, plain, (![C_171, A_172, B_173]: (m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~r1_tarski(k2_relat_1(C_171), B_173) | ~r1_tarski(k1_relat_1(C_171), A_172) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.06/2.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.15  tff(c_466, plain, (![C_183, A_184, B_185]: (r1_tarski(C_183, k2_zfmisc_1(A_184, B_185)) | ~r1_tarski(k2_relat_1(C_183), B_185) | ~r1_tarski(k1_relat_1(C_183), A_184) | ~v1_relat_1(C_183))), inference(resolution, [status(thm)], [c_413, c_2])).
% 6.06/2.15  tff(c_470, plain, (![B_186, A_187, A_188]: (r1_tarski(B_186, k2_zfmisc_1(A_187, A_188)) | ~r1_tarski(k1_relat_1(B_186), A_187) | ~v5_relat_1(B_186, A_188) | ~v1_relat_1(B_186))), inference(resolution, [status(thm)], [c_12, c_466])).
% 6.06/2.15  tff(c_735, plain, (![B_251, A_252, A_253]: (r1_tarski(k7_relat_1(B_251, A_252), k2_zfmisc_1(A_252, A_253)) | ~v5_relat_1(k7_relat_1(B_251, A_252), A_253) | ~v1_relat_1(k7_relat_1(B_251, A_252)) | ~v1_relat_1(B_251))), inference(resolution, [status(thm)], [c_18, c_470])).
% 6.06/2.15  tff(c_753, plain, (![D_202, A_253]: (r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_202), k2_zfmisc_1(u1_struct_0(D_202), A_253)) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_202)), A_253) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_202))) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_202, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_735])).
% 6.06/2.15  tff(c_1024, plain, (![D_312, A_313]: (r1_tarski(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_312), k2_zfmisc_1(u1_struct_0(D_312), A_313)) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_312)), A_313) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_312))) | ~m1_pre_topc(D_312, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_753])).
% 6.06/2.15  tff(c_125, plain, (![A_1, B_97, A_98]: (v5_relat_1(A_1, B_97) | ~r1_tarski(A_1, k2_zfmisc_1(A_98, B_97)))), inference(resolution, [status(thm)], [c_4, c_116])).
% 6.06/2.15  tff(c_1060, plain, (![D_314, A_315]: (v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_314), A_315) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_314)), A_315) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_314))) | ~m1_pre_topc(D_314, '#skF_1'))), inference(resolution, [status(thm)], [c_1024, c_125])).
% 6.06/2.15  tff(c_1075, plain, (![D_314]: (v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_314), u1_struct_0('#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_314))) | ~m1_pre_topc(D_314, '#skF_1') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0(D_314)), '#skF_4'))), inference(resolution, [status(thm)], [c_258, c_1060])).
% 6.06/2.15  tff(c_522, plain, (![D_203]: (k7_relat_1('#skF_4', u1_struct_0(D_203))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_203) | ~m1_pre_topc(D_203, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_519])).
% 6.06/2.15  tff(c_530, plain, (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_522, c_483])).
% 6.06/2.15  tff(c_559, plain, (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_530])).
% 6.06/2.15  tff(c_533, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_522, c_457])).
% 6.06/2.15  tff(c_561, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_533])).
% 6.06/2.15  tff(c_545, plain, (![D_203]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_203)), u1_struct_0(D_203)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_203, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_522, c_18])).
% 6.06/2.15  tff(c_569, plain, (![D_203]: (r1_tarski(k1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_203)), u1_struct_0(D_203)) | ~m1_pre_topc(D_203, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_545])).
% 6.06/2.15  tff(c_26, plain, (![A_23, B_24, C_25, D_26]: (k8_relset_1(A_23, B_24, C_25, D_26)=k10_relat_1(C_25, D_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.06/2.15  tff(c_691, plain, (![A_229, B_230, C_231, D_232]: (k8_relset_1(A_229, B_230, C_231, D_232)=k10_relat_1(C_231, D_232) | ~r1_tarski(k2_relat_1(C_231), B_230) | ~r1_tarski(k1_relat_1(C_231), A_229) | ~v1_relat_1(C_231))), inference(resolution, [status(thm)], [c_413, c_26])).
% 6.06/2.15  tff(c_699, plain, (![A_237, A_238, B_239, D_240]: (k8_relset_1(A_237, A_238, B_239, D_240)=k10_relat_1(B_239, D_240) | ~r1_tarski(k1_relat_1(B_239), A_237) | ~v5_relat_1(B_239, A_238) | ~v1_relat_1(B_239))), inference(resolution, [status(thm)], [c_12, c_691])).
% 6.06/2.15  tff(c_2354, plain, (![D_524, A_525, D_526]: (k8_relset_1(u1_struct_0(D_524), A_525, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_524), D_526)=k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_524), D_526) | ~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_524), A_525) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_524)) | ~m1_pre_topc(D_524, '#skF_1'))), inference(resolution, [status(thm)], [c_569, c_699])).
% 6.06/2.15  tff(c_36, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.06/2.15  tff(c_308, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_36])).
% 6.06/2.15  tff(c_2360, plain, (k10_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2354, c_308])).
% 6.06/2.15  tff(c_2366, plain, (~v5_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_559, c_561, c_2360])).
% 6.06/2.15  tff(c_2370, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_1') | ~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(resolution, [status(thm)], [c_1075, c_2366])).
% 6.06/2.15  tff(c_2376, plain, (~r1_tarski(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_483, c_2370])).
% 6.06/2.15  tff(c_2383, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2376])).
% 6.06/2.15  tff(c_2389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_2383])).
% 6.06/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.15  
% 6.06/2.15  Inference rules
% 6.06/2.15  ----------------------
% 6.06/2.15  #Ref     : 0
% 6.06/2.15  #Sup     : 527
% 6.06/2.15  #Fact    : 0
% 6.06/2.15  #Define  : 0
% 6.06/2.15  #Split   : 5
% 6.06/2.15  #Chain   : 0
% 6.06/2.15  #Close   : 0
% 6.06/2.15  
% 6.06/2.15  Ordering : KBO
% 6.06/2.15  
% 6.06/2.15  Simplification rules
% 6.06/2.15  ----------------------
% 6.06/2.15  #Subsume      : 102
% 6.06/2.15  #Demod        : 156
% 6.06/2.15  #Tautology    : 80
% 6.06/2.15  #SimpNegUnit  : 12
% 6.06/2.15  #BackRed      : 2
% 6.06/2.15  
% 6.06/2.15  #Partial instantiations: 0
% 6.06/2.15  #Strategies tried      : 1
% 6.06/2.15  
% 6.06/2.15  Timing (in seconds)
% 6.06/2.15  ----------------------
% 6.23/2.16  Preprocessing        : 0.35
% 6.23/2.16  Parsing              : 0.19
% 6.23/2.16  CNF conversion       : 0.03
% 6.23/2.16  Main loop            : 1.05
% 6.23/2.16  Inferencing          : 0.39
% 6.23/2.16  Reduction            : 0.30
% 6.23/2.16  Demodulation         : 0.21
% 6.23/2.16  BG Simplification    : 0.04
% 6.23/2.16  Subsumption          : 0.24
% 6.23/2.16  Abstraction          : 0.06
% 6.23/2.16  MUC search           : 0.00
% 6.23/2.16  Cooper               : 0.00
% 6.23/2.16  Total                : 1.44
% 6.23/2.16  Index Insertion      : 0.00
% 6.23/2.16  Index Deletion       : 0.00
% 6.23/2.16  Index Matching       : 0.00
% 6.23/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
