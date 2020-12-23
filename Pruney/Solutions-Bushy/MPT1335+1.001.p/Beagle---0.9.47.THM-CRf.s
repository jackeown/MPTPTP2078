%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1335+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:49 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 685 expanded)
%              Number of leaves         :   44 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :  292 (3486 expanded)
%              Number of equality atoms :   15 ( 134 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_189,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & l1_pre_topc(C) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ( ( v5_pre_topc(D,A,C)
                            & v5_pre_topc(E,C,B) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(A),u1_struct_0(C),u1_struct_0(C),u1_struct_0(B),D,E),A,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_108,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v1_xboole_0(B)
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & v1_funct_2(E,B,C)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k5_relat_1(D,E))
        & v1_funct_2(k5_relat_1(D,E),A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_70,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_20,plain,(
    ! [A_38] :
      ( l1_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_339,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k8_relset_1(A_165,B_166,C_167,D_168) = k10_relat_1(C_167,D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_397,plain,(
    ! [D_172] : k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_9',D_172) = k10_relat_1('#skF_9',D_172) ),
    inference(resolution,[status(thm)],[c_58,c_339])).

tff(c_18,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( m1_subset_1(k8_relset_1(A_34,B_35,C_36,D_37),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_403,plain,(
    ! [D_172] :
      ( m1_subset_1(k10_relat_1('#skF_9',D_172),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_18])).

tff(c_411,plain,(
    ! [D_173] : m1_subset_1(k10_relat_1('#skF_9',D_173),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_403])).

tff(c_42,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_424,plain,(
    ! [D_173] : r1_tarski(k10_relat_1('#skF_9',D_173),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_411,c_42])).

tff(c_44,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(A_63,k1_zfmisc_1(B_64))
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_66,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_56,plain,(
    v5_pre_topc('#skF_8','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_358,plain,(
    ! [D_168] : k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'),'#skF_8',D_168) = k10_relat_1('#skF_8',D_168) ),
    inference(resolution,[status(thm)],[c_64,c_339])).

tff(c_2592,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_364),u1_struct_0(B_365),C_366,D_367),A_364)
      | ~ v4_pre_topc(D_367,B_365)
      | ~ m1_subset_1(D_367,k1_zfmisc_1(u1_struct_0(B_365)))
      | ~ v5_pre_topc(C_366,A_364,B_365)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_364),u1_struct_0(B_365))))
      | ~ v1_funct_2(C_366,u1_struct_0(A_364),u1_struct_0(B_365))
      | ~ v1_funct_1(C_366)
      | ~ l1_pre_topc(B_365)
      | ~ l1_pre_topc(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2611,plain,(
    ! [D_367] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'),'#skF_8',D_367),'#skF_5')
      | ~ v4_pre_topc(D_367,'#skF_7')
      | ~ m1_subset_1(D_367,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ v5_pre_topc('#skF_8','#skF_5','#skF_7')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_2592])).

tff(c_2678,plain,(
    ! [D_370] :
      ( v4_pre_topc(k10_relat_1('#skF_8',D_370),'#skF_5')
      | ~ v4_pre_topc(D_370,'#skF_7')
      | ~ m1_subset_1(D_370,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_68,c_66,c_56,c_358,c_2611])).

tff(c_2715,plain,(
    ! [A_373] :
      ( v4_pre_topc(k10_relat_1('#skF_8',A_373),'#skF_5')
      | ~ v4_pre_topc(A_373,'#skF_7')
      | ~ r1_tarski(A_373,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2678])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_98,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_98])).

tff(c_38,plain,(
    ! [B_58,C_60,A_57] :
      ( k10_relat_1(k5_relat_1(B_58,C_60),A_57) = k10_relat_1(B_58,k10_relat_1(C_60,A_57))
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_62,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_524,plain,(
    ! [B_194,A_190,C_195,D_193,F_191,E_192] :
      ( k1_partfun1(A_190,B_194,C_195,D_193,E_192,F_191) = k5_relat_1(E_192,F_191)
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(C_195,D_193)))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_537,plain,(
    ! [A_190,B_194,E_192] :
      ( k1_partfun1(A_190,B_194,u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),E_192,'#skF_9') = k5_relat_1(E_192,'#skF_9')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_1(E_192) ) ),
    inference(resolution,[status(thm)],[c_58,c_524])).

tff(c_1036,plain,(
    ! [A_242,B_243,E_244] :
      ( k1_partfun1(A_242,B_243,u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),E_244,'#skF_9') = k5_relat_1(E_244,'#skF_9')
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_537])).

tff(c_1056,plain,
    ( k1_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_8','#skF_9') = k5_relat_1('#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_1036])).

tff(c_1079,plain,(
    k1_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_8','#skF_9') = k5_relat_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1056])).

tff(c_52,plain,(
    ~ v5_pre_topc(k1_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_8','#skF_9'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1085,plain,(
    ~ v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_52])).

tff(c_74,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_434,plain,(
    ! [A_177,B_179,C_178,E_176,D_180,F_175] :
      ( v1_funct_1(k1_partfun1(A_177,B_179,C_178,D_180,E_176,F_175))
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_178,D_180)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_179)))
      | ~ v1_funct_1(E_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_447,plain,(
    ! [A_177,B_179,E_176] :
      ( v1_funct_1(k1_partfun1(A_177,B_179,u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),E_176,'#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_179)))
      | ~ v1_funct_1(E_176) ) ),
    inference(resolution,[status(thm)],[c_58,c_434])).

tff(c_459,plain,(
    ! [A_177,B_179,E_176] :
      ( v1_funct_1(k1_partfun1(A_177,B_179,u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),E_176,'#skF_9'))
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_179)))
      | ~ v1_funct_1(E_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_447])).

tff(c_1092,plain,
    ( v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_459])).

tff(c_1098,plain,(
    v1_funct_1(k5_relat_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1092])).

tff(c_14,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1089,plain,
    ( m1_subset_1(k5_relat_1('#skF_8','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_14])).

tff(c_1096,plain,(
    m1_subset_1(k5_relat_1('#skF_8','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1089])).

tff(c_10,plain,(
    ! [A_6,B_18,C_24] :
      ( v4_pre_topc('#skF_1'(A_6,B_18,C_24),B_18)
      | v5_pre_topc(C_24,A_6,B_18)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6),u1_struct_0(B_18))))
      | ~ v1_funct_2(C_24,u1_struct_0(A_6),u1_struct_0(B_18))
      | ~ v1_funct_1(C_24)
      | ~ l1_pre_topc(B_18)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1104,plain,
    ( v4_pre_topc('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),'#skF_6')
    | v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6')
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1096,c_10])).

tff(c_1135,plain,
    ( v4_pre_topc('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),'#skF_6')
    | v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6')
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1098,c_1104])).

tff(c_1136,plain,
    ( v4_pre_topc('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),'#skF_6')
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_1135])).

tff(c_1431,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1136])).

tff(c_48,plain,(
    ! [C_70,B_69,A_68] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_423,plain,(
    ! [A_68,D_173] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_68,k10_relat_1('#skF_9',D_173)) ) ),
    inference(resolution,[status(thm)],[c_411,c_48])).

tff(c_433,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_60,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1335,plain,(
    ! [A_252,B_251,E_249,C_253,D_250] :
      ( v1_funct_2(k5_relat_1(D_250,E_249),A_252,C_253)
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(B_251,C_253)))
      | ~ v1_funct_2(E_249,B_251,C_253)
      | ~ v1_funct_1(E_249)
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251)))
      | ~ v1_funct_2(D_250,A_252,B_251)
      | ~ v1_funct_1(D_250)
      | v1_xboole_0(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1358,plain,(
    ! [D_250,A_252] :
      ( v1_funct_2(k5_relat_1(D_250,'#skF_9'),A_252,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_252,u1_struct_0('#skF_7'))))
      | ~ v1_funct_2(D_250,A_252,u1_struct_0('#skF_7'))
      | ~ v1_funct_1(D_250)
      | v1_xboole_0(u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_58,c_1335])).

tff(c_1388,plain,(
    ! [D_250,A_252] :
      ( v1_funct_2(k5_relat_1(D_250,'#skF_9'),A_252,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_252,u1_struct_0('#skF_7'))))
      | ~ v1_funct_2(D_250,A_252,u1_struct_0('#skF_7'))
      | ~ v1_funct_1(D_250)
      | v1_xboole_0(u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1358])).

tff(c_2387,plain,(
    ! [D_344,A_345] :
      ( v1_funct_2(k5_relat_1(D_344,'#skF_9'),A_345,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(D_344,k1_zfmisc_1(k2_zfmisc_1(A_345,u1_struct_0('#skF_7'))))
      | ~ v1_funct_2(D_344,A_345,u1_struct_0('#skF_7'))
      | ~ v1_funct_1(D_344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_1388])).

tff(c_2412,plain,
    ( v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_2387])).

tff(c_2433,plain,(
    v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2412])).

tff(c_2435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1431,c_2433])).

tff(c_2437,plain,(
    v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1136])).

tff(c_36,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k8_relset_1(A_53,B_54,C_55,D_56) = k10_relat_1(C_55,D_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1151,plain,(
    ! [D_56] : k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),k5_relat_1('#skF_8','#skF_9'),D_56) = k10_relat_1(k5_relat_1('#skF_8','#skF_9'),D_56) ),
    inference(resolution,[status(thm)],[c_1096,c_36])).

tff(c_2487,plain,(
    ! [A_352,B_353,C_354] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_352),u1_struct_0(B_353),C_354,'#skF_1'(A_352,B_353,C_354)),A_352)
      | v5_pre_topc(C_354,A_352,B_353)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_352),u1_struct_0(B_353))))
      | ~ v1_funct_2(C_354,u1_struct_0(A_352),u1_struct_0(B_353))
      | ~ v1_funct_1(C_354)
      | ~ l1_pre_topc(B_353)
      | ~ l1_pre_topc(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2491,plain,
    ( ~ v4_pre_topc(k10_relat_1(k5_relat_1('#skF_8','#skF_9'),'#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_5')
    | v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6')
    | ~ m1_subset_1(k5_relat_1('#skF_8','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_2487])).

tff(c_2501,plain,
    ( ~ v4_pre_topc(k10_relat_1(k5_relat_1('#skF_8','#skF_9'),'#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_5')
    | v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1098,c_2437,c_1096,c_2491])).

tff(c_2502,plain,(
    ~ v4_pre_topc(k10_relat_1(k5_relat_1('#skF_8','#skF_9'),'#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_2501])).

tff(c_2544,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_8',k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')))),'#skF_5')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2502])).

tff(c_2546,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_8',k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')))),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111,c_2544])).

tff(c_2718,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_7')
    | ~ r1_tarski(k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2715,c_2546])).

tff(c_2721,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_2718])).

tff(c_2436,plain,(
    v4_pre_topc('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1136])).

tff(c_1157,plain,(
    ! [A_245,B_246,C_247] :
      ( m1_subset_1('#skF_1'(A_245,B_246,C_247),k1_zfmisc_1(u1_struct_0(B_246)))
      | v5_pre_topc(C_247,A_245,B_246)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245),u1_struct_0(B_246))))
      | ~ v1_funct_2(C_247,u1_struct_0(A_245),u1_struct_0(B_246))
      | ~ v1_funct_1(C_247)
      | ~ l1_pre_topc(B_246)
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1159,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6')
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1096,c_1157])).

tff(c_1185,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v5_pre_topc(k5_relat_1('#skF_8','#skF_9'),'#skF_5','#skF_6')
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1098,c_1159])).

tff(c_1186,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v1_funct_2(k5_relat_1('#skF_8','#skF_9'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_1185])).

tff(c_2440,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_1186])).

tff(c_54,plain,(
    v5_pre_topc('#skF_9','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_360,plain,(
    ! [D_168] : k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_9',D_168) = k10_relat_1('#skF_9',D_168) ),
    inference(resolution,[status(thm)],[c_58,c_339])).

tff(c_2616,plain,(
    ! [D_367] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_9',D_367),'#skF_7')
      | ~ v4_pre_topc(D_367,'#skF_6')
      | ~ m1_subset_1(D_367,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v5_pre_topc('#skF_9','#skF_7','#skF_6')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_2592])).

tff(c_2727,plain,(
    ! [D_375] :
      ( v4_pre_topc(k10_relat_1('#skF_9',D_375),'#skF_7')
      | ~ v4_pre_topc(D_375,'#skF_6')
      | ~ m1_subset_1(D_375,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_62,c_60,c_54,c_360,c_2616])).

tff(c_2730,plain,
    ( v4_pre_topc(k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_7')
    | ~ v4_pre_topc('#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2440,c_2727])).

tff(c_2749,plain,(
    v4_pre_topc(k10_relat_1('#skF_9','#skF_1'('#skF_5','#skF_6',k5_relat_1('#skF_8','#skF_9'))),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_2730])).

tff(c_2751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2721,c_2749])).

tff(c_2753,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_28,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(u1_struct_0(A_41))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2783,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2753,c_28])).

tff(c_2786,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2783])).

tff(c_2789,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_2786])).

tff(c_2793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2789])).

%------------------------------------------------------------------------------
