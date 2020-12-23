%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 288 expanded)
%              Number of leaves         :   40 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 (1697 expanded)
%              Number of equality atoms :   38 ( 123 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_194,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(D),u1_struct_0(B),E,F),u1_struct_0(C))
                               => k8_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tmap_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_100,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_63,plain,(
    ! [B_136,A_137] :
      ( l1_pre_topc(B_136)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_78,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_14,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_94,plain,(
    ! [B_140,A_141] :
      ( v2_pre_topc(B_140)
      | ~ m1_pre_topc(B_140,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_97,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_94])).

tff(c_106,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_97])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_75,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_129,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k2_partfun1(A_147,B_148,C_149,D_150) = k7_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_funct_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [D_150] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_150) = k7_relat_1('#skF_5',D_150)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_134,plain,(
    ! [D_150] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_150) = k7_relat_1('#skF_5',D_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_131])).

tff(c_505,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k2_partfun1(u1_struct_0(A_241),u1_struct_0(B_242),C_243,u1_struct_0(D_244)) = k2_tmap_1(A_241,B_242,C_243,D_244)
      | ~ m1_pre_topc(D_244,A_241)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241),u1_struct_0(B_242))))
      | ~ v1_funct_2(C_243,u1_struct_0(A_241),u1_struct_0(B_242))
      | ~ v1_funct_1(C_243)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_509,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_244)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244)
      | ~ m1_pre_topc(D_244,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_505])).

tff(c_513,plain,(
    ! [D_244] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_244)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244)
      | ~ m1_pre_topc(D_244,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_75,c_52,c_50,c_40,c_38,c_134,c_509])).

tff(c_515,plain,(
    ! [D_245] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_245)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_245)
      | ~ m1_pre_topc(D_245,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_54,c_513])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_85])).

tff(c_115,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k8_relset_1(A_142,B_143,C_144,D_145) = k10_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_118,plain,(
    ! [D_145] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_145) = k10_relat_1('#skF_5',D_145) ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_30,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_119,plain,(
    r1_tarski(k10_relat_1('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_30])).

tff(c_144,plain,(
    ! [A_152,B_153,C_154] :
      ( k10_relat_1(k7_relat_1(A_152,B_153),C_154) = k10_relat_1(A_152,C_154)
      | ~ r1_tarski(k10_relat_1(A_152,C_154),B_153)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_147,plain,
    ( k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_144])).

tff(c_150,plain,(
    k10_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_40,c_147])).

tff(c_533,plain,
    ( k10_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k10_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_150])).

tff(c_547,plain,(
    k10_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_533])).

tff(c_400,plain,(
    ! [A_212,B_213,C_214,D_215] :
      ( v1_funct_1(k2_tmap_1(A_212,B_213,C_214,D_215))
      | ~ l1_struct_0(D_215)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212),u1_struct_0(B_213))))
      | ~ v1_funct_2(C_214,u1_struct_0(A_212),u1_struct_0(B_213))
      | ~ v1_funct_1(C_214)
      | ~ l1_struct_0(B_213)
      | ~ l1_struct_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_402,plain,(
    ! [D_215] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_215))
      | ~ l1_struct_0(D_215)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_400])).

tff(c_405,plain,(
    ! [D_215] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_215))
      | ~ l1_struct_0(D_215)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_402])).

tff(c_406,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_409,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_406])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_409])).

tff(c_415,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_414,plain,(
    ! [D_215] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_215))
      | ~ l1_struct_0(D_215) ) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_416,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_419,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_416])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_419])).

tff(c_425,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_445,plain,(
    ! [A_222,B_223,C_224,D_225] :
      ( m1_subset_1(k2_tmap_1(A_222,B_223,C_224,D_225),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_225),u1_struct_0(B_223))))
      | ~ l1_struct_0(D_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_222),u1_struct_0(B_223))))
      | ~ v1_funct_2(C_224,u1_struct_0(A_222),u1_struct_0(B_223))
      | ~ v1_funct_1(C_224)
      | ~ l1_struct_0(B_223)
      | ~ l1_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k8_relset_1(A_6,B_7,C_8,D_9) = k10_relat_1(C_8,D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_487,plain,(
    ! [B_237,D_234,C_236,D_235,A_238] :
      ( k8_relset_1(u1_struct_0(D_234),u1_struct_0(B_237),k2_tmap_1(A_238,B_237,C_236,D_234),D_235) = k10_relat_1(k2_tmap_1(A_238,B_237,C_236,D_234),D_235)
      | ~ l1_struct_0(D_234)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_238),u1_struct_0(B_237))))
      | ~ v1_funct_2(C_236,u1_struct_0(A_238),u1_struct_0(B_237))
      | ~ v1_funct_1(C_236)
      | ~ l1_struct_0(B_237)
      | ~ l1_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_445,c_6])).

tff(c_491,plain,(
    ! [D_234,D_235] :
      ( k8_relset_1(u1_struct_0(D_234),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_234),D_235) = k10_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_234),D_235)
      | ~ l1_struct_0(D_234)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_487])).

tff(c_495,plain,(
    ! [D_234,D_235] :
      ( k8_relset_1(u1_struct_0(D_234),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_234),D_235) = k10_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_234),D_235)
      | ~ l1_struct_0(D_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_425,c_40,c_38,c_491])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_549,plain,(
    ! [B_248,C_249,A_246,D_250,E_247] :
      ( k3_tmap_1(A_246,B_248,C_249,D_250,E_247) = k2_partfun1(u1_struct_0(C_249),u1_struct_0(B_248),E_247,u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,C_249)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_249),u1_struct_0(B_248))))
      | ~ v1_funct_2(E_247,u1_struct_0(C_249),u1_struct_0(B_248))
      | ~ v1_funct_1(E_247)
      | ~ m1_pre_topc(D_250,A_246)
      | ~ m1_pre_topc(C_249,A_246)
      | ~ l1_pre_topc(B_248)
      | ~ v2_pre_topc(B_248)
      | v2_struct_0(B_248)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_553,plain,(
    ! [A_246,D_250] :
      ( k3_tmap_1(A_246,'#skF_2','#skF_4',D_250,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_250,A_246)
      | ~ m1_pre_topc('#skF_4',A_246)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_36,c_549])).

tff(c_557,plain,(
    ! [D_250,A_246] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_250)) = k3_tmap_1(A_246,'#skF_2','#skF_4',D_250,'#skF_5')
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ m1_pre_topc(D_250,A_246)
      | ~ m1_pre_topc('#skF_4',A_246)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_134,c_553])).

tff(c_580,plain,(
    ! [D_252,A_253] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_252)) = k3_tmap_1(A_253,'#skF_2','#skF_4',D_252,'#skF_5')
      | ~ m1_pre_topc(D_252,'#skF_4')
      | ~ m1_pre_topc(D_252,A_253)
      | ~ m1_pre_topc('#skF_4',A_253)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_557])).

tff(c_584,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_580])).

tff(c_593,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_34,c_584])).

tff(c_594,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_593])).

tff(c_514,plain,(
    ! [D_244] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_244)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244)
      | ~ m1_pre_topc(D_244,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_54,c_513])).

tff(c_607,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_514])).

tff(c_614,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_607])).

tff(c_28,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_159,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_28])).

tff(c_631,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k10_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_159])).

tff(c_670,plain,
    ( k10_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k10_relat_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_631])).

tff(c_672,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_670])).

tff(c_675,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_672])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:59:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.50  
% 3.40/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.51  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.40/1.51  
% 3.40/1.51  %Foreground sorts:
% 3.40/1.51  
% 3.40/1.51  
% 3.40/1.51  %Background operators:
% 3.40/1.51  
% 3.40/1.51  
% 3.40/1.51  %Foreground operators:
% 3.40/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.40/1.51  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.40/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.40/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.40/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.40/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.40/1.51  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.40/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.40/1.51  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.40/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.40/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.51  
% 3.65/1.53  tff(f_194, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tmap_1)).
% 3.65/1.53  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.65/1.53  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.65/1.53  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.65/1.53  tff(f_44, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.65/1.53  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.65/1.53  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.65/1.53  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.65/1.53  tff(f_38, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.65/1.53  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.65/1.53  tff(f_150, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.65/1.53  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.65/1.53  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_63, plain, (![B_136, A_137]: (l1_pre_topc(B_136) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.65/1.53  tff(c_69, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_63])).
% 3.65/1.53  tff(c_78, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_69])).
% 3.65/1.53  tff(c_14, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.65/1.53  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_94, plain, (![B_140, A_141]: (v2_pre_topc(B_140) | ~m1_pre_topc(B_140, A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.65/1.53  tff(c_97, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_94])).
% 3.65/1.53  tff(c_106, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_97])).
% 3.65/1.53  tff(c_66, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_63])).
% 3.65/1.53  tff(c_75, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66])).
% 3.65/1.53  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_129, plain, (![A_147, B_148, C_149, D_150]: (k2_partfun1(A_147, B_148, C_149, D_150)=k7_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_funct_1(C_149))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.65/1.53  tff(c_131, plain, (![D_150]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_150)=k7_relat_1('#skF_5', D_150) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_129])).
% 3.65/1.53  tff(c_134, plain, (![D_150]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_150)=k7_relat_1('#skF_5', D_150))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_131])).
% 3.65/1.53  tff(c_505, plain, (![A_241, B_242, C_243, D_244]: (k2_partfun1(u1_struct_0(A_241), u1_struct_0(B_242), C_243, u1_struct_0(D_244))=k2_tmap_1(A_241, B_242, C_243, D_244) | ~m1_pre_topc(D_244, A_241) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241), u1_struct_0(B_242)))) | ~v1_funct_2(C_243, u1_struct_0(A_241), u1_struct_0(B_242)) | ~v1_funct_1(C_243) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.53  tff(c_509, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_244))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244) | ~m1_pre_topc(D_244, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_505])).
% 3.65/1.53  tff(c_513, plain, (![D_244]: (k7_relat_1('#skF_5', u1_struct_0(D_244))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244) | ~m1_pre_topc(D_244, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_75, c_52, c_50, c_40, c_38, c_134, c_509])).
% 3.65/1.53  tff(c_515, plain, (![D_245]: (k7_relat_1('#skF_5', u1_struct_0(D_245))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_245) | ~m1_pre_topc(D_245, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_54, c_513])).
% 3.65/1.53  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.65/1.53  tff(c_82, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.65/1.53  tff(c_85, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_82])).
% 3.65/1.53  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_85])).
% 3.65/1.53  tff(c_115, plain, (![A_142, B_143, C_144, D_145]: (k8_relset_1(A_142, B_143, C_144, D_145)=k10_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.65/1.53  tff(c_118, plain, (![D_145]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_145)=k10_relat_1('#skF_5', D_145))), inference(resolution, [status(thm)], [c_36, c_115])).
% 3.65/1.53  tff(c_30, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_119, plain, (r1_tarski(k10_relat_1('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_30])).
% 3.65/1.53  tff(c_144, plain, (![A_152, B_153, C_154]: (k10_relat_1(k7_relat_1(A_152, B_153), C_154)=k10_relat_1(A_152, C_154) | ~r1_tarski(k10_relat_1(A_152, C_154), B_153) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.65/1.53  tff(c_147, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_119, c_144])).
% 3.65/1.53  tff(c_150, plain, (k10_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_40, c_147])).
% 3.65/1.53  tff(c_533, plain, (k10_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k10_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_515, c_150])).
% 3.65/1.53  tff(c_547, plain, (k10_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_533])).
% 3.65/1.53  tff(c_400, plain, (![A_212, B_213, C_214, D_215]: (v1_funct_1(k2_tmap_1(A_212, B_213, C_214, D_215)) | ~l1_struct_0(D_215) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212), u1_struct_0(B_213)))) | ~v1_funct_2(C_214, u1_struct_0(A_212), u1_struct_0(B_213)) | ~v1_funct_1(C_214) | ~l1_struct_0(B_213) | ~l1_struct_0(A_212))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.65/1.53  tff(c_402, plain, (![D_215]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_215)) | ~l1_struct_0(D_215) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_400])).
% 3.65/1.53  tff(c_405, plain, (![D_215]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_215)) | ~l1_struct_0(D_215) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_402])).
% 3.65/1.53  tff(c_406, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_405])).
% 3.65/1.53  tff(c_409, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_406])).
% 3.65/1.53  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_409])).
% 3.65/1.53  tff(c_415, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_405])).
% 3.65/1.53  tff(c_414, plain, (![D_215]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_215)) | ~l1_struct_0(D_215))), inference(splitRight, [status(thm)], [c_405])).
% 3.65/1.53  tff(c_416, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_414])).
% 3.65/1.53  tff(c_419, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_416])).
% 3.65/1.53  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_419])).
% 3.65/1.53  tff(c_425, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_414])).
% 3.65/1.53  tff(c_445, plain, (![A_222, B_223, C_224, D_225]: (m1_subset_1(k2_tmap_1(A_222, B_223, C_224, D_225), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_225), u1_struct_0(B_223)))) | ~l1_struct_0(D_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_222), u1_struct_0(B_223)))) | ~v1_funct_2(C_224, u1_struct_0(A_222), u1_struct_0(B_223)) | ~v1_funct_1(C_224) | ~l1_struct_0(B_223) | ~l1_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.65/1.53  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k8_relset_1(A_6, B_7, C_8, D_9)=k10_relat_1(C_8, D_9) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.65/1.53  tff(c_487, plain, (![B_237, D_234, C_236, D_235, A_238]: (k8_relset_1(u1_struct_0(D_234), u1_struct_0(B_237), k2_tmap_1(A_238, B_237, C_236, D_234), D_235)=k10_relat_1(k2_tmap_1(A_238, B_237, C_236, D_234), D_235) | ~l1_struct_0(D_234) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_238), u1_struct_0(B_237)))) | ~v1_funct_2(C_236, u1_struct_0(A_238), u1_struct_0(B_237)) | ~v1_funct_1(C_236) | ~l1_struct_0(B_237) | ~l1_struct_0(A_238))), inference(resolution, [status(thm)], [c_445, c_6])).
% 3.65/1.53  tff(c_491, plain, (![D_234, D_235]: (k8_relset_1(u1_struct_0(D_234), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_234), D_235)=k10_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_234), D_235) | ~l1_struct_0(D_234) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_487])).
% 3.65/1.53  tff(c_495, plain, (![D_234, D_235]: (k8_relset_1(u1_struct_0(D_234), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_234), D_235)=k10_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_234), D_235) | ~l1_struct_0(D_234))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_425, c_40, c_38, c_491])).
% 3.65/1.53  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_549, plain, (![B_248, C_249, A_246, D_250, E_247]: (k3_tmap_1(A_246, B_248, C_249, D_250, E_247)=k2_partfun1(u1_struct_0(C_249), u1_struct_0(B_248), E_247, u1_struct_0(D_250)) | ~m1_pre_topc(D_250, C_249) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_249), u1_struct_0(B_248)))) | ~v1_funct_2(E_247, u1_struct_0(C_249), u1_struct_0(B_248)) | ~v1_funct_1(E_247) | ~m1_pre_topc(D_250, A_246) | ~m1_pre_topc(C_249, A_246) | ~l1_pre_topc(B_248) | ~v2_pre_topc(B_248) | v2_struct_0(B_248) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.65/1.53  tff(c_553, plain, (![A_246, D_250]: (k3_tmap_1(A_246, '#skF_2', '#skF_4', D_250, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_250, A_246) | ~m1_pre_topc('#skF_4', A_246) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(resolution, [status(thm)], [c_36, c_549])).
% 3.65/1.53  tff(c_557, plain, (![D_250, A_246]: (k7_relat_1('#skF_5', u1_struct_0(D_250))=k3_tmap_1(A_246, '#skF_2', '#skF_4', D_250, '#skF_5') | ~m1_pre_topc(D_250, '#skF_4') | ~m1_pre_topc(D_250, A_246) | ~m1_pre_topc('#skF_4', A_246) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_134, c_553])).
% 3.65/1.53  tff(c_580, plain, (![D_252, A_253]: (k7_relat_1('#skF_5', u1_struct_0(D_252))=k3_tmap_1(A_253, '#skF_2', '#skF_4', D_252, '#skF_5') | ~m1_pre_topc(D_252, '#skF_4') | ~m1_pre_topc(D_252, A_253) | ~m1_pre_topc('#skF_4', A_253) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(negUnitSimplification, [status(thm)], [c_54, c_557])).
% 3.65/1.53  tff(c_584, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_580])).
% 3.65/1.53  tff(c_593, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_34, c_584])).
% 3.65/1.53  tff(c_594, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_593])).
% 3.65/1.53  tff(c_514, plain, (![D_244]: (k7_relat_1('#skF_5', u1_struct_0(D_244))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244) | ~m1_pre_topc(D_244, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_54, c_513])).
% 3.65/1.53  tff(c_607, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_594, c_514])).
% 3.65/1.53  tff(c_614, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_607])).
% 3.65/1.53  tff(c_28, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.65/1.53  tff(c_159, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_28])).
% 3.65/1.53  tff(c_631, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_159])).
% 3.65/1.53  tff(c_670, plain, (k10_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k10_relat_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_495, c_631])).
% 3.65/1.53  tff(c_672, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_670])).
% 3.65/1.53  tff(c_675, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_672])).
% 3.65/1.53  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_675])).
% 3.65/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.53  
% 3.65/1.53  Inference rules
% 3.65/1.53  ----------------------
% 3.65/1.53  #Ref     : 0
% 3.65/1.53  #Sup     : 118
% 3.65/1.53  #Fact    : 0
% 3.65/1.53  #Define  : 0
% 3.65/1.53  #Split   : 12
% 3.65/1.53  #Chain   : 0
% 3.65/1.53  #Close   : 0
% 3.65/1.53  
% 3.65/1.53  Ordering : KBO
% 3.65/1.53  
% 3.65/1.53  Simplification rules
% 3.65/1.53  ----------------------
% 3.65/1.53  #Subsume      : 1
% 3.65/1.53  #Demod        : 151
% 3.65/1.53  #Tautology    : 39
% 3.65/1.53  #SimpNegUnit  : 7
% 3.65/1.53  #BackRed      : 11
% 3.65/1.53  
% 3.65/1.53  #Partial instantiations: 0
% 3.65/1.53  #Strategies tried      : 1
% 3.65/1.53  
% 3.65/1.53  Timing (in seconds)
% 3.65/1.53  ----------------------
% 3.65/1.53  Preprocessing        : 0.39
% 3.65/1.53  Parsing              : 0.21
% 3.65/1.53  CNF conversion       : 0.04
% 3.65/1.53  Main loop            : 0.38
% 3.65/1.53  Inferencing          : 0.13
% 3.65/1.53  Reduction            : 0.12
% 3.65/1.53  Demodulation         : 0.09
% 3.65/1.53  BG Simplification    : 0.02
% 3.65/1.53  Subsumption          : 0.07
% 3.65/1.54  Abstraction          : 0.02
% 3.65/1.54  MUC search           : 0.00
% 3.65/1.54  Cooper               : 0.00
% 3.65/1.54  Total                : 0.81
% 3.65/1.54  Index Insertion      : 0.00
% 3.65/1.54  Index Deletion       : 0.00
% 3.65/1.54  Index Matching       : 0.00
% 3.65/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
