%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:13 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 299 expanded)
%              Number of leaves         :   39 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  285 (1812 expanded)
%              Number of equality atoms :   38 ( 124 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_187,negated_conjecture,(
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
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ( r1_tarski(F,u1_struct_0(C))
                               => k7_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k7_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tmap_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_93,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_143,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_60,plain,(
    ! [B_132,A_133] :
      ( l1_pre_topc(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_63])).

tff(c_12,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_28,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_79,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_84,plain,(
    ! [B_137,A_138] :
      ( v2_pre_topc(B_137)
      | ~ m1_pre_topc(B_137,A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_84])).

tff(c_102,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_93])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_128,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k2_partfun1(A_147,B_148,C_149,D_150) = k7_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_funct_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [D_150] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_150) = k7_relat_1('#skF_5',D_150)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_133,plain,(
    ! [D_150] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_150) = k7_relat_1('#skF_5',D_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_130])).

tff(c_198,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k2_partfun1(u1_struct_0(A_166),u1_struct_0(B_167),C_168,u1_struct_0(D_169)) = k2_tmap_1(A_166,B_167,C_168,D_169)
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_pre_topc(B_167)
      | ~ v2_pre_topc(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_202,plain,(
    ! [D_169] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_169)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_169)
      | ~ m1_pre_topc(D_169,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_198])).

tff(c_206,plain,(
    ! [D_169] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_169)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_169)
      | ~ m1_pre_topc(D_169,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_76,c_50,c_48,c_38,c_36,c_133,c_202])).

tff(c_208,plain,(
    ! [D_170] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_170)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_170)
      | ~ m1_pre_topc(D_170,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52,c_206])).

tff(c_2,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_214,plain,(
    ! [D_170,B_4] :
      ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_170),B_4) = k9_relat_1('#skF_5',B_4)
      | ~ r1_tarski(B_4,u1_struct_0(D_170))
      | ~ v1_relat_1('#skF_5')
      | ~ m1_pre_topc(D_170,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_2])).

tff(c_222,plain,(
    ! [D_171,B_172] :
      ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_171),B_172) = k9_relat_1('#skF_5',B_172)
      | ~ r1_tarski(B_172,u1_struct_0(D_171))
      | ~ m1_pre_topc(D_171,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_214])).

tff(c_225,plain,
    ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k9_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_222])).

tff(c_228,plain,(
    k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_225])).

tff(c_143,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( v1_funct_1(k2_tmap_1(A_152,B_153,C_154,D_155))
      | ~ l1_struct_0(D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152),u1_struct_0(B_153))))
      | ~ v1_funct_2(C_154,u1_struct_0(A_152),u1_struct_0(B_153))
      | ~ v1_funct_1(C_154)
      | ~ l1_struct_0(B_153)
      | ~ l1_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_145,plain,(
    ! [D_155] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_155))
      | ~ l1_struct_0(D_155)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_148,plain,(
    ! [D_155] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_155))
      | ~ l1_struct_0(D_155)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_145])).

tff(c_155,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_158])).

tff(c_164,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_149,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( v1_funct_2(k2_tmap_1(A_156,B_157,C_158,D_159),u1_struct_0(D_159),u1_struct_0(B_157))
      | ~ l1_struct_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0(A_156),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_struct_0(B_157)
      | ~ l1_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_151,plain,(
    ! [D_159] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_159),u1_struct_0(D_159),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_159)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_154,plain,(
    ! [D_159] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_159),u1_struct_0(D_159),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_159)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_151])).

tff(c_166,plain,(
    ! [D_159] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_159),u1_struct_0(D_159),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_159)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_154])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_170])).

tff(c_176,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_181,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( m1_subset_1(k2_tmap_1(A_162,B_163,C_164,D_165),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_165),u1_struct_0(B_163))))
      | ~ l1_struct_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(B_163))))
      | ~ v1_funct_2(C_164,u1_struct_0(A_162),u1_struct_0(B_163))
      | ~ v1_funct_1(C_164)
      | ~ l1_struct_0(B_163)
      | ~ l1_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_328,plain,(
    ! [C_190,D_187,A_188,D_189,B_186] :
      ( k7_relset_1(u1_struct_0(D_187),u1_struct_0(B_186),k2_tmap_1(A_188,B_186,C_190,D_187),D_189) = k9_relat_1(k2_tmap_1(A_188,B_186,C_190,D_187),D_189)
      | ~ l1_struct_0(D_187)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0(B_186))))
      | ~ v1_funct_2(C_190,u1_struct_0(A_188),u1_struct_0(B_186))
      | ~ v1_funct_1(C_190)
      | ~ l1_struct_0(B_186)
      | ~ l1_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_181,c_6])).

tff(c_332,plain,(
    ! [D_187,D_189] :
      ( k7_relset_1(u1_struct_0(D_187),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_187),D_189) = k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_187),D_189)
      | ~ l1_struct_0(D_187)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_328])).

tff(c_337,plain,(
    ! [D_191,D_192] :
      ( k7_relset_1(u1_struct_0(D_191),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_191),D_192) = k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_191),D_192)
      | ~ l1_struct_0(D_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_176,c_38,c_36,c_332])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_233,plain,(
    ! [D_173,E_177,A_174,C_175,B_176] :
      ( k3_tmap_1(A_174,B_176,C_175,D_173,E_177) = k2_partfun1(u1_struct_0(C_175),u1_struct_0(B_176),E_177,u1_struct_0(D_173))
      | ~ m1_pre_topc(D_173,C_175)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(E_177,u1_struct_0(C_175),u1_struct_0(B_176))
      | ~ v1_funct_1(E_177)
      | ~ m1_pre_topc(D_173,A_174)
      | ~ m1_pre_topc(C_175,A_174)
      | ~ l1_pre_topc(B_176)
      | ~ v2_pre_topc(B_176)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_237,plain,(
    ! [A_174,D_173] :
      ( k3_tmap_1(A_174,'#skF_2','#skF_4',D_173,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_173))
      | ~ m1_pre_topc(D_173,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_173,A_174)
      | ~ m1_pre_topc('#skF_4',A_174)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_34,c_233])).

tff(c_241,plain,(
    ! [D_173,A_174] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_173)) = k3_tmap_1(A_174,'#skF_2','#skF_4',D_173,'#skF_5')
      | ~ m1_pre_topc(D_173,'#skF_4')
      | ~ m1_pre_topc(D_173,A_174)
      | ~ m1_pre_topc('#skF_4',A_174)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_36,c_133,c_237])).

tff(c_243,plain,(
    ! [D_178,A_179] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_178)) = k3_tmap_1(A_179,'#skF_2','#skF_4',D_178,'#skF_5')
      | ~ m1_pre_topc(D_178,'#skF_4')
      | ~ m1_pre_topc(D_178,A_179)
      | ~ m1_pre_topc('#skF_4',A_179)
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_241])).

tff(c_245,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_243])).

tff(c_252,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_32,c_245])).

tff(c_253,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_252])).

tff(c_207,plain,(
    ! [D_169] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_169)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_169)
      | ~ m1_pre_topc(D_169,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_52,c_206])).

tff(c_265,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_207])).

tff(c_275,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_265])).

tff(c_114,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k7_relset_1(A_142,B_143,C_144,D_145) = k9_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_117,plain,(
    ! [D_145] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_145) = k9_relat_1('#skF_5',D_145) ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_26,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_118,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_26])).

tff(c_282,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_118])).

tff(c_343,plain,
    ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k9_relat_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_282])).

tff(c_349,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_343])).

tff(c_362,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_349])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.48  
% 2.99/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.48  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.99/1.48  
% 2.99/1.48  %Foreground sorts:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Background operators:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Foreground operators:
% 2.99/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.99/1.48  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.99/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.99/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.99/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.99/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.99/1.48  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.99/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.99/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.99/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.48  
% 3.07/1.50  tff(f_187, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tmap_1)).
% 3.07/1.50  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.07/1.50  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.07/1.50  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.50  tff(f_55, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.07/1.50  tff(f_46, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.07/1.50  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.07/1.50  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 3.07/1.50  tff(f_143, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.07/1.50  tff(f_40, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.07/1.50  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.07/1.50  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_60, plain, (![B_132, A_133]: (l1_pre_topc(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.07/1.50  tff(c_63, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_60])).
% 3.07/1.50  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_63])).
% 3.07/1.50  tff(c_12, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.50  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_28, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_79, plain, (![C_134, A_135, B_136]: (v1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.50  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_79])).
% 3.07/1.50  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_84, plain, (![B_137, A_138]: (v2_pre_topc(B_137) | ~m1_pre_topc(B_137, A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.07/1.50  tff(c_93, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_84])).
% 3.07/1.50  tff(c_102, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_93])).
% 3.07/1.50  tff(c_69, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_60])).
% 3.07/1.50  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69])).
% 3.07/1.50  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_36, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_128, plain, (![A_147, B_148, C_149, D_150]: (k2_partfun1(A_147, B_148, C_149, D_150)=k7_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_funct_1(C_149))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_130, plain, (![D_150]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_150)=k7_relat_1('#skF_5', D_150) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_128])).
% 3.07/1.50  tff(c_133, plain, (![D_150]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_150)=k7_relat_1('#skF_5', D_150))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_130])).
% 3.07/1.50  tff(c_198, plain, (![A_166, B_167, C_168, D_169]: (k2_partfun1(u1_struct_0(A_166), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1(A_166, B_167, C_168, D_169) | ~m1_pre_topc(D_169, A_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.50  tff(c_202, plain, (![D_169]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_169))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_169) | ~m1_pre_topc(D_169, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_198])).
% 3.07/1.50  tff(c_206, plain, (![D_169]: (k7_relat_1('#skF_5', u1_struct_0(D_169))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_169) | ~m1_pre_topc(D_169, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_76, c_50, c_48, c_38, c_36, c_133, c_202])).
% 3.07/1.50  tff(c_208, plain, (![D_170]: (k7_relat_1('#skF_5', u1_struct_0(D_170))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_170) | ~m1_pre_topc(D_170, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_52, c_206])).
% 3.07/1.50  tff(c_2, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_214, plain, (![D_170, B_4]: (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_170), B_4)=k9_relat_1('#skF_5', B_4) | ~r1_tarski(B_4, u1_struct_0(D_170)) | ~v1_relat_1('#skF_5') | ~m1_pre_topc(D_170, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_2])).
% 3.07/1.50  tff(c_222, plain, (![D_171, B_172]: (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_171), B_172)=k9_relat_1('#skF_5', B_172) | ~r1_tarski(B_172, u1_struct_0(D_171)) | ~m1_pre_topc(D_171, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_214])).
% 3.07/1.50  tff(c_225, plain, (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_222])).
% 3.07/1.50  tff(c_228, plain, (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_225])).
% 3.07/1.50  tff(c_143, plain, (![A_152, B_153, C_154, D_155]: (v1_funct_1(k2_tmap_1(A_152, B_153, C_154, D_155)) | ~l1_struct_0(D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152), u1_struct_0(B_153)))) | ~v1_funct_2(C_154, u1_struct_0(A_152), u1_struct_0(B_153)) | ~v1_funct_1(C_154) | ~l1_struct_0(B_153) | ~l1_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.07/1.50  tff(c_145, plain, (![D_155]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_155)) | ~l1_struct_0(D_155) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_143])).
% 3.07/1.50  tff(c_148, plain, (![D_155]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_155)) | ~l1_struct_0(D_155) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_145])).
% 3.07/1.50  tff(c_155, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_148])).
% 3.07/1.50  tff(c_158, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_155])).
% 3.07/1.50  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_158])).
% 3.07/1.50  tff(c_164, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_148])).
% 3.07/1.50  tff(c_149, plain, (![A_156, B_157, C_158, D_159]: (v1_funct_2(k2_tmap_1(A_156, B_157, C_158, D_159), u1_struct_0(D_159), u1_struct_0(B_157)) | ~l1_struct_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0(A_156), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_struct_0(B_157) | ~l1_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.07/1.50  tff(c_151, plain, (![D_159]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_159), u1_struct_0(D_159), u1_struct_0('#skF_2')) | ~l1_struct_0(D_159) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_149])).
% 3.07/1.50  tff(c_154, plain, (![D_159]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_159), u1_struct_0(D_159), u1_struct_0('#skF_2')) | ~l1_struct_0(D_159) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_151])).
% 3.07/1.50  tff(c_166, plain, (![D_159]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_159), u1_struct_0(D_159), u1_struct_0('#skF_2')) | ~l1_struct_0(D_159) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_154])).
% 3.07/1.50  tff(c_167, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_166])).
% 3.07/1.50  tff(c_170, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_167])).
% 3.07/1.50  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_170])).
% 3.07/1.50  tff(c_176, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_166])).
% 3.07/1.50  tff(c_181, plain, (![A_162, B_163, C_164, D_165]: (m1_subset_1(k2_tmap_1(A_162, B_163, C_164, D_165), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_165), u1_struct_0(B_163)))) | ~l1_struct_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162), u1_struct_0(B_163)))) | ~v1_funct_2(C_164, u1_struct_0(A_162), u1_struct_0(B_163)) | ~v1_funct_1(C_164) | ~l1_struct_0(B_163) | ~l1_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.07/1.50  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.50  tff(c_328, plain, (![C_190, D_187, A_188, D_189, B_186]: (k7_relset_1(u1_struct_0(D_187), u1_struct_0(B_186), k2_tmap_1(A_188, B_186, C_190, D_187), D_189)=k9_relat_1(k2_tmap_1(A_188, B_186, C_190, D_187), D_189) | ~l1_struct_0(D_187) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), u1_struct_0(B_186)))) | ~v1_funct_2(C_190, u1_struct_0(A_188), u1_struct_0(B_186)) | ~v1_funct_1(C_190) | ~l1_struct_0(B_186) | ~l1_struct_0(A_188))), inference(resolution, [status(thm)], [c_181, c_6])).
% 3.07/1.50  tff(c_332, plain, (![D_187, D_189]: (k7_relset_1(u1_struct_0(D_187), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_187), D_189)=k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_187), D_189) | ~l1_struct_0(D_187) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_328])).
% 3.07/1.50  tff(c_337, plain, (![D_191, D_192]: (k7_relset_1(u1_struct_0(D_191), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_191), D_192)=k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_191), D_192) | ~l1_struct_0(D_191))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_176, c_38, c_36, c_332])).
% 3.07/1.50  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_233, plain, (![D_173, E_177, A_174, C_175, B_176]: (k3_tmap_1(A_174, B_176, C_175, D_173, E_177)=k2_partfun1(u1_struct_0(C_175), u1_struct_0(B_176), E_177, u1_struct_0(D_173)) | ~m1_pre_topc(D_173, C_175) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_175), u1_struct_0(B_176)))) | ~v1_funct_2(E_177, u1_struct_0(C_175), u1_struct_0(B_176)) | ~v1_funct_1(E_177) | ~m1_pre_topc(D_173, A_174) | ~m1_pre_topc(C_175, A_174) | ~l1_pre_topc(B_176) | ~v2_pre_topc(B_176) | v2_struct_0(B_176) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.07/1.50  tff(c_237, plain, (![A_174, D_173]: (k3_tmap_1(A_174, '#skF_2', '#skF_4', D_173, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_173)) | ~m1_pre_topc(D_173, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_173, A_174) | ~m1_pre_topc('#skF_4', A_174) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(resolution, [status(thm)], [c_34, c_233])).
% 3.07/1.50  tff(c_241, plain, (![D_173, A_174]: (k7_relat_1('#skF_5', u1_struct_0(D_173))=k3_tmap_1(A_174, '#skF_2', '#skF_4', D_173, '#skF_5') | ~m1_pre_topc(D_173, '#skF_4') | ~m1_pre_topc(D_173, A_174) | ~m1_pre_topc('#skF_4', A_174) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_36, c_133, c_237])).
% 3.07/1.50  tff(c_243, plain, (![D_178, A_179]: (k7_relat_1('#skF_5', u1_struct_0(D_178))=k3_tmap_1(A_179, '#skF_2', '#skF_4', D_178, '#skF_5') | ~m1_pre_topc(D_178, '#skF_4') | ~m1_pre_topc(D_178, A_179) | ~m1_pre_topc('#skF_4', A_179) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(negUnitSimplification, [status(thm)], [c_52, c_241])).
% 3.07/1.50  tff(c_245, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_243])).
% 3.07/1.50  tff(c_252, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_32, c_245])).
% 3.07/1.50  tff(c_253, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_252])).
% 3.07/1.50  tff(c_207, plain, (![D_169]: (k7_relat_1('#skF_5', u1_struct_0(D_169))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_169) | ~m1_pre_topc(D_169, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_52, c_206])).
% 3.07/1.50  tff(c_265, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_253, c_207])).
% 3.07/1.50  tff(c_275, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_265])).
% 3.07/1.50  tff(c_114, plain, (![A_142, B_143, C_144, D_145]: (k7_relset_1(A_142, B_143, C_144, D_145)=k9_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.50  tff(c_117, plain, (![D_145]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_145)=k9_relat_1('#skF_5', D_145))), inference(resolution, [status(thm)], [c_34, c_114])).
% 3.07/1.50  tff(c_26, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_187])).
% 3.07/1.50  tff(c_118, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_26])).
% 3.07/1.50  tff(c_282, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_118])).
% 3.07/1.50  tff(c_343, plain, (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_337, c_282])).
% 3.07/1.50  tff(c_349, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_343])).
% 3.07/1.50  tff(c_362, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_349])).
% 3.07/1.50  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_362])).
% 3.07/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  Inference rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Ref     : 0
% 3.07/1.50  #Sup     : 60
% 3.07/1.50  #Fact    : 0
% 3.07/1.50  #Define  : 0
% 3.07/1.50  #Split   : 3
% 3.07/1.50  #Chain   : 0
% 3.07/1.50  #Close   : 0
% 3.07/1.50  
% 3.07/1.50  Ordering : KBO
% 3.07/1.50  
% 3.07/1.50  Simplification rules
% 3.07/1.50  ----------------------
% 3.07/1.51  #Subsume      : 2
% 3.07/1.51  #Demod        : 71
% 3.07/1.51  #Tautology    : 24
% 3.07/1.51  #SimpNegUnit  : 5
% 3.07/1.51  #BackRed      : 3
% 3.07/1.51  
% 3.07/1.51  #Partial instantiations: 0
% 3.07/1.51  #Strategies tried      : 1
% 3.07/1.51  
% 3.07/1.51  Timing (in seconds)
% 3.07/1.51  ----------------------
% 3.07/1.51  Preprocessing        : 0.37
% 3.07/1.51  Parsing              : 0.20
% 3.07/1.51  CNF conversion       : 0.04
% 3.07/1.51  Main loop            : 0.35
% 3.07/1.51  Inferencing          : 0.14
% 3.07/1.51  Reduction            : 0.10
% 3.07/1.51  Demodulation         : 0.07
% 3.07/1.51  BG Simplification    : 0.02
% 3.07/1.51  Subsumption          : 0.05
% 3.07/1.51  Abstraction          : 0.02
% 3.07/1.51  MUC search           : 0.00
% 3.07/1.51  Cooper               : 0.00
% 3.07/1.51  Total                : 0.77
% 3.07/1.51  Index Insertion      : 0.00
% 3.07/1.51  Index Deletion       : 0.00
% 3.07/1.51  Index Matching       : 0.00
% 3.07/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
