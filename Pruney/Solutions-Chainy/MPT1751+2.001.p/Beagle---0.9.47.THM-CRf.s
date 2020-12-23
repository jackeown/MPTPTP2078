%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:57 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 349 expanded)
%              Number of leaves         :   42 ( 148 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 (1669 expanded)
%              Number of equality atoms :   40 ( 171 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_156,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_120,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_36,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_18,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_18])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_135,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k2_partfun1(A_118,B_119,C_120,D_121) = k7_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_137,plain,(
    ! [D_121] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_121) = k7_relat_1('#skF_4',D_121)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_135])).

tff(c_140,plain,(
    ! [D_121] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_121) = k7_relat_1('#skF_4',D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_137])).

tff(c_227,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k2_partfun1(u1_struct_0(A_141),u1_struct_0(B_142),C_143,u1_struct_0(D_144)) = k2_tmap_1(A_141,B_142,C_143,D_144)
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,u1_struct_0(A_141),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_235,plain,(
    ! [D_144] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_227])).

tff(c_240,plain,(
    ! [D_144] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58,c_56,c_44,c_42,c_140,c_235])).

tff(c_242,plain,(
    ! [D_145] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_145)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_145)
      | ~ m1_pre_topc(D_145,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_240])).

tff(c_12,plain,(
    ! [A_10,C_14,B_13] :
      ( k9_relat_1(k7_relat_1(A_10,C_14),B_13) = k9_relat_1(A_10,B_13)
      | ~ r1_tarski(B_13,C_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_253,plain,(
    ! [D_145,B_13] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_145),B_13) = k9_relat_1('#skF_4',B_13)
      | ~ r1_tarski(B_13,u1_struct_0(D_145))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_145,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_12])).

tff(c_368,plain,(
    ! [D_169,B_170] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_169),B_170) = k9_relat_1('#skF_4',B_170)
      | ~ r1_tarski(B_170,u1_struct_0(D_169))
      | ~ m1_pre_topc(D_169,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_253])).

tff(c_386,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_368])).

tff(c_393,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_386])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_121,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( m1_subset_1(A_112,k1_zfmisc_1(k2_zfmisc_1(B_113,C_114)))
      | ~ r1_tarski(A_112,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(B_113,C_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_132,plain,(
    ! [B_18,A_17,B_113,C_114] :
      ( m1_subset_1(k7_relat_1(B_18,A_17),k1_zfmisc_1(k2_zfmisc_1(B_113,C_114)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(B_113,C_114)))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_16,c_121])).

tff(c_250,plain,(
    ! [D_145,B_113,C_114] :
      ( m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_145),k1_zfmisc_1(k2_zfmisc_1(B_113,C_114)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_113,C_114)))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_145,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_132])).

tff(c_740,plain,(
    ! [D_289,B_290,C_291] :
      ( m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_289),k1_zfmisc_1(k2_zfmisc_1(B_290,C_291)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_290,C_291)))
      | ~ m1_pre_topc(D_289,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_250])).

tff(c_24,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k7_relset_1(A_25,B_26,C_27,D_28) = k9_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2280,plain,(
    ! [B_712,C_713,D_714,D_715] :
      ( k7_relset_1(B_712,C_713,k2_tmap_1('#skF_2','#skF_1','#skF_4',D_714),D_715) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_714),D_715)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_712,C_713)))
      | ~ m1_pre_topc(D_714,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_740,c_24])).

tff(c_2290,plain,(
    ! [D_716,D_717] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_716),D_717) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_716),D_717)
      | ~ m1_pre_topc(D_716,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_2280])).

tff(c_241,plain,(
    ! [D_144] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_240])).

tff(c_189,plain,(
    ! [B_132,A_133,B_134,C_135] :
      ( m1_subset_1(k7_relat_1(B_132,A_133),k1_zfmisc_1(k2_zfmisc_1(B_134,C_135)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_zfmisc_1(B_134,C_135)))
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_16,c_121])).

tff(c_970,plain,(
    ! [C_345,B_346,D_343,A_344,B_342] :
      ( k7_relset_1(B_346,C_345,k7_relat_1(B_342,A_344),D_343) = k9_relat_1(k7_relat_1(B_342,A_344),D_343)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k2_zfmisc_1(B_346,C_345)))
      | ~ v1_relat_1(B_342) ) ),
    inference(resolution,[status(thm)],[c_189,c_24])).

tff(c_982,plain,(
    ! [A_344,D_343] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_344),D_343) = k9_relat_1(k7_relat_1('#skF_4',A_344),D_343)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_970])).

tff(c_991,plain,(
    ! [A_347,D_348] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_347),D_348) = k9_relat_1(k7_relat_1('#skF_4',A_347),D_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_982])).

tff(c_1000,plain,(
    ! [D_144,D_348] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144),D_348) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_144)),D_348)
      | ~ m1_pre_topc(D_144,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_991])).

tff(c_2296,plain,(
    ! [D_716,D_717] :
      ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_716)),D_717) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_716),D_717)
      | ~ m1_pre_topc(D_716,'#skF_2')
      | ~ m1_pre_topc(D_716,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2290,c_1000])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_214,plain,(
    ! [B_136,A_137,C_138,B_139] :
      ( v5_relat_1(k7_relat_1(B_136,A_137),C_138)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(B_139,C_138)))
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_189,c_20])).

tff(c_220,plain,(
    ! [A_137] :
      ( v5_relat_1(k7_relat_1('#skF_4',A_137),u1_struct_0('#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_214])).

tff(c_225,plain,(
    ! [A_137] : v5_relat_1(k7_relat_1('#skF_4',A_137),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_220])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,(
    ! [C_123,A_124,B_125] :
      ( m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ r1_tarski(k2_relat_1(C_123),B_125)
      | ~ r1_tarski(k1_relat_1(C_123),A_124)
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_523,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k7_relset_1(A_201,B_202,C_203,D_204) = k9_relat_1(C_203,D_204)
      | ~ r1_tarski(k2_relat_1(C_203),B_202)
      | ~ r1_tarski(k1_relat_1(C_203),A_201)
      | ~ v1_relat_1(C_203) ) ),
    inference(resolution,[status(thm)],[c_150,c_24])).

tff(c_563,plain,(
    ! [A_226,A_227,B_228,D_229] :
      ( k7_relset_1(A_226,A_227,B_228,D_229) = k9_relat_1(B_228,D_229)
      | ~ r1_tarski(k1_relat_1(B_228),A_226)
      | ~ v5_relat_1(B_228,A_227)
      | ~ v1_relat_1(B_228) ) ),
    inference(resolution,[status(thm)],[c_6,c_523])).

tff(c_1747,plain,(
    ! [A_579,A_580,B_581,D_582] :
      ( k7_relset_1(A_579,A_580,k7_relat_1(B_581,A_579),D_582) = k9_relat_1(k7_relat_1(B_581,A_579),D_582)
      | ~ v5_relat_1(k7_relat_1(B_581,A_579),A_580)
      | ~ v1_relat_1(k7_relat_1(B_581,A_579))
      | ~ v1_relat_1(B_581) ) ),
    inference(resolution,[status(thm)],[c_14,c_563])).

tff(c_1765,plain,(
    ! [A_137,D_582] :
      ( k7_relset_1(A_137,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_137),D_582) = k9_relat_1(k7_relat_1('#skF_4',A_137),D_582)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_137))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_225,c_1747])).

tff(c_1778,plain,(
    ! [A_583,D_584] :
      ( k7_relset_1(A_583,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_583),D_584) = k9_relat_1(k7_relat_1('#skF_4',A_583),D_584)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_583)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1765])).

tff(c_2761,plain,(
    ! [D_856,D_857] :
      ( k7_relset_1(u1_struct_0(D_856),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_856),D_857) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_856)),D_857)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_856)))
      | ~ m1_pre_topc(D_856,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_1778])).

tff(c_107,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k7_relset_1(A_107,B_108,C_109,D_110) = k9_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,(
    ! [D_110] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_110) = k9_relat_1('#skF_4',D_110) ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_34,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_111,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_34])).

tff(c_2775,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2761,c_111])).

tff(c_2790,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2775])).

tff(c_2830,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2790])).

tff(c_2836,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_2830])).

tff(c_2842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2836])).

tff(c_2843,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2790])).

tff(c_2853,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2296,c_2843])).

tff(c_2862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_393,c_2853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.35  
% 6.64/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.64/2.36  
% 6.64/2.36  %Foreground sorts:
% 6.64/2.36  
% 6.64/2.36  
% 6.64/2.36  %Background operators:
% 6.64/2.36  
% 6.64/2.36  
% 6.64/2.36  %Foreground operators:
% 6.64/2.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.64/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.64/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.64/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.64/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.64/2.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.64/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.64/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.64/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.64/2.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.64/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.64/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.64/2.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.64/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.64/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.64/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.64/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.64/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.64/2.36  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.64/2.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.64/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.64/2.36  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.64/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.64/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.64/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.64/2.36  
% 6.97/2.38  tff(f_156, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 6.97/2.38  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.97/2.38  tff(f_93, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.97/2.38  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.97/2.38  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 6.97/2.38  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.97/2.38  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 6.97/2.38  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.97/2.38  tff(f_42, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.97/2.38  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.97/2.38  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.97/2.38  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.97/2.38  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.97/2.38  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_36, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_18, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.97/2.38  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_18])).
% 6.97/2.38  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_135, plain, (![A_118, B_119, C_120, D_121]: (k2_partfun1(A_118, B_119, C_120, D_121)=k7_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.97/2.38  tff(c_137, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_121)=k7_relat_1('#skF_4', D_121) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_135])).
% 6.97/2.38  tff(c_140, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_121)=k7_relat_1('#skF_4', D_121))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_137])).
% 6.97/2.38  tff(c_227, plain, (![A_141, B_142, C_143, D_144]: (k2_partfun1(u1_struct_0(A_141), u1_struct_0(B_142), C_143, u1_struct_0(D_144))=k2_tmap_1(A_141, B_142, C_143, D_144) | ~m1_pre_topc(D_144, A_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, u1_struct_0(A_141), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.97/2.38  tff(c_235, plain, (![D_144]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_227])).
% 6.97/2.38  tff(c_240, plain, (![D_144]: (k7_relat_1('#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58, c_56, c_44, c_42, c_140, c_235])).
% 6.97/2.38  tff(c_242, plain, (![D_145]: (k7_relat_1('#skF_4', u1_struct_0(D_145))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_145) | ~m1_pre_topc(D_145, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_60, c_240])).
% 6.97/2.38  tff(c_12, plain, (![A_10, C_14, B_13]: (k9_relat_1(k7_relat_1(A_10, C_14), B_13)=k9_relat_1(A_10, B_13) | ~r1_tarski(B_13, C_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.97/2.38  tff(c_253, plain, (![D_145, B_13]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_145), B_13)=k9_relat_1('#skF_4', B_13) | ~r1_tarski(B_13, u1_struct_0(D_145)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_145, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_12])).
% 6.97/2.38  tff(c_368, plain, (![D_169, B_170]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_169), B_170)=k9_relat_1('#skF_4', B_170) | ~r1_tarski(B_170, u1_struct_0(D_169)) | ~m1_pre_topc(D_169, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_253])).
% 6.97/2.38  tff(c_386, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_368])).
% 6.97/2.38  tff(c_393, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_386])).
% 6.97/2.38  tff(c_16, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.97/2.38  tff(c_121, plain, (![A_112, B_113, C_114, D_115]: (m1_subset_1(A_112, k1_zfmisc_1(k2_zfmisc_1(B_113, C_114))) | ~r1_tarski(A_112, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(B_113, C_114))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.97/2.38  tff(c_132, plain, (![B_18, A_17, B_113, C_114]: (m1_subset_1(k7_relat_1(B_18, A_17), k1_zfmisc_1(k2_zfmisc_1(B_113, C_114))) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(B_113, C_114))) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_16, c_121])).
% 6.97/2.38  tff(c_250, plain, (![D_145, B_113, C_114]: (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_145), k1_zfmisc_1(k2_zfmisc_1(B_113, C_114))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_113, C_114))) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_145, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_132])).
% 6.97/2.38  tff(c_740, plain, (![D_289, B_290, C_291]: (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_289), k1_zfmisc_1(k2_zfmisc_1(B_290, C_291))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_290, C_291))) | ~m1_pre_topc(D_289, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_250])).
% 6.97/2.38  tff(c_24, plain, (![A_25, B_26, C_27, D_28]: (k7_relset_1(A_25, B_26, C_27, D_28)=k9_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.97/2.38  tff(c_2280, plain, (![B_712, C_713, D_714, D_715]: (k7_relset_1(B_712, C_713, k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_714), D_715)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_714), D_715) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_712, C_713))) | ~m1_pre_topc(D_714, '#skF_2'))), inference(resolution, [status(thm)], [c_740, c_24])).
% 6.97/2.38  tff(c_2290, plain, (![D_716, D_717]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_716), D_717)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_716), D_717) | ~m1_pre_topc(D_716, '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_2280])).
% 6.97/2.38  tff(c_241, plain, (![D_144]: (k7_relat_1('#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_60, c_240])).
% 6.97/2.38  tff(c_189, plain, (![B_132, A_133, B_134, C_135]: (m1_subset_1(k7_relat_1(B_132, A_133), k1_zfmisc_1(k2_zfmisc_1(B_134, C_135))) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_zfmisc_1(B_134, C_135))) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_16, c_121])).
% 6.97/2.38  tff(c_970, plain, (![C_345, B_346, D_343, A_344, B_342]: (k7_relset_1(B_346, C_345, k7_relat_1(B_342, A_344), D_343)=k9_relat_1(k7_relat_1(B_342, A_344), D_343) | ~m1_subset_1(B_342, k1_zfmisc_1(k2_zfmisc_1(B_346, C_345))) | ~v1_relat_1(B_342))), inference(resolution, [status(thm)], [c_189, c_24])).
% 6.97/2.38  tff(c_982, plain, (![A_344, D_343]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_344), D_343)=k9_relat_1(k7_relat_1('#skF_4', A_344), D_343) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_970])).
% 6.97/2.38  tff(c_991, plain, (![A_347, D_348]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_347), D_348)=k9_relat_1(k7_relat_1('#skF_4', A_347), D_348))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_982])).
% 6.97/2.38  tff(c_1000, plain, (![D_144, D_348]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144), D_348)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_144)), D_348) | ~m1_pre_topc(D_144, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_991])).
% 6.97/2.38  tff(c_2296, plain, (![D_716, D_717]: (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_716)), D_717)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_716), D_717) | ~m1_pre_topc(D_716, '#skF_2') | ~m1_pre_topc(D_716, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2290, c_1000])).
% 6.97/2.38  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.97/2.38  tff(c_20, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.97/2.38  tff(c_214, plain, (![B_136, A_137, C_138, B_139]: (v5_relat_1(k7_relat_1(B_136, A_137), C_138) | ~m1_subset_1(B_136, k1_zfmisc_1(k2_zfmisc_1(B_139, C_138))) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_189, c_20])).
% 6.97/2.38  tff(c_220, plain, (![A_137]: (v5_relat_1(k7_relat_1('#skF_4', A_137), u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_214])).
% 6.97/2.38  tff(c_225, plain, (![A_137]: (v5_relat_1(k7_relat_1('#skF_4', A_137), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_220])).
% 6.97/2.38  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.97/2.38  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.97/2.38  tff(c_150, plain, (![C_123, A_124, B_125]: (m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~r1_tarski(k2_relat_1(C_123), B_125) | ~r1_tarski(k1_relat_1(C_123), A_124) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.97/2.38  tff(c_523, plain, (![A_201, B_202, C_203, D_204]: (k7_relset_1(A_201, B_202, C_203, D_204)=k9_relat_1(C_203, D_204) | ~r1_tarski(k2_relat_1(C_203), B_202) | ~r1_tarski(k1_relat_1(C_203), A_201) | ~v1_relat_1(C_203))), inference(resolution, [status(thm)], [c_150, c_24])).
% 6.97/2.38  tff(c_563, plain, (![A_226, A_227, B_228, D_229]: (k7_relset_1(A_226, A_227, B_228, D_229)=k9_relat_1(B_228, D_229) | ~r1_tarski(k1_relat_1(B_228), A_226) | ~v5_relat_1(B_228, A_227) | ~v1_relat_1(B_228))), inference(resolution, [status(thm)], [c_6, c_523])).
% 6.97/2.38  tff(c_1747, plain, (![A_579, A_580, B_581, D_582]: (k7_relset_1(A_579, A_580, k7_relat_1(B_581, A_579), D_582)=k9_relat_1(k7_relat_1(B_581, A_579), D_582) | ~v5_relat_1(k7_relat_1(B_581, A_579), A_580) | ~v1_relat_1(k7_relat_1(B_581, A_579)) | ~v1_relat_1(B_581))), inference(resolution, [status(thm)], [c_14, c_563])).
% 6.97/2.38  tff(c_1765, plain, (![A_137, D_582]: (k7_relset_1(A_137, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_137), D_582)=k9_relat_1(k7_relat_1('#skF_4', A_137), D_582) | ~v1_relat_1(k7_relat_1('#skF_4', A_137)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_225, c_1747])).
% 6.97/2.38  tff(c_1778, plain, (![A_583, D_584]: (k7_relset_1(A_583, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_583), D_584)=k9_relat_1(k7_relat_1('#skF_4', A_583), D_584) | ~v1_relat_1(k7_relat_1('#skF_4', A_583)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1765])).
% 6.97/2.38  tff(c_2761, plain, (![D_856, D_857]: (k7_relset_1(u1_struct_0(D_856), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_856), D_857)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_856)), D_857) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_856))) | ~m1_pre_topc(D_856, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_1778])).
% 6.97/2.38  tff(c_107, plain, (![A_107, B_108, C_109, D_110]: (k7_relset_1(A_107, B_108, C_109, D_110)=k9_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.97/2.38  tff(c_110, plain, (![D_110]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_110)=k9_relat_1('#skF_4', D_110))), inference(resolution, [status(thm)], [c_40, c_107])).
% 6.97/2.38  tff(c_34, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.97/2.38  tff(c_111, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_34])).
% 6.97/2.38  tff(c_2775, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2761, c_111])).
% 6.97/2.38  tff(c_2790, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2775])).
% 6.97/2.38  tff(c_2830, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2790])).
% 6.97/2.38  tff(c_2836, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_2830])).
% 6.97/2.38  tff(c_2842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2836])).
% 6.97/2.38  tff(c_2843, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2790])).
% 6.97/2.38  tff(c_2853, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2296, c_2843])).
% 6.97/2.38  tff(c_2862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_393, c_2853])).
% 6.97/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.97/2.38  
% 6.97/2.38  Inference rules
% 6.97/2.38  ----------------------
% 6.97/2.38  #Ref     : 0
% 6.97/2.38  #Sup     : 737
% 6.97/2.38  #Fact    : 0
% 6.97/2.38  #Define  : 0
% 6.97/2.38  #Split   : 5
% 6.97/2.38  #Chain   : 0
% 6.97/2.38  #Close   : 0
% 6.97/2.38  
% 6.97/2.38  Ordering : KBO
% 6.97/2.38  
% 6.97/2.38  Simplification rules
% 6.97/2.38  ----------------------
% 6.97/2.38  #Subsume      : 60
% 6.97/2.38  #Demod        : 143
% 6.97/2.38  #Tautology    : 76
% 6.97/2.38  #SimpNegUnit  : 14
% 6.97/2.38  #BackRed      : 1
% 6.97/2.38  
% 6.97/2.38  #Partial instantiations: 0
% 6.97/2.38  #Strategies tried      : 1
% 6.97/2.38  
% 6.97/2.38  Timing (in seconds)
% 6.97/2.38  ----------------------
% 6.97/2.38  Preprocessing        : 0.34
% 6.97/2.38  Parsing              : 0.19
% 6.97/2.38  CNF conversion       : 0.03
% 6.97/2.38  Main loop            : 1.27
% 6.97/2.38  Inferencing          : 0.46
% 6.97/2.38  Reduction            : 0.37
% 6.97/2.38  Demodulation         : 0.24
% 6.97/2.38  BG Simplification    : 0.04
% 6.97/2.38  Subsumption          : 0.29
% 6.97/2.38  Abstraction          : 0.06
% 6.97/2.38  MUC search           : 0.00
% 6.97/2.38  Cooper               : 0.00
% 6.97/2.38  Total                : 1.65
% 6.97/2.38  Index Insertion      : 0.00
% 6.97/2.38  Index Deletion       : 0.00
% 6.97/2.38  Index Matching       : 0.00
% 6.97/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
