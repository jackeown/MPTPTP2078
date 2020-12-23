%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 291 expanded)
%              Number of leaves         :   40 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 (1391 expanded)
%              Number of equality atoms :   33 ( 147 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_148,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_112,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_30,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_103,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_187,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k2_partfun1(A_115,B_116,C_117,D_118) = k7_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_189,plain,(
    ! [D_118] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_118) = k7_relat_1('#skF_4',D_118)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_195,plain,(
    ! [D_118] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_118) = k7_relat_1('#skF_4',D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_189])).

tff(c_261,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k2_partfun1(u1_struct_0(A_135),u1_struct_0(B_136),C_137,u1_struct_0(D_138)) = k2_tmap_1(A_135,B_136,C_137,D_138)
      | ~ m1_pre_topc(D_138,A_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_137,u1_struct_0(A_135),u1_struct_0(B_136))
      | ~ v1_funct_1(C_137)
      | ~ l1_pre_topc(B_136)
      | ~ v2_pre_topc(B_136)
      | v2_struct_0(B_136)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_266,plain,(
    ! [D_138] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_138)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_261])).

tff(c_273,plain,(
    ! [D_138] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_138)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_52,c_50,c_38,c_36,c_195,c_266])).

tff(c_276,plain,(
    ! [D_139] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_139)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_139)
      | ~ m1_pre_topc(D_139,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_273])).

tff(c_10,plain,(
    ! [A_8,C_12,B_11] :
      ( k9_relat_1(k7_relat_1(A_8,C_12),B_11) = k9_relat_1(A_8,B_11)
      | ~ r1_tarski(B_11,C_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_282,plain,(
    ! [D_139,B_11] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_139),B_11) = k9_relat_1('#skF_4',B_11)
      | ~ r1_tarski(B_11,u1_struct_0(D_139))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_139,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_10])).

tff(c_371,plain,(
    ! [D_150,B_151] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_150),B_151) = k9_relat_1('#skF_4',B_151)
      | ~ r1_tarski(B_151,u1_struct_0(D_150))
      | ~ m1_pre_topc(D_150,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_282])).

tff(c_398,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_371])).

tff(c_408,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_398])).

tff(c_274,plain,(
    ! [D_138] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_138)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_138)
      | ~ m1_pre_topc(D_138,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_273])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    ! [A_84,B_85] :
      ( v1_relat_1(A_84)
      | ~ v1_relat_1(B_85)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_94,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_156,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k7_relset_1(A_106,B_107,C_108,D_109) = k9_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_162,plain,(
    ! [D_109] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_109) = k9_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_34,c_156])).

tff(c_242,plain,(
    ! [A_130,B_131,D_132,C_133] :
      ( r1_tarski(k7_relset_1(A_130,B_131,D_132,C_133),B_131)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(D_132,A_130,B_131)
      | ~ v1_funct_1(D_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_246,plain,(
    ! [C_133] :
      ( r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',C_133),u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_242])).

tff(c_253,plain,(
    ! [C_133] : r1_tarski(k9_relat_1('#skF_4',C_133),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_162,c_246])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_220,plain,(
    ! [C_124,A_125,B_126] :
      ( m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ r1_tarski(k2_relat_1(C_124),B_126)
      | ~ r1_tarski(k1_relat_1(C_124),A_125)
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_239,plain,(
    ! [C_127,A_128,B_129] :
      ( r1_tarski(C_127,k2_zfmisc_1(A_128,B_129))
      | ~ r1_tarski(k2_relat_1(C_127),B_129)
      | ~ r1_tarski(k1_relat_1(C_127),A_128)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_610,plain,(
    ! [B_192,A_193,A_194,B_195] :
      ( r1_tarski(k7_relat_1(B_192,A_193),k2_zfmisc_1(A_194,B_195))
      | ~ r1_tarski(k9_relat_1(B_192,A_193),B_195)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_192,A_193)),A_194)
      | ~ v1_relat_1(k7_relat_1(B_192,A_193))
      | ~ v1_relat_1(B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_239])).

tff(c_618,plain,(
    ! [B_196,A_197,B_198] :
      ( r1_tarski(k7_relat_1(B_196,A_197),k2_zfmisc_1(A_197,B_198))
      | ~ r1_tarski(k9_relat_1(B_196,A_197),B_198)
      | ~ v1_relat_1(k7_relat_1(B_196,A_197))
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_12,c_610])).

tff(c_163,plain,(
    ! [A_106,B_107,A_1,D_109] :
      ( k7_relset_1(A_106,B_107,A_1,D_109) = k9_relat_1(A_1,D_109)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_649,plain,(
    ! [A_199,B_200,B_201,D_202] :
      ( k7_relset_1(A_199,B_200,k7_relat_1(B_201,A_199),D_202) = k9_relat_1(k7_relat_1(B_201,A_199),D_202)
      | ~ r1_tarski(k9_relat_1(B_201,A_199),B_200)
      | ~ v1_relat_1(k7_relat_1(B_201,A_199))
      | ~ v1_relat_1(B_201) ) ),
    inference(resolution,[status(thm)],[c_618,c_163])).

tff(c_665,plain,(
    ! [C_133,D_202] :
      ( k7_relset_1(C_133,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',C_133),D_202) = k9_relat_1(k7_relat_1('#skF_4',C_133),D_202)
      | ~ v1_relat_1(k7_relat_1('#skF_4',C_133))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_253,c_649])).

tff(c_675,plain,(
    ! [C_203,D_204] :
      ( k7_relset_1(C_203,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',C_203),D_204) = k9_relat_1(k7_relat_1('#skF_4',C_203),D_204)
      | ~ v1_relat_1(k7_relat_1('#skF_4',C_203)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_665])).

tff(c_748,plain,(
    ! [D_215,D_216] :
      ( k7_relset_1(u1_struct_0(D_215),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_215),D_216) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_215)),D_216)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_215)))
      | ~ m1_pre_topc(D_215,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_675])).

tff(c_28,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_164,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_28])).

tff(c_760,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_164])).

tff(c_766,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_760])).

tff(c_768,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_803,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_768])).

tff(c_809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_803])).

tff(c_810,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_819,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_810])).

tff(c_825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_408,c_819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.59  
% 3.47/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.59  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.47/1.59  
% 3.47/1.59  %Foreground sorts:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Background operators:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Foreground operators:
% 3.47/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.47/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.47/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.59  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.47/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.47/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.47/1.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.47/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.47/1.59  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.47/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.59  
% 3.47/1.61  tff(f_148, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.47/1.61  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.47/1.61  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.47/1.61  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.47/1.61  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 3.47/1.61  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.47/1.61  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.47/1.61  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.61  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.47/1.61  tff(f_85, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 3.47/1.61  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.47/1.61  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.47/1.61  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.47/1.61  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_30, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_103, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.61  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_103])).
% 3.47/1.61  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_187, plain, (![A_115, B_116, C_117, D_118]: (k2_partfun1(A_115, B_116, C_117, D_118)=k7_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.47/1.61  tff(c_189, plain, (![D_118]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_118)=k7_relat_1('#skF_4', D_118) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_187])).
% 3.47/1.61  tff(c_195, plain, (![D_118]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_118)=k7_relat_1('#skF_4', D_118))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_189])).
% 3.47/1.61  tff(c_261, plain, (![A_135, B_136, C_137, D_138]: (k2_partfun1(u1_struct_0(A_135), u1_struct_0(B_136), C_137, u1_struct_0(D_138))=k2_tmap_1(A_135, B_136, C_137, D_138) | ~m1_pre_topc(D_138, A_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135), u1_struct_0(B_136)))) | ~v1_funct_2(C_137, u1_struct_0(A_135), u1_struct_0(B_136)) | ~v1_funct_1(C_137) | ~l1_pre_topc(B_136) | ~v2_pre_topc(B_136) | v2_struct_0(B_136) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.47/1.61  tff(c_266, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_138))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_138) | ~m1_pre_topc(D_138, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_261])).
% 3.47/1.61  tff(c_273, plain, (![D_138]: (k7_relat_1('#skF_4', u1_struct_0(D_138))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_138) | ~m1_pre_topc(D_138, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_52, c_50, c_38, c_36, c_195, c_266])).
% 3.47/1.61  tff(c_276, plain, (![D_139]: (k7_relat_1('#skF_4', u1_struct_0(D_139))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_139) | ~m1_pre_topc(D_139, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_54, c_273])).
% 3.47/1.61  tff(c_10, plain, (![A_8, C_12, B_11]: (k9_relat_1(k7_relat_1(A_8, C_12), B_11)=k9_relat_1(A_8, B_11) | ~r1_tarski(B_11, C_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.47/1.61  tff(c_282, plain, (![D_139, B_11]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_139), B_11)=k9_relat_1('#skF_4', B_11) | ~r1_tarski(B_11, u1_struct_0(D_139)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_139, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_10])).
% 3.47/1.61  tff(c_371, plain, (![D_150, B_151]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_150), B_151)=k9_relat_1('#skF_4', B_151) | ~r1_tarski(B_151, u1_struct_0(D_150)) | ~m1_pre_topc(D_150, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_282])).
% 3.47/1.61  tff(c_398, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_371])).
% 3.47/1.61  tff(c_408, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_398])).
% 3.47/1.61  tff(c_274, plain, (![D_138]: (k7_relat_1('#skF_4', u1_struct_0(D_138))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_138) | ~m1_pre_topc(D_138, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_54, c_273])).
% 3.47/1.61  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.61  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.61  tff(c_66, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.47/1.61  tff(c_84, plain, (![A_84, B_85]: (v1_relat_1(A_84) | ~v1_relat_1(B_85) | ~r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_4, c_66])).
% 3.47/1.61  tff(c_94, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_14, c_84])).
% 3.47/1.61  tff(c_156, plain, (![A_106, B_107, C_108, D_109]: (k7_relset_1(A_106, B_107, C_108, D_109)=k9_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.47/1.61  tff(c_162, plain, (![D_109]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_109)=k9_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_34, c_156])).
% 3.47/1.61  tff(c_242, plain, (![A_130, B_131, D_132, C_133]: (r1_tarski(k7_relset_1(A_130, B_131, D_132, C_133), B_131) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_2(D_132, A_130, B_131) | ~v1_funct_1(D_132))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.47/1.61  tff(c_246, plain, (![C_133]: (r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', C_133), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_242])).
% 3.47/1.61  tff(c_253, plain, (![C_133]: (r1_tarski(k9_relat_1('#skF_4', C_133), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_162, c_246])).
% 3.47/1.61  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.61  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.47/1.61  tff(c_220, plain, (![C_124, A_125, B_126]: (m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~r1_tarski(k2_relat_1(C_124), B_126) | ~r1_tarski(k1_relat_1(C_124), A_125) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.61  tff(c_239, plain, (![C_127, A_128, B_129]: (r1_tarski(C_127, k2_zfmisc_1(A_128, B_129)) | ~r1_tarski(k2_relat_1(C_127), B_129) | ~r1_tarski(k1_relat_1(C_127), A_128) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_220, c_2])).
% 3.47/1.61  tff(c_610, plain, (![B_192, A_193, A_194, B_195]: (r1_tarski(k7_relat_1(B_192, A_193), k2_zfmisc_1(A_194, B_195)) | ~r1_tarski(k9_relat_1(B_192, A_193), B_195) | ~r1_tarski(k1_relat_1(k7_relat_1(B_192, A_193)), A_194) | ~v1_relat_1(k7_relat_1(B_192, A_193)) | ~v1_relat_1(B_192))), inference(superposition, [status(thm), theory('equality')], [c_8, c_239])).
% 3.47/1.61  tff(c_618, plain, (![B_196, A_197, B_198]: (r1_tarski(k7_relat_1(B_196, A_197), k2_zfmisc_1(A_197, B_198)) | ~r1_tarski(k9_relat_1(B_196, A_197), B_198) | ~v1_relat_1(k7_relat_1(B_196, A_197)) | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_12, c_610])).
% 3.47/1.61  tff(c_163, plain, (![A_106, B_107, A_1, D_109]: (k7_relset_1(A_106, B_107, A_1, D_109)=k9_relat_1(A_1, D_109) | ~r1_tarski(A_1, k2_zfmisc_1(A_106, B_107)))), inference(resolution, [status(thm)], [c_4, c_156])).
% 3.47/1.61  tff(c_649, plain, (![A_199, B_200, B_201, D_202]: (k7_relset_1(A_199, B_200, k7_relat_1(B_201, A_199), D_202)=k9_relat_1(k7_relat_1(B_201, A_199), D_202) | ~r1_tarski(k9_relat_1(B_201, A_199), B_200) | ~v1_relat_1(k7_relat_1(B_201, A_199)) | ~v1_relat_1(B_201))), inference(resolution, [status(thm)], [c_618, c_163])).
% 3.47/1.61  tff(c_665, plain, (![C_133, D_202]: (k7_relset_1(C_133, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', C_133), D_202)=k9_relat_1(k7_relat_1('#skF_4', C_133), D_202) | ~v1_relat_1(k7_relat_1('#skF_4', C_133)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_253, c_649])).
% 3.47/1.61  tff(c_675, plain, (![C_203, D_204]: (k7_relset_1(C_203, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', C_203), D_204)=k9_relat_1(k7_relat_1('#skF_4', C_203), D_204) | ~v1_relat_1(k7_relat_1('#skF_4', C_203)))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_665])).
% 3.47/1.61  tff(c_748, plain, (![D_215, D_216]: (k7_relset_1(u1_struct_0(D_215), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_215), D_216)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_215)), D_216) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_215))) | ~m1_pre_topc(D_215, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_675])).
% 3.47/1.61  tff(c_28, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.47/1.61  tff(c_164, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_28])).
% 3.47/1.61  tff(c_760, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_748, c_164])).
% 3.47/1.61  tff(c_766, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_760])).
% 3.47/1.61  tff(c_768, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_766])).
% 3.47/1.61  tff(c_803, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_768])).
% 3.47/1.61  tff(c_809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_803])).
% 3.47/1.61  tff(c_810, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_766])).
% 3.47/1.61  tff(c_819, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_274, c_810])).
% 3.47/1.61  tff(c_825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_408, c_819])).
% 3.47/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  Inference rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Ref     : 0
% 3.47/1.61  #Sup     : 179
% 3.47/1.61  #Fact    : 0
% 3.47/1.61  #Define  : 0
% 3.47/1.61  #Split   : 6
% 3.47/1.61  #Chain   : 0
% 3.47/1.61  #Close   : 0
% 3.47/1.61  
% 3.47/1.61  Ordering : KBO
% 3.47/1.61  
% 3.47/1.61  Simplification rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Subsume      : 16
% 3.47/1.61  #Demod        : 71
% 3.47/1.61  #Tautology    : 48
% 3.47/1.61  #SimpNegUnit  : 4
% 3.47/1.61  #BackRed      : 1
% 3.47/1.61  
% 3.47/1.61  #Partial instantiations: 0
% 3.47/1.61  #Strategies tried      : 1
% 3.47/1.61  
% 3.47/1.61  Timing (in seconds)
% 3.47/1.61  ----------------------
% 3.47/1.61  Preprocessing        : 0.37
% 3.47/1.61  Parsing              : 0.20
% 3.47/1.61  CNF conversion       : 0.03
% 3.47/1.61  Main loop            : 0.44
% 3.47/1.61  Inferencing          : 0.17
% 3.47/1.61  Reduction            : 0.13
% 3.47/1.61  Demodulation         : 0.09
% 3.47/1.62  BG Simplification    : 0.03
% 3.47/1.62  Subsumption          : 0.08
% 3.47/1.62  Abstraction          : 0.03
% 3.47/1.62  MUC search           : 0.00
% 3.47/1.62  Cooper               : 0.00
% 3.47/1.62  Total                : 0.85
% 3.47/1.62  Index Insertion      : 0.00
% 3.47/1.62  Index Deletion       : 0.00
% 3.47/1.62  Index Matching       : 0.00
% 3.47/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
