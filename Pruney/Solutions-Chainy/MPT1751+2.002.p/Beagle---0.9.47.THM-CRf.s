%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:57 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 289 expanded)
%              Number of leaves         :   40 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 (1349 expanded)
%              Number of equality atoms :   36 ( 149 expanded)
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

tff(f_144,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_108,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

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
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_332,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k2_partfun1(A_153,B_154,C_155,D_156) = k7_relat_1(C_155,D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ v1_funct_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_339,plain,(
    ! [D_156] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_156) = k7_relat_1('#skF_4',D_156)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_332])).

tff(c_347,plain,(
    ! [D_156] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_156) = k7_relat_1('#skF_4',D_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_339])).

tff(c_389,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k2_partfun1(u1_struct_0(A_167),u1_struct_0(B_168),C_169,u1_struct_0(D_170)) = k2_tmap_1(A_167,B_168,C_169,D_170)
      | ~ m1_pre_topc(D_170,A_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167),u1_struct_0(B_168))))
      | ~ v1_funct_2(C_169,u1_struct_0(A_167),u1_struct_0(B_168))
      | ~ v1_funct_1(C_169)
      | ~ l1_pre_topc(B_168)
      | ~ v2_pre_topc(B_168)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_397,plain,(
    ! [D_170] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_170)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_170)
      | ~ m1_pre_topc(D_170,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_389])).

tff(c_405,plain,(
    ! [D_170] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_170)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_170)
      | ~ m1_pre_topc(D_170,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_52,c_50,c_38,c_36,c_347,c_397])).

tff(c_408,plain,(
    ! [D_171] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_171)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_171)
      | ~ m1_pre_topc(D_171,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_405])).

tff(c_10,plain,(
    ! [A_8,C_12,B_11] :
      ( k9_relat_1(k7_relat_1(A_8,C_12),B_11) = k9_relat_1(A_8,B_11)
      | ~ r1_tarski(B_11,C_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_414,plain,(
    ! [D_171,B_11] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_171),B_11) = k9_relat_1('#skF_4',B_11)
      | ~ r1_tarski(B_11,u1_struct_0(D_171))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_171,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_10])).

tff(c_498,plain,(
    ! [D_187,B_188] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_187),B_188) = k9_relat_1('#skF_4',B_188)
      | ~ r1_tarski(B_188,u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_414])).

tff(c_525,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_498])).

tff(c_535,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_525])).

tff(c_406,plain,(
    ! [D_170] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_170)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_170)
      | ~ m1_pre_topc(D_170,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_405])).

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

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k7_relset_1(A_123,B_124,C_125,D_126) = k9_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_224,plain,(
    ! [D_126] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_126) = k9_relat_1('#skF_4',D_126) ),
    inference(resolution,[status(thm)],[c_34,c_214])).

tff(c_156,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( m1_subset_1(k7_relset_1(A_106,B_107,C_108,D_109),k1_zfmisc_1(B_107))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( r1_tarski(k7_relset_1(A_110,B_111,C_112,D_113),B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_180,plain,(
    ! [D_113] : r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_113),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_226,plain,(
    ! [D_113] : r1_tarski(k9_relat_1('#skF_4',D_113),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_180])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_247,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ r1_tarski(k2_relat_1(C_128),B_130)
      | ~ r1_tarski(k1_relat_1(C_128),A_129)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( k7_relset_1(A_24,B_25,C_26,D_27) = k9_relat_1(C_26,D_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_473,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k7_relset_1(A_176,B_177,C_178,D_179) = k9_relat_1(C_178,D_179)
      | ~ r1_tarski(k2_relat_1(C_178),B_177)
      | ~ r1_tarski(k1_relat_1(C_178),A_176)
      | ~ v1_relat_1(C_178) ) ),
    inference(resolution,[status(thm)],[c_247,c_20])).

tff(c_1895,plain,(
    ! [D_555,B_552,A_551,B_553,A_554] :
      ( k7_relset_1(A_551,B_552,k7_relat_1(B_553,A_554),D_555) = k9_relat_1(k7_relat_1(B_553,A_554),D_555)
      | ~ r1_tarski(k9_relat_1(B_553,A_554),B_552)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_553,A_554)),A_551)
      | ~ v1_relat_1(k7_relat_1(B_553,A_554))
      | ~ v1_relat_1(B_553) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_473])).

tff(c_1939,plain,(
    ! [A_551,D_113,D_555] :
      ( k7_relset_1(A_551,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_113),D_555) = k9_relat_1(k7_relat_1('#skF_4',D_113),D_555)
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_113)),A_551)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_113))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_226,c_1895])).

tff(c_2016,plain,(
    ! [A_563,D_564,D_565] :
      ( k7_relset_1(A_563,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_564),D_565) = k9_relat_1(k7_relat_1('#skF_4',D_564),D_565)
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_564)),A_563)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_564)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1939])).

tff(c_2021,plain,(
    ! [A_13,D_565] :
      ( k7_relset_1(A_13,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_13),D_565) = k9_relat_1(k7_relat_1('#skF_4',A_13),D_565)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_13))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_2016])).

tff(c_2025,plain,(
    ! [A_566,D_567] :
      ( k7_relset_1(A_566,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_566),D_567) = k9_relat_1(k7_relat_1('#skF_4',A_566),D_567)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_566)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2021])).

tff(c_2202,plain,(
    ! [D_588,D_589] :
      ( k7_relset_1(u1_struct_0(D_588),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_588),D_589) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_588)),D_589)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_588)))
      | ~ m1_pre_topc(D_588,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_2025])).

tff(c_28,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_227,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_28])).

tff(c_2217,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2202,c_227])).

tff(c_2229,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2217])).

tff(c_2231,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2229])).

tff(c_2237,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_2231])).

tff(c_2243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2237])).

tff(c_2244,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2229])).

tff(c_2253,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_2244])).

tff(c_2259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_535,c_2253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.00  
% 5.13/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.01  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.13/2.01  
% 5.13/2.01  %Foreground sorts:
% 5.13/2.01  
% 5.13/2.01  
% 5.13/2.01  %Background operators:
% 5.13/2.01  
% 5.13/2.01  
% 5.13/2.01  %Foreground operators:
% 5.13/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.13/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.13/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/2.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.13/2.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.13/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.13/2.01  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.13/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.13/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.13/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.13/2.01  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.13/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.13/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.13/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.13/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.13/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.13/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/2.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.13/2.01  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.13/2.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.13/2.01  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.13/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.13/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.13/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/2.01  
% 5.13/2.03  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 5.13/2.03  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.13/2.03  tff(f_81, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.13/2.03  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.13/2.03  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 5.13/2.03  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 5.13/2.03  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.13/2.03  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.13/2.03  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.13/2.03  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.13/2.03  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 5.13/2.03  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.13/2.03  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.13/2.03  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_30, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_103, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.13/2.03  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_103])).
% 5.13/2.03  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_332, plain, (![A_153, B_154, C_155, D_156]: (k2_partfun1(A_153, B_154, C_155, D_156)=k7_relat_1(C_155, D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~v1_funct_1(C_155))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.13/2.03  tff(c_339, plain, (![D_156]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_156)=k7_relat_1('#skF_4', D_156) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_332])).
% 5.13/2.03  tff(c_347, plain, (![D_156]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_156)=k7_relat_1('#skF_4', D_156))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_339])).
% 5.13/2.03  tff(c_389, plain, (![A_167, B_168, C_169, D_170]: (k2_partfun1(u1_struct_0(A_167), u1_struct_0(B_168), C_169, u1_struct_0(D_170))=k2_tmap_1(A_167, B_168, C_169, D_170) | ~m1_pre_topc(D_170, A_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167), u1_struct_0(B_168)))) | ~v1_funct_2(C_169, u1_struct_0(A_167), u1_struct_0(B_168)) | ~v1_funct_1(C_169) | ~l1_pre_topc(B_168) | ~v2_pre_topc(B_168) | v2_struct_0(B_168) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.13/2.03  tff(c_397, plain, (![D_170]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_170))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_170) | ~m1_pre_topc(D_170, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_389])).
% 5.13/2.03  tff(c_405, plain, (![D_170]: (k7_relat_1('#skF_4', u1_struct_0(D_170))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_170) | ~m1_pre_topc(D_170, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_52, c_50, c_38, c_36, c_347, c_397])).
% 5.13/2.03  tff(c_408, plain, (![D_171]: (k7_relat_1('#skF_4', u1_struct_0(D_171))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_171) | ~m1_pre_topc(D_171, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_54, c_405])).
% 5.13/2.03  tff(c_10, plain, (![A_8, C_12, B_11]: (k9_relat_1(k7_relat_1(A_8, C_12), B_11)=k9_relat_1(A_8, B_11) | ~r1_tarski(B_11, C_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.13/2.03  tff(c_414, plain, (![D_171, B_11]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_171), B_11)=k9_relat_1('#skF_4', B_11) | ~r1_tarski(B_11, u1_struct_0(D_171)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_171, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_408, c_10])).
% 5.13/2.03  tff(c_498, plain, (![D_187, B_188]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_187), B_188)=k9_relat_1('#skF_4', B_188) | ~r1_tarski(B_188, u1_struct_0(D_187)) | ~m1_pre_topc(D_187, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_414])).
% 5.13/2.03  tff(c_525, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_498])).
% 5.13/2.03  tff(c_535, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_525])).
% 5.13/2.03  tff(c_406, plain, (![D_170]: (k7_relat_1('#skF_4', u1_struct_0(D_170))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_170) | ~m1_pre_topc(D_170, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_54, c_405])).
% 5.13/2.03  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.13/2.03  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.13/2.03  tff(c_66, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.13/2.03  tff(c_84, plain, (![A_84, B_85]: (v1_relat_1(A_84) | ~v1_relat_1(B_85) | ~r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_4, c_66])).
% 5.13/2.03  tff(c_94, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_14, c_84])).
% 5.13/2.03  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.13/2.03  tff(c_214, plain, (![A_123, B_124, C_125, D_126]: (k7_relset_1(A_123, B_124, C_125, D_126)=k9_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.13/2.03  tff(c_224, plain, (![D_126]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_126)=k9_relat_1('#skF_4', D_126))), inference(resolution, [status(thm)], [c_34, c_214])).
% 5.13/2.03  tff(c_156, plain, (![A_106, B_107, C_108, D_109]: (m1_subset_1(k7_relset_1(A_106, B_107, C_108, D_109), k1_zfmisc_1(B_107)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.13/2.03  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.13/2.03  tff(c_170, plain, (![A_110, B_111, C_112, D_113]: (r1_tarski(k7_relset_1(A_110, B_111, C_112, D_113), B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(resolution, [status(thm)], [c_156, c_2])).
% 5.13/2.03  tff(c_180, plain, (![D_113]: (r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_113), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_170])).
% 5.13/2.03  tff(c_226, plain, (![D_113]: (r1_tarski(k9_relat_1('#skF_4', D_113), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_180])).
% 5.13/2.03  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.13/2.03  tff(c_247, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~r1_tarski(k2_relat_1(C_128), B_130) | ~r1_tarski(k1_relat_1(C_128), A_129) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.13/2.03  tff(c_20, plain, (![A_24, B_25, C_26, D_27]: (k7_relset_1(A_24, B_25, C_26, D_27)=k9_relat_1(C_26, D_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.13/2.03  tff(c_473, plain, (![A_176, B_177, C_178, D_179]: (k7_relset_1(A_176, B_177, C_178, D_179)=k9_relat_1(C_178, D_179) | ~r1_tarski(k2_relat_1(C_178), B_177) | ~r1_tarski(k1_relat_1(C_178), A_176) | ~v1_relat_1(C_178))), inference(resolution, [status(thm)], [c_247, c_20])).
% 5.13/2.03  tff(c_1895, plain, (![D_555, B_552, A_551, B_553, A_554]: (k7_relset_1(A_551, B_552, k7_relat_1(B_553, A_554), D_555)=k9_relat_1(k7_relat_1(B_553, A_554), D_555) | ~r1_tarski(k9_relat_1(B_553, A_554), B_552) | ~r1_tarski(k1_relat_1(k7_relat_1(B_553, A_554)), A_551) | ~v1_relat_1(k7_relat_1(B_553, A_554)) | ~v1_relat_1(B_553))), inference(superposition, [status(thm), theory('equality')], [c_8, c_473])).
% 5.13/2.03  tff(c_1939, plain, (![A_551, D_113, D_555]: (k7_relset_1(A_551, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_113), D_555)=k9_relat_1(k7_relat_1('#skF_4', D_113), D_555) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_113)), A_551) | ~v1_relat_1(k7_relat_1('#skF_4', D_113)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_226, c_1895])).
% 5.13/2.03  tff(c_2016, plain, (![A_563, D_564, D_565]: (k7_relset_1(A_563, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_564), D_565)=k9_relat_1(k7_relat_1('#skF_4', D_564), D_565) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_564)), A_563) | ~v1_relat_1(k7_relat_1('#skF_4', D_564)))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1939])).
% 5.13/2.03  tff(c_2021, plain, (![A_13, D_565]: (k7_relset_1(A_13, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_13), D_565)=k9_relat_1(k7_relat_1('#skF_4', A_13), D_565) | ~v1_relat_1(k7_relat_1('#skF_4', A_13)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_2016])).
% 5.13/2.03  tff(c_2025, plain, (![A_566, D_567]: (k7_relset_1(A_566, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_566), D_567)=k9_relat_1(k7_relat_1('#skF_4', A_566), D_567) | ~v1_relat_1(k7_relat_1('#skF_4', A_566)))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2021])).
% 5.13/2.03  tff(c_2202, plain, (![D_588, D_589]: (k7_relset_1(u1_struct_0(D_588), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_588), D_589)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_588)), D_589) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_588))) | ~m1_pre_topc(D_588, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_2025])).
% 5.13/2.03  tff(c_28, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.13/2.03  tff(c_227, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_28])).
% 5.13/2.03  tff(c_2217, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2202, c_227])).
% 5.13/2.03  tff(c_2229, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2217])).
% 5.13/2.03  tff(c_2231, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2229])).
% 5.13/2.03  tff(c_2237, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_2231])).
% 5.13/2.03  tff(c_2243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_2237])).
% 5.13/2.03  tff(c_2244, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2229])).
% 5.13/2.03  tff(c_2253, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_406, c_2244])).
% 5.13/2.03  tff(c_2259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_535, c_2253])).
% 5.13/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.03  
% 5.13/2.03  Inference rules
% 5.13/2.03  ----------------------
% 5.13/2.03  #Ref     : 0
% 5.13/2.03  #Sup     : 535
% 5.13/2.03  #Fact    : 0
% 5.13/2.03  #Define  : 0
% 5.13/2.03  #Split   : 6
% 5.13/2.03  #Chain   : 0
% 5.13/2.03  #Close   : 0
% 5.13/2.03  
% 5.13/2.03  Ordering : KBO
% 5.13/2.03  
% 5.13/2.03  Simplification rules
% 5.13/2.03  ----------------------
% 5.13/2.03  #Subsume      : 83
% 5.13/2.03  #Demod        : 90
% 5.13/2.03  #Tautology    : 58
% 5.13/2.03  #SimpNegUnit  : 4
% 5.13/2.03  #BackRed      : 2
% 5.13/2.03  
% 5.13/2.03  #Partial instantiations: 0
% 5.13/2.03  #Strategies tried      : 1
% 5.13/2.03  
% 5.13/2.03  Timing (in seconds)
% 5.13/2.03  ----------------------
% 5.13/2.03  Preprocessing        : 0.35
% 5.13/2.03  Parsing              : 0.19
% 5.13/2.03  CNF conversion       : 0.02
% 5.13/2.03  Main loop            : 0.85
% 5.13/2.03  Inferencing          : 0.35
% 5.13/2.03  Reduction            : 0.22
% 5.13/2.03  Demodulation         : 0.15
% 5.13/2.03  BG Simplification    : 0.04
% 5.13/2.03  Subsumption          : 0.17
% 5.13/2.03  Abstraction          : 0.06
% 5.13/2.03  MUC search           : 0.00
% 5.13/2.03  Cooper               : 0.00
% 5.13/2.03  Total                : 1.24
% 5.13/2.03  Index Insertion      : 0.00
% 5.13/2.03  Index Deletion       : 0.00
% 5.13/2.03  Index Matching       : 0.00
% 5.13/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
