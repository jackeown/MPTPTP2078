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
% DateTime   : Thu Dec  3 10:26:59 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 180 expanded)
%              Number of leaves         :   36 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 872 expanded)
%              Number of equality atoms :   30 (  90 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_129,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_22,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_8])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_92,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k2_partfun1(A_95,B_96,C_97,D_98) = k7_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,(
    ! [D_98] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_97,plain,(
    ! [D_98] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_94])).

tff(c_173,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k2_partfun1(u1_struct_0(A_118),u1_struct_0(B_119),C_120,u1_struct_0(D_121)) = k2_tmap_1(A_118,B_119,C_120,D_121)
      | ~ m1_pre_topc(D_121,A_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118),u1_struct_0(B_119))))
      | ~ v1_funct_2(C_120,u1_struct_0(A_118),u1_struct_0(B_119))
      | ~ v1_funct_1(C_120)
      | ~ l1_pre_topc(B_119)
      | ~ v2_pre_topc(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_184,plain,(
    ! [D_121] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_121)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_121)
      | ~ m1_pre_topc(D_121,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_193,plain,(
    ! [D_121] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_121)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_121)
      | ~ m1_pre_topc(D_121,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_44,c_42,c_30,c_28,c_97,c_184])).

tff(c_195,plain,(
    ! [D_122] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_122)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_122)
      | ~ m1_pre_topc(D_122,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_193])).

tff(c_2,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    ! [D_122,B_4] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_122),B_4) = k9_relat_1('#skF_4',B_4)
      | ~ r1_tarski(B_4,u1_struct_0(D_122))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_122,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_277,plain,(
    ! [D_133,B_134] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_133),B_134) = k9_relat_1('#skF_4',B_134)
      | ~ r1_tarski(B_134,u1_struct_0(D_133))
      | ~ m1_pre_topc(D_133,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_209])).

tff(c_291,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_277])).

tff(c_297,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_291])).

tff(c_194,plain,(
    ! [D_121] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_121)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_121)
      | ~ m1_pre_topc(D_121,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_193])).

tff(c_4,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k7_relat_1(B_9,A_8),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( m1_subset_1(A_85,k1_zfmisc_1(k2_zfmisc_1(B_86,C_87)))
      | ~ r1_tarski(A_85,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(B_86,C_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [B_105,A_106,B_107,C_108] :
      ( m1_subset_1(k7_relat_1(B_105,A_106),k1_zfmisc_1(k2_zfmisc_1(B_107,C_108)))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_zfmisc_1(B_107,C_108)))
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_12,plain,(
    ! [D_20,B_18,C_19,A_17] :
      ( m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(B_18,C_19)))
      | ~ r1_tarski(k1_relat_1(D_20),B_18)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,C_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_563,plain,(
    ! [C_200,A_202,B_199,B_198,B_201] :
      ( m1_subset_1(k7_relat_1(B_199,A_202),k1_zfmisc_1(k2_zfmisc_1(B_198,C_200)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_199,A_202)),B_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(B_201,C_200)))
      | ~ v1_relat_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_126,c_12])).

tff(c_575,plain,(
    ! [A_202,B_198] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_202),k1_zfmisc_1(k2_zfmisc_1(B_198,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_202)),B_198)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_563])).

tff(c_586,plain,(
    ! [A_203,B_204] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_203),k1_zfmisc_1(k2_zfmisc_1(B_204,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_203)),B_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_575])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k7_relset_1(A_13,B_14,C_15,D_16) = k9_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_692,plain,(
    ! [B_233,A_234,D_235] :
      ( k7_relset_1(B_233,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_234),D_235) = k9_relat_1(k7_relat_1('#skF_4',A_234),D_235)
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_234)),B_233) ) ),
    inference(resolution,[status(thm)],[c_586,c_10])).

tff(c_697,plain,(
    ! [A_6,D_235] :
      ( k7_relset_1(A_6,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_6),D_235) = k9_relat_1(k7_relat_1('#skF_4',A_6),D_235)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_692])).

tff(c_701,plain,(
    ! [A_236,D_237] : k7_relset_1(A_236,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_236),D_237) = k9_relat_1(k7_relat_1('#skF_4',A_236),D_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_697])).

tff(c_746,plain,(
    ! [D_248,D_249] :
      ( k7_relset_1(u1_struct_0(D_248),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_248),D_249) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_248)),D_249)
      | ~ m1_pre_topc(D_248,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_701])).

tff(c_63,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k7_relset_1(A_80,B_81,C_82,D_83) = k9_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ! [D_83] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k9_relat_1('#skF_4',D_83) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_20,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_67,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20])).

tff(c_759,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_67])).

tff(c_775,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_759])).

tff(c_781,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_775])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_297,c_781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.49  
% 3.33/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.49  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.49  
% 3.33/1.49  %Foreground sorts:
% 3.33/1.49  
% 3.33/1.49  
% 3.33/1.49  %Background operators:
% 3.33/1.49  
% 3.33/1.49  
% 3.33/1.49  %Foreground operators:
% 3.33/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.33/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.33/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.33/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.49  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.33/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.49  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.33/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.49  
% 3.33/1.51  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.33/1.51  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.51  tff(f_66, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.33/1.51  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.33/1.51  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 3.33/1.51  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.33/1.51  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.33/1.51  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 3.33/1.51  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.33/1.51  tff(f_48, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.33/1.51  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_22, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_8, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.33/1.51  tff(c_53, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_8])).
% 3.33/1.51  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_28, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_92, plain, (![A_95, B_96, C_97, D_98]: (k2_partfun1(A_95, B_96, C_97, D_98)=k7_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.33/1.51  tff(c_94, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_92])).
% 3.33/1.51  tff(c_97, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_94])).
% 3.33/1.51  tff(c_173, plain, (![A_118, B_119, C_120, D_121]: (k2_partfun1(u1_struct_0(A_118), u1_struct_0(B_119), C_120, u1_struct_0(D_121))=k2_tmap_1(A_118, B_119, C_120, D_121) | ~m1_pre_topc(D_121, A_118) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_118), u1_struct_0(B_119)))) | ~v1_funct_2(C_120, u1_struct_0(A_118), u1_struct_0(B_119)) | ~v1_funct_1(C_120) | ~l1_pre_topc(B_119) | ~v2_pre_topc(B_119) | v2_struct_0(B_119) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.33/1.51  tff(c_184, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_121))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_121) | ~m1_pre_topc(D_121, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_173])).
% 3.33/1.51  tff(c_193, plain, (![D_121]: (k7_relat_1('#skF_4', u1_struct_0(D_121))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_121) | ~m1_pre_topc(D_121, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_44, c_42, c_30, c_28, c_97, c_184])).
% 3.33/1.51  tff(c_195, plain, (![D_122]: (k7_relat_1('#skF_4', u1_struct_0(D_122))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_122) | ~m1_pre_topc(D_122, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_193])).
% 3.33/1.51  tff(c_2, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.33/1.51  tff(c_209, plain, (![D_122, B_4]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_122), B_4)=k9_relat_1('#skF_4', B_4) | ~r1_tarski(B_4, u1_struct_0(D_122)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_122, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 3.33/1.51  tff(c_277, plain, (![D_133, B_134]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_133), B_134)=k9_relat_1('#skF_4', B_134) | ~r1_tarski(B_134, u1_struct_0(D_133)) | ~m1_pre_topc(D_133, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_209])).
% 3.33/1.51  tff(c_291, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_277])).
% 3.33/1.51  tff(c_297, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_291])).
% 3.33/1.51  tff(c_194, plain, (![D_121]: (k7_relat_1('#skF_4', u1_struct_0(D_121))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_121) | ~m1_pre_topc(D_121, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_193])).
% 3.33/1.51  tff(c_4, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.33/1.51  tff(c_6, plain, (![B_9, A_8]: (r1_tarski(k7_relat_1(B_9, A_8), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.33/1.51  tff(c_77, plain, (![A_85, B_86, C_87, D_88]: (m1_subset_1(A_85, k1_zfmisc_1(k2_zfmisc_1(B_86, C_87))) | ~r1_tarski(A_85, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(B_86, C_87))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.33/1.51  tff(c_126, plain, (![B_105, A_106, B_107, C_108]: (m1_subset_1(k7_relat_1(B_105, A_106), k1_zfmisc_1(k2_zfmisc_1(B_107, C_108))) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_zfmisc_1(B_107, C_108))) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_6, c_77])).
% 3.33/1.51  tff(c_12, plain, (![D_20, B_18, C_19, A_17]: (m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(B_18, C_19))) | ~r1_tarski(k1_relat_1(D_20), B_18) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, C_19))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.51  tff(c_563, plain, (![C_200, A_202, B_199, B_198, B_201]: (m1_subset_1(k7_relat_1(B_199, A_202), k1_zfmisc_1(k2_zfmisc_1(B_198, C_200))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_199, A_202)), B_198) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(B_201, C_200))) | ~v1_relat_1(B_199))), inference(resolution, [status(thm)], [c_126, c_12])).
% 3.33/1.51  tff(c_575, plain, (![A_202, B_198]: (m1_subset_1(k7_relat_1('#skF_4', A_202), k1_zfmisc_1(k2_zfmisc_1(B_198, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_202)), B_198) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_563])).
% 3.33/1.51  tff(c_586, plain, (![A_203, B_204]: (m1_subset_1(k7_relat_1('#skF_4', A_203), k1_zfmisc_1(k2_zfmisc_1(B_204, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_203)), B_204))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_575])).
% 3.33/1.51  tff(c_10, plain, (![A_13, B_14, C_15, D_16]: (k7_relset_1(A_13, B_14, C_15, D_16)=k9_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.51  tff(c_692, plain, (![B_233, A_234, D_235]: (k7_relset_1(B_233, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_234), D_235)=k9_relat_1(k7_relat_1('#skF_4', A_234), D_235) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_234)), B_233))), inference(resolution, [status(thm)], [c_586, c_10])).
% 3.33/1.51  tff(c_697, plain, (![A_6, D_235]: (k7_relset_1(A_6, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_6), D_235)=k9_relat_1(k7_relat_1('#skF_4', A_6), D_235) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_692])).
% 3.33/1.51  tff(c_701, plain, (![A_236, D_237]: (k7_relset_1(A_236, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_236), D_237)=k9_relat_1(k7_relat_1('#skF_4', A_236), D_237))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_697])).
% 3.33/1.51  tff(c_746, plain, (![D_248, D_249]: (k7_relset_1(u1_struct_0(D_248), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_248), D_249)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_248)), D_249) | ~m1_pre_topc(D_248, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_701])).
% 3.33/1.51  tff(c_63, plain, (![A_80, B_81, C_82, D_83]: (k7_relset_1(A_80, B_81, C_82, D_83)=k9_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.51  tff(c_66, plain, (![D_83]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k9_relat_1('#skF_4', D_83))), inference(resolution, [status(thm)], [c_26, c_63])).
% 3.33/1.51  tff(c_20, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.33/1.51  tff(c_67, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20])).
% 3.33/1.51  tff(c_759, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_746, c_67])).
% 3.33/1.51  tff(c_775, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_759])).
% 3.33/1.51  tff(c_781, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_775])).
% 3.33/1.51  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_297, c_781])).
% 3.33/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.51  
% 3.33/1.51  Inference rules
% 3.33/1.51  ----------------------
% 3.33/1.51  #Ref     : 0
% 3.33/1.51  #Sup     : 178
% 3.33/1.51  #Fact    : 0
% 3.33/1.51  #Define  : 0
% 3.33/1.51  #Split   : 1
% 3.33/1.51  #Chain   : 0
% 3.33/1.51  #Close   : 0
% 3.33/1.51  
% 3.33/1.51  Ordering : KBO
% 3.33/1.51  
% 3.33/1.51  Simplification rules
% 3.33/1.51  ----------------------
% 3.33/1.51  #Subsume      : 16
% 3.33/1.51  #Demod        : 61
% 3.33/1.51  #Tautology    : 47
% 3.33/1.51  #SimpNegUnit  : 5
% 3.33/1.51  #BackRed      : 1
% 3.33/1.51  
% 3.33/1.51  #Partial instantiations: 0
% 3.33/1.51  #Strategies tried      : 1
% 3.33/1.51  
% 3.33/1.51  Timing (in seconds)
% 3.33/1.51  ----------------------
% 3.33/1.51  Preprocessing        : 0.33
% 3.33/1.51  Parsing              : 0.18
% 3.33/1.51  CNF conversion       : 0.03
% 3.33/1.51  Main loop            : 0.43
% 3.33/1.51  Inferencing          : 0.17
% 3.33/1.51  Reduction            : 0.12
% 3.33/1.51  Demodulation         : 0.09
% 3.33/1.51  BG Simplification    : 0.02
% 3.33/1.51  Subsumption          : 0.08
% 3.33/1.51  Abstraction          : 0.03
% 3.33/1.51  MUC search           : 0.00
% 3.33/1.51  Cooper               : 0.00
% 3.33/1.51  Total                : 0.79
% 3.33/1.51  Index Insertion      : 0.00
% 3.33/1.51  Index Deletion       : 0.00
% 3.33/1.51  Index Matching       : 0.00
% 3.33/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
