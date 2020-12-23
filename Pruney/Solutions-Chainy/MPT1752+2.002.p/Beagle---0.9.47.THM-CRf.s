%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:00 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 129 expanded)
%              Number of leaves         :   42 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 ( 476 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_149,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(k10_relat_1(A,C),B)
         => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_113,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_88,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_88])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_14])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_98,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k8_relset_1(A_97,B_98,C_99,D_100) = k10_relat_1(C_99,D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_101,plain,(
    ! [D_100] : k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_100) = k10_relat_1('#skF_4',D_100) ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_32,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_102,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_32])).

tff(c_425,plain,(
    ! [A_162,B_163,C_164] :
      ( k10_relat_1(k7_relat_1(A_162,B_163),C_164) = k10_relat_1(A_162,C_164)
      | ~ r1_tarski(k10_relat_1(A_162,C_164),B_163)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_428,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_425])).

tff(c_431,plain,(
    k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') = k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_40,c_428])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_177,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k2_partfun1(A_115,B_116,C_117,D_118) = k7_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_179,plain,(
    ! [D_118] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_118) = k7_relat_1('#skF_4',D_118)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_177])).

tff(c_182,plain,(
    ! [D_118] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',D_118) = k7_relat_1('#skF_4',D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_179])).

tff(c_572,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_partfun1(u1_struct_0(A_182),u1_struct_0(B_183),C_184,u1_struct_0(D_185)) = k2_tmap_1(A_182,B_183,C_184,D_185)
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182),u1_struct_0(B_183))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_182),u1_struct_0(B_183))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(B_183)
      | ~ v2_pre_topc(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_577,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_572])).

tff(c_581,plain,(
    ! [D_185] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_38,c_182,c_577])).

tff(c_582,plain,(
    ! [D_185] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_4',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_581])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_11,A_10)),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,C_87)
      | ~ r1_tarski(B_88,C_87)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_107,A_108,B_109] :
      ( r1_tarski(A_107,A_108)
      | ~ r1_tarski(A_107,k2_relat_1(B_109))
      | ~ v5_relat_1(B_109,A_108)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_154,plain,(
    ! [B_110,A_111,A_112] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_110,A_111)),A_112)
      | ~ v5_relat_1(B_110,A_112)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v5_relat_1(B_5,A_4)
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [B_110,A_111,A_112] :
      ( v5_relat_1(k7_relat_1(B_110,A_111),A_112)
      | ~ v1_relat_1(k7_relat_1(B_110,A_111))
      | ~ v5_relat_1(B_110,A_112)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_282,plain,(
    ! [C_137,A_138,B_139] :
      ( m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ r1_tarski(k2_relat_1(C_137),B_139)
      | ~ r1_tarski(k1_relat_1(C_137),A_138)
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k8_relset_1(A_18,B_19,C_20,D_21) = k10_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_771,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ r1_tarski(k2_relat_1(C_196),B_195)
      | ~ r1_tarski(k1_relat_1(C_196),A_194)
      | ~ v1_relat_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_282,c_20])).

tff(c_1096,plain,(
    ! [A_227,A_228,B_229,D_230] :
      ( k8_relset_1(A_227,A_228,B_229,D_230) = k10_relat_1(B_229,D_230)
      | ~ r1_tarski(k1_relat_1(B_229),A_227)
      | ~ v5_relat_1(B_229,A_228)
      | ~ v1_relat_1(B_229) ) ),
    inference(resolution,[status(thm)],[c_6,c_771])).

tff(c_4019,plain,(
    ! [A_511,A_512,B_513,D_514] :
      ( k8_relset_1(A_511,A_512,k7_relat_1(B_513,A_511),D_514) = k10_relat_1(k7_relat_1(B_513,A_511),D_514)
      | ~ v5_relat_1(k7_relat_1(B_513,A_511),A_512)
      | ~ v1_relat_1(k7_relat_1(B_513,A_511))
      | ~ v1_relat_1(B_513) ) ),
    inference(resolution,[status(thm)],[c_10,c_1096])).

tff(c_4203,plain,(
    ! [A_520,A_521,B_522,D_523] :
      ( k8_relset_1(A_520,A_521,k7_relat_1(B_522,A_520),D_523) = k10_relat_1(k7_relat_1(B_522,A_520),D_523)
      | ~ v1_relat_1(k7_relat_1(B_522,A_520))
      | ~ v5_relat_1(B_522,A_521)
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_174,c_4019])).

tff(c_4216,plain,(
    ! [B_526,A_527,A_528,D_529] :
      ( k8_relset_1(B_526,A_527,k7_relat_1(A_528,B_526),D_529) = k10_relat_1(k7_relat_1(A_528,B_526),D_529)
      | ~ v5_relat_1(A_528,A_527)
      | ~ v1_relat_1(A_528) ) ),
    inference(resolution,[status(thm)],[c_8,c_4203])).

tff(c_4232,plain,(
    ! [D_185,A_527,D_529] :
      ( k8_relset_1(u1_struct_0(D_185),A_527,k2_tmap_1('#skF_1','#skF_2','#skF_4',D_185),D_529) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_185)),D_529)
      | ~ v5_relat_1('#skF_4',A_527)
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_185,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_4216])).

tff(c_5757,plain,(
    ! [D_652,A_653,D_654] :
      ( k8_relset_1(u1_struct_0(D_652),A_653,k2_tmap_1('#skF_1','#skF_2','#skF_4',D_652),D_654) = k10_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_652)),D_654)
      | ~ v5_relat_1('#skF_4',A_653)
      | ~ m1_pre_topc(D_652,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4232])).

tff(c_30,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_126,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_5') != k10_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_30])).

tff(c_5763,plain,
    ( k10_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k10_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5757,c_126])).

tff(c_5770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_92,c_431,c_5763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.68  
% 7.65/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.65/2.68  
% 7.65/2.68  %Foreground sorts:
% 7.65/2.68  
% 7.65/2.68  
% 7.65/2.68  %Background operators:
% 7.65/2.68  
% 7.65/2.68  
% 7.65/2.68  %Foreground operators:
% 7.65/2.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.65/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.65/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.65/2.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.65/2.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.65/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.65/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.65/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.65/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.65/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.65/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.65/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.65/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.65/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.65/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.65/2.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.65/2.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.65/2.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.65/2.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.65/2.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.65/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.65/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.65/2.68  
% 7.88/2.70  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tmap_1)).
% 7.88/2.70  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.88/2.70  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.88/2.70  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.88/2.70  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 7.88/2.70  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.88/2.70  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.88/2.70  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.88/2.70  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 7.88/2.70  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.88/2.70  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.88/2.70  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.88/2.70  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.88/2.70  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_88, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.88/2.70  tff(c_92, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_88])).
% 7.88/2.70  tff(c_14, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.88/2.70  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_14])).
% 7.88/2.70  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_98, plain, (![A_97, B_98, C_99, D_100]: (k8_relset_1(A_97, B_98, C_99, D_100)=k10_relat_1(C_99, D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.88/2.70  tff(c_101, plain, (![D_100]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_100)=k10_relat_1('#skF_4', D_100))), inference(resolution, [status(thm)], [c_36, c_98])).
% 7.88/2.70  tff(c_32, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_102, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_32])).
% 7.88/2.70  tff(c_425, plain, (![A_162, B_163, C_164]: (k10_relat_1(k7_relat_1(A_162, B_163), C_164)=k10_relat_1(A_162, C_164) | ~r1_tarski(k10_relat_1(A_162, C_164), B_163) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.88/2.70  tff(c_428, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_425])).
% 7.88/2.70  tff(c_431, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_40, c_428])).
% 7.88/2.70  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_177, plain, (![A_115, B_116, C_117, D_118]: (k2_partfun1(A_115, B_116, C_117, D_118)=k7_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.88/2.70  tff(c_179, plain, (![D_118]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_118)=k7_relat_1('#skF_4', D_118) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_177])).
% 7.88/2.70  tff(c_182, plain, (![D_118]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', D_118)=k7_relat_1('#skF_4', D_118))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_179])).
% 7.88/2.70  tff(c_572, plain, (![A_182, B_183, C_184, D_185]: (k2_partfun1(u1_struct_0(A_182), u1_struct_0(B_183), C_184, u1_struct_0(D_185))=k2_tmap_1(A_182, B_183, C_184, D_185) | ~m1_pre_topc(D_185, A_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182), u1_struct_0(B_183)))) | ~v1_funct_2(C_184, u1_struct_0(A_182), u1_struct_0(B_183)) | ~v1_funct_1(C_184) | ~l1_pre_topc(B_183) | ~v2_pre_topc(B_183) | v2_struct_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.88/2.70  tff(c_577, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_185) | ~m1_pre_topc(D_185, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_572])).
% 7.88/2.70  tff(c_581, plain, (![D_185]: (k7_relat_1('#skF_4', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_185) | ~m1_pre_topc(D_185, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_46, c_40, c_38, c_182, c_577])).
% 7.88/2.70  tff(c_582, plain, (![D_185]: (k7_relat_1('#skF_4', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_185) | ~m1_pre_topc(D_185, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_581])).
% 7.88/2.70  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.88/2.70  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(k7_relat_1(B_11, A_10)), k2_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.88/2.70  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.88/2.70  tff(c_66, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, C_87) | ~r1_tarski(B_88, C_87) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.88/2.70  tff(c_142, plain, (![A_107, A_108, B_109]: (r1_tarski(A_107, A_108) | ~r1_tarski(A_107, k2_relat_1(B_109)) | ~v5_relat_1(B_109, A_108) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_6, c_66])).
% 7.88/2.70  tff(c_154, plain, (![B_110, A_111, A_112]: (r1_tarski(k2_relat_1(k7_relat_1(B_110, A_111)), A_112) | ~v5_relat_1(B_110, A_112) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_12, c_142])).
% 7.88/2.70  tff(c_4, plain, (![B_5, A_4]: (v5_relat_1(B_5, A_4) | ~r1_tarski(k2_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.88/2.70  tff(c_174, plain, (![B_110, A_111, A_112]: (v5_relat_1(k7_relat_1(B_110, A_111), A_112) | ~v1_relat_1(k7_relat_1(B_110, A_111)) | ~v5_relat_1(B_110, A_112) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_154, c_4])).
% 7.88/2.70  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.88/2.70  tff(c_282, plain, (![C_137, A_138, B_139]: (m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~r1_tarski(k2_relat_1(C_137), B_139) | ~r1_tarski(k1_relat_1(C_137), A_138) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.88/2.70  tff(c_20, plain, (![A_18, B_19, C_20, D_21]: (k8_relset_1(A_18, B_19, C_20, D_21)=k10_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.88/2.70  tff(c_771, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~r1_tarski(k2_relat_1(C_196), B_195) | ~r1_tarski(k1_relat_1(C_196), A_194) | ~v1_relat_1(C_196))), inference(resolution, [status(thm)], [c_282, c_20])).
% 7.88/2.70  tff(c_1096, plain, (![A_227, A_228, B_229, D_230]: (k8_relset_1(A_227, A_228, B_229, D_230)=k10_relat_1(B_229, D_230) | ~r1_tarski(k1_relat_1(B_229), A_227) | ~v5_relat_1(B_229, A_228) | ~v1_relat_1(B_229))), inference(resolution, [status(thm)], [c_6, c_771])).
% 7.88/2.70  tff(c_4019, plain, (![A_511, A_512, B_513, D_514]: (k8_relset_1(A_511, A_512, k7_relat_1(B_513, A_511), D_514)=k10_relat_1(k7_relat_1(B_513, A_511), D_514) | ~v5_relat_1(k7_relat_1(B_513, A_511), A_512) | ~v1_relat_1(k7_relat_1(B_513, A_511)) | ~v1_relat_1(B_513))), inference(resolution, [status(thm)], [c_10, c_1096])).
% 7.88/2.70  tff(c_4203, plain, (![A_520, A_521, B_522, D_523]: (k8_relset_1(A_520, A_521, k7_relat_1(B_522, A_520), D_523)=k10_relat_1(k7_relat_1(B_522, A_520), D_523) | ~v1_relat_1(k7_relat_1(B_522, A_520)) | ~v5_relat_1(B_522, A_521) | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_174, c_4019])).
% 7.88/2.70  tff(c_4216, plain, (![B_526, A_527, A_528, D_529]: (k8_relset_1(B_526, A_527, k7_relat_1(A_528, B_526), D_529)=k10_relat_1(k7_relat_1(A_528, B_526), D_529) | ~v5_relat_1(A_528, A_527) | ~v1_relat_1(A_528))), inference(resolution, [status(thm)], [c_8, c_4203])).
% 7.88/2.70  tff(c_4232, plain, (![D_185, A_527, D_529]: (k8_relset_1(u1_struct_0(D_185), A_527, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_185), D_529)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_185)), D_529) | ~v5_relat_1('#skF_4', A_527) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_185, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_4216])).
% 7.88/2.70  tff(c_5757, plain, (![D_652, A_653, D_654]: (k8_relset_1(u1_struct_0(D_652), A_653, k2_tmap_1('#skF_1', '#skF_2', '#skF_4', D_652), D_654)=k10_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_652)), D_654) | ~v5_relat_1('#skF_4', A_653) | ~m1_pre_topc(D_652, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4232])).
% 7.88/2.70  tff(c_30, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.88/2.70  tff(c_126, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_30])).
% 7.88/2.70  tff(c_5763, plain, (k10_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k10_relat_1('#skF_4', '#skF_5') | ~v5_relat_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5757, c_126])).
% 7.88/2.70  tff(c_5770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_92, c_431, c_5763])).
% 7.88/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.70  
% 7.88/2.70  Inference rules
% 7.88/2.70  ----------------------
% 7.88/2.70  #Ref     : 0
% 7.88/2.70  #Sup     : 1394
% 7.88/2.70  #Fact    : 0
% 7.88/2.70  #Define  : 0
% 7.88/2.70  #Split   : 3
% 7.88/2.70  #Chain   : 0
% 7.88/2.70  #Close   : 0
% 7.88/2.70  
% 7.88/2.70  Ordering : KBO
% 7.88/2.70  
% 7.88/2.70  Simplification rules
% 7.88/2.70  ----------------------
% 7.88/2.70  #Subsume      : 160
% 7.88/2.70  #Demod        : 136
% 7.88/2.70  #Tautology    : 23
% 7.88/2.70  #SimpNegUnit  : 3
% 7.88/2.70  #BackRed      : 1
% 7.88/2.70  
% 7.88/2.70  #Partial instantiations: 0
% 7.88/2.70  #Strategies tried      : 1
% 7.88/2.70  
% 7.88/2.70  Timing (in seconds)
% 7.88/2.70  ----------------------
% 7.88/2.70  Preprocessing        : 0.34
% 7.88/2.70  Parsing              : 0.18
% 7.88/2.70  CNF conversion       : 0.03
% 7.88/2.70  Main loop            : 1.59
% 7.88/2.70  Inferencing          : 0.44
% 7.88/2.70  Reduction            : 0.36
% 7.88/2.70  Demodulation         : 0.24
% 7.88/2.70  BG Simplification    : 0.06
% 7.88/2.70  Subsumption          : 0.60
% 7.88/2.70  Abstraction          : 0.08
% 7.88/2.70  MUC search           : 0.00
% 7.88/2.70  Cooper               : 0.00
% 7.88/2.70  Total                : 1.96
% 7.88/2.70  Index Insertion      : 0.00
% 7.88/2.70  Index Deletion       : 0.00
% 7.88/2.70  Index Matching       : 0.00
% 7.88/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
