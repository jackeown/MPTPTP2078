%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 182 expanded)
%              Number of leaves         :   35 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 897 expanded)
%              Number of equality atoms :   30 (  96 expanded)
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

tff(f_127,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_91,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_6])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_83,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k2_partfun1(A_86,B_87,C_88,D_89) = k7_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,(
    ! [D_89] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_88,plain,(
    ! [D_89] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_89) = k7_relat_1('#skF_4',D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_178,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k2_partfun1(u1_struct_0(A_111),u1_struct_0(B_112),C_113,u1_struct_0(D_114)) = k2_tmap_1(A_111,B_112,C_113,D_114)
      | ~ m1_pre_topc(D_114,A_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_188,plain,(
    ! [D_114] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_114)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_114)
      | ~ m1_pre_topc(D_114,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_178])).

tff(c_200,plain,(
    ! [D_114] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_114)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_114)
      | ~ m1_pre_topc(D_114,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_44,c_42,c_30,c_28,c_88,c_188])).

tff(c_202,plain,(
    ! [D_115] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_115)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_115)
      | ~ m1_pre_topc(D_115,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_200])).

tff(c_2,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_216,plain,(
    ! [D_115,B_4] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_115),B_4) = k9_relat_1('#skF_4',B_4)
      | ~ r1_tarski(B_4,u1_struct_0(D_115))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_115,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2])).

tff(c_562,plain,(
    ! [D_177,B_178] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_177),B_178) = k9_relat_1('#skF_4',B_178)
      | ~ r1_tarski(B_178,u1_struct_0(D_177))
      | ~ m1_pre_topc(D_177,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_216])).

tff(c_572,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_562])).

tff(c_577,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_572])).

tff(c_201,plain,(
    ! [D_114] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_114)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_114)
      | ~ m1_pre_topc(D_114,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_200])).

tff(c_4,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_133,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( m1_subset_1(k2_partfun1(A_103,B_104,C_105,D_106),k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,(
    ! [D_89] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_89),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_133])).

tff(c_155,plain,(
    ! [D_107] : m1_subset_1(k7_relat_1('#skF_4',D_107),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_147])).

tff(c_10,plain,(
    ! [D_18,B_16,C_17,A_15] :
      ( m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(B_16,C_17)))
      | ~ r1_tarski(k1_relat_1(D_18),B_16)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,C_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_443,plain,(
    ! [D_161,B_162] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_161),k1_zfmisc_1(k2_zfmisc_1(B_162,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_161)),B_162) ) ),
    inference(resolution,[status(thm)],[c_155,c_10])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k7_relset_1(A_11,B_12,C_13,D_14) = k9_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_853,plain,(
    ! [B_233,D_234,D_235] :
      ( k7_relset_1(B_233,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_234),D_235) = k9_relat_1(k7_relat_1('#skF_4',D_234),D_235)
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_234)),B_233) ) ),
    inference(resolution,[status(thm)],[c_443,c_8])).

tff(c_858,plain,(
    ! [A_6,D_235] :
      ( k7_relset_1(A_6,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_6),D_235) = k9_relat_1(k7_relat_1('#skF_4',A_6),D_235)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_853])).

tff(c_915,plain,(
    ! [A_241,D_242] : k7_relset_1(A_241,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_241),D_242) = k9_relat_1(k7_relat_1('#skF_4',A_241),D_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_858])).

tff(c_1181,plain,(
    ! [D_284,D_285] :
      ( k7_relset_1(u1_struct_0(D_284),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_284),D_285) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_284)),D_285)
      | ~ m1_pre_topc(D_284,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_915])).

tff(c_69,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    ! [D_84] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_84) = k9_relat_1('#skF_4',D_84) ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_20,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_73,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_1191,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1181,c_73])).

tff(c_1202,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1191])).

tff(c_1207,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_1202])).

tff(c_1213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_577,c_1207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:29:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.60  
% 3.68/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.60  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.68/1.60  
% 3.68/1.60  %Foreground sorts:
% 3.68/1.60  
% 3.68/1.60  
% 3.68/1.60  %Background operators:
% 3.68/1.60  
% 3.68/1.60  
% 3.68/1.60  %Foreground operators:
% 3.68/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.68/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.68/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.68/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.60  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.68/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.68/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.68/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.68/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.68/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.68/1.60  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.68/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.68/1.60  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.68/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.68/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.68/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.60  
% 3.68/1.62  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.68/1.62  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.68/1.62  tff(f_64, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.68/1.62  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.68/1.62  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 3.68/1.62  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.68/1.62  tff(f_58, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.68/1.62  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.68/1.62  tff(f_44, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.68/1.62  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_22, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_6, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.68/1.62  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_6])).
% 3.68/1.62  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_28, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_83, plain, (![A_86, B_87, C_88, D_89]: (k2_partfun1(A_86, B_87, C_88, D_89)=k7_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.62  tff(c_85, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.68/1.62  tff(c_88, plain, (![D_89]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_89)=k7_relat_1('#skF_4', D_89))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_85])).
% 3.68/1.62  tff(c_178, plain, (![A_111, B_112, C_113, D_114]: (k2_partfun1(u1_struct_0(A_111), u1_struct_0(B_112), C_113, u1_struct_0(D_114))=k2_tmap_1(A_111, B_112, C_113, D_114) | ~m1_pre_topc(D_114, A_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0(A_111), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.68/1.62  tff(c_188, plain, (![D_114]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_114))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_114) | ~m1_pre_topc(D_114, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_178])).
% 3.68/1.62  tff(c_200, plain, (![D_114]: (k7_relat_1('#skF_4', u1_struct_0(D_114))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_114) | ~m1_pre_topc(D_114, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_44, c_42, c_30, c_28, c_88, c_188])).
% 3.68/1.62  tff(c_202, plain, (![D_115]: (k7_relat_1('#skF_4', u1_struct_0(D_115))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_115) | ~m1_pre_topc(D_115, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_200])).
% 3.68/1.62  tff(c_2, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.62  tff(c_216, plain, (![D_115, B_4]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_115), B_4)=k9_relat_1('#skF_4', B_4) | ~r1_tarski(B_4, u1_struct_0(D_115)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_115, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_2])).
% 3.68/1.62  tff(c_562, plain, (![D_177, B_178]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_177), B_178)=k9_relat_1('#skF_4', B_178) | ~r1_tarski(B_178, u1_struct_0(D_177)) | ~m1_pre_topc(D_177, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_216])).
% 3.68/1.62  tff(c_572, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_562])).
% 3.68/1.62  tff(c_577, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_572])).
% 3.68/1.62  tff(c_201, plain, (![D_114]: (k7_relat_1('#skF_4', u1_struct_0(D_114))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_114) | ~m1_pre_topc(D_114, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_200])).
% 3.68/1.62  tff(c_4, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.68/1.62  tff(c_133, plain, (![A_103, B_104, C_105, D_106]: (m1_subset_1(k2_partfun1(A_103, B_104, C_105, D_106), k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(C_105))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.68/1.62  tff(c_147, plain, (![D_89]: (m1_subset_1(k7_relat_1('#skF_4', D_89), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_133])).
% 3.68/1.62  tff(c_155, plain, (![D_107]: (m1_subset_1(k7_relat_1('#skF_4', D_107), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_147])).
% 3.68/1.62  tff(c_10, plain, (![D_18, B_16, C_17, A_15]: (m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(B_16, C_17))) | ~r1_tarski(k1_relat_1(D_18), B_16) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, C_17))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.68/1.62  tff(c_443, plain, (![D_161, B_162]: (m1_subset_1(k7_relat_1('#skF_4', D_161), k1_zfmisc_1(k2_zfmisc_1(B_162, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_161)), B_162))), inference(resolution, [status(thm)], [c_155, c_10])).
% 3.68/1.62  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k7_relset_1(A_11, B_12, C_13, D_14)=k9_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.62  tff(c_853, plain, (![B_233, D_234, D_235]: (k7_relset_1(B_233, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_234), D_235)=k9_relat_1(k7_relat_1('#skF_4', D_234), D_235) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_234)), B_233))), inference(resolution, [status(thm)], [c_443, c_8])).
% 3.68/1.62  tff(c_858, plain, (![A_6, D_235]: (k7_relset_1(A_6, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_6), D_235)=k9_relat_1(k7_relat_1('#skF_4', A_6), D_235) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_853])).
% 3.68/1.62  tff(c_915, plain, (![A_241, D_242]: (k7_relset_1(A_241, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_241), D_242)=k9_relat_1(k7_relat_1('#skF_4', A_241), D_242))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_858])).
% 3.68/1.62  tff(c_1181, plain, (![D_284, D_285]: (k7_relset_1(u1_struct_0(D_284), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_284), D_285)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_284)), D_285) | ~m1_pre_topc(D_284, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_915])).
% 3.68/1.62  tff(c_69, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.62  tff(c_72, plain, (![D_84]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_84)=k9_relat_1('#skF_4', D_84))), inference(resolution, [status(thm)], [c_26, c_69])).
% 3.68/1.62  tff(c_20, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.68/1.62  tff(c_73, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 3.68/1.62  tff(c_1191, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1181, c_73])).
% 3.68/1.62  tff(c_1202, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1191])).
% 3.68/1.62  tff(c_1207, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_201, c_1202])).
% 3.68/1.62  tff(c_1213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_577, c_1207])).
% 3.68/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.62  
% 3.68/1.62  Inference rules
% 3.68/1.62  ----------------------
% 3.68/1.62  #Ref     : 0
% 3.68/1.62  #Sup     : 270
% 3.68/1.62  #Fact    : 0
% 3.68/1.62  #Define  : 0
% 3.68/1.62  #Split   : 0
% 3.68/1.62  #Chain   : 0
% 3.68/1.62  #Close   : 0
% 3.68/1.62  
% 3.68/1.62  Ordering : KBO
% 3.68/1.62  
% 3.68/1.62  Simplification rules
% 3.68/1.62  ----------------------
% 3.68/1.62  #Subsume      : 14
% 3.68/1.62  #Demod        : 249
% 3.68/1.62  #Tautology    : 68
% 3.68/1.62  #SimpNegUnit  : 22
% 3.68/1.62  #BackRed      : 8
% 3.68/1.62  
% 3.68/1.62  #Partial instantiations: 0
% 3.68/1.62  #Strategies tried      : 1
% 3.68/1.62  
% 3.68/1.62  Timing (in seconds)
% 3.68/1.62  ----------------------
% 3.68/1.62  Preprocessing        : 0.33
% 3.68/1.62  Parsing              : 0.17
% 3.68/1.62  CNF conversion       : 0.03
% 3.68/1.62  Main loop            : 0.53
% 3.68/1.62  Inferencing          : 0.21
% 3.68/1.62  Reduction            : 0.18
% 3.68/1.62  Demodulation         : 0.13
% 3.68/1.62  BG Simplification    : 0.03
% 3.68/1.62  Subsumption          : 0.08
% 3.68/1.62  Abstraction          : 0.04
% 3.68/1.62  MUC search           : 0.00
% 3.68/1.62  Cooper               : 0.00
% 3.68/1.62  Total                : 0.89
% 3.68/1.62  Index Insertion      : 0.00
% 3.68/1.62  Index Deletion       : 0.00
% 3.68/1.62  Index Matching       : 0.00
% 3.68/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
