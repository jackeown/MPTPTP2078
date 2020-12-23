%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:00 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 188 expanded)
%              Number of leaves         :   36 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 909 expanded)
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

tff(f_132,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_96,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_24,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_51,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_54])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_93,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k2_partfun1(A_89,B_90,C_91,D_92) = k7_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,(
    ! [D_92] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_92) = k7_relat_1('#skF_4',D_92)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_93])).

tff(c_98,plain,(
    ! [D_92] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_92) = k7_relat_1('#skF_4',D_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_95])).

tff(c_168,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k2_partfun1(u1_struct_0(A_110),u1_struct_0(B_111),C_112,u1_struct_0(D_113)) = k2_tmap_1(A_110,B_111,C_112,D_113)
      | ~ m1_pre_topc(D_113,A_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc(B_111)
      | ~ v2_pre_topc(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_176,plain,(
    ! [D_113] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_113)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_113)
      | ~ m1_pre_topc(D_113,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_184,plain,(
    ! [D_113] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_113)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_113)
      | ~ m1_pre_topc(D_113,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_46,c_44,c_32,c_30,c_98,c_176])).

tff(c_217,plain,(
    ! [D_118] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_118)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_118)
      | ~ m1_pre_topc(D_118,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48,c_184])).

tff(c_6,plain,(
    ! [A_6,C_10,B_9] :
      ( k9_relat_1(k7_relat_1(A_6,C_10),B_9) = k9_relat_1(A_6,B_9)
      | ~ r1_tarski(B_9,C_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_231,plain,(
    ! [D_118,B_9] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_118),B_9) = k9_relat_1('#skF_4',B_9)
      | ~ r1_tarski(B_9,u1_struct_0(D_118))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_118,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_6])).

tff(c_589,plain,(
    ! [D_182,B_183] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_182),B_183) = k9_relat_1('#skF_4',B_183)
      | ~ r1_tarski(B_183,u1_struct_0(D_182))
      | ~ m1_pre_topc(D_182,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_231])).

tff(c_599,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_589])).

tff(c_604,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_599])).

tff(c_185,plain,(
    ! [D_113] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_113)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_113)
      | ~ m1_pre_topc(D_113,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48,c_184])).

tff(c_8,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( m1_subset_1(k2_partfun1(A_106,B_107,C_108,D_109),k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_158,plain,(
    ! [D_92] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_92),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_144])).

tff(c_186,plain,(
    ! [D_114] : m1_subset_1(k7_relat_1('#skF_4',D_114),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_158])).

tff(c_12,plain,(
    ! [D_20,B_18,C_19,A_17] :
      ( m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(B_18,C_19)))
      | ~ r1_tarski(k1_relat_1(D_20),B_18)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,C_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_407,plain,(
    ! [D_162,B_163] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_162),k1_zfmisc_1(k2_zfmisc_1(B_163,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_162)),B_163) ) ),
    inference(resolution,[status(thm)],[c_186,c_12])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k7_relset_1(A_13,B_14,C_15,D_16) = k9_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_906,plain,(
    ! [B_237,D_238,D_239] :
      ( k7_relset_1(B_237,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_238),D_239) = k9_relat_1(k7_relat_1('#skF_4',D_238),D_239)
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_238)),B_237) ) ),
    inference(resolution,[status(thm)],[c_407,c_10])).

tff(c_911,plain,(
    ! [A_11,D_239] :
      ( k7_relset_1(A_11,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_11),D_239) = k9_relat_1(k7_relat_1('#skF_4',A_11),D_239)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_906])).

tff(c_915,plain,(
    ! [A_240,D_241] : k7_relset_1(A_240,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',A_240),D_241) = k9_relat_1(k7_relat_1('#skF_4',A_240),D_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_911])).

tff(c_1304,plain,(
    ! [D_287,D_288] :
      ( k7_relset_1(u1_struct_0(D_287),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_287),D_288) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_287)),D_288)
      | ~ m1_pre_topc(D_287,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_915])).

tff(c_72,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [D_82] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_82) = k9_relat_1('#skF_4',D_82) ),
    inference(resolution,[status(thm)],[c_28,c_72])).

tff(c_22,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_76,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_22])).

tff(c_1314,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_76])).

tff(c_1325,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1314])).

tff(c_1349,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_1325])).

tff(c_1355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_604,c_1349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.56  
% 3.73/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.57  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.73/1.57  
% 3.73/1.57  %Foreground sorts:
% 3.73/1.57  
% 3.73/1.57  
% 3.73/1.57  %Background operators:
% 3.73/1.57  
% 3.73/1.57  
% 3.73/1.57  %Foreground operators:
% 3.73/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.73/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.73/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.73/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.73/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.73/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.73/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.73/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.73/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.73/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.73/1.57  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.73/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.73/1.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.73/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.73/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.73/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.57  
% 3.73/1.58  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.73/1.58  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.73/1.58  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.73/1.58  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.73/1.58  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.73/1.58  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 3.73/1.58  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.73/1.58  tff(f_63, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.73/1.58  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.73/1.58  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.73/1.58  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_24, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.58  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_51, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.73/1.58  tff(c_54, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_51])).
% 3.73/1.58  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_54])).
% 3.73/1.58  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_30, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_93, plain, (![A_89, B_90, C_91, D_92]: (k2_partfun1(A_89, B_90, C_91, D_92)=k7_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.73/1.58  tff(c_95, plain, (![D_92]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_92)=k7_relat_1('#skF_4', D_92) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_93])).
% 3.73/1.58  tff(c_98, plain, (![D_92]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_92)=k7_relat_1('#skF_4', D_92))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_95])).
% 3.73/1.58  tff(c_168, plain, (![A_110, B_111, C_112, D_113]: (k2_partfun1(u1_struct_0(A_110), u1_struct_0(B_111), C_112, u1_struct_0(D_113))=k2_tmap_1(A_110, B_111, C_112, D_113) | ~m1_pre_topc(D_113, A_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_pre_topc(B_111) | ~v2_pre_topc(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.73/1.58  tff(c_176, plain, (![D_113]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_113))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_113) | ~m1_pre_topc(D_113, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_168])).
% 3.73/1.58  tff(c_184, plain, (![D_113]: (k7_relat_1('#skF_4', u1_struct_0(D_113))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_113) | ~m1_pre_topc(D_113, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_46, c_44, c_32, c_30, c_98, c_176])).
% 3.73/1.58  tff(c_217, plain, (![D_118]: (k7_relat_1('#skF_4', u1_struct_0(D_118))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_118) | ~m1_pre_topc(D_118, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_48, c_184])).
% 3.73/1.58  tff(c_6, plain, (![A_6, C_10, B_9]: (k9_relat_1(k7_relat_1(A_6, C_10), B_9)=k9_relat_1(A_6, B_9) | ~r1_tarski(B_9, C_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.58  tff(c_231, plain, (![D_118, B_9]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_118), B_9)=k9_relat_1('#skF_4', B_9) | ~r1_tarski(B_9, u1_struct_0(D_118)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_118, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_6])).
% 3.73/1.58  tff(c_589, plain, (![D_182, B_183]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_182), B_183)=k9_relat_1('#skF_4', B_183) | ~r1_tarski(B_183, u1_struct_0(D_182)) | ~m1_pre_topc(D_182, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_231])).
% 3.73/1.58  tff(c_599, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_589])).
% 3.73/1.58  tff(c_604, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_599])).
% 3.73/1.58  tff(c_185, plain, (![D_113]: (k7_relat_1('#skF_4', u1_struct_0(D_113))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_113) | ~m1_pre_topc(D_113, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_48, c_184])).
% 3.73/1.58  tff(c_8, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.73/1.58  tff(c_144, plain, (![A_106, B_107, C_108, D_109]: (m1_subset_1(k2_partfun1(A_106, B_107, C_108, D_109), k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_funct_1(C_108))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.73/1.58  tff(c_158, plain, (![D_92]: (m1_subset_1(k7_relat_1('#skF_4', D_92), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_144])).
% 3.73/1.58  tff(c_186, plain, (![D_114]: (m1_subset_1(k7_relat_1('#skF_4', D_114), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_158])).
% 3.73/1.58  tff(c_12, plain, (![D_20, B_18, C_19, A_17]: (m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(B_18, C_19))) | ~r1_tarski(k1_relat_1(D_20), B_18) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, C_19))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.73/1.58  tff(c_407, plain, (![D_162, B_163]: (m1_subset_1(k7_relat_1('#skF_4', D_162), k1_zfmisc_1(k2_zfmisc_1(B_163, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_162)), B_163))), inference(resolution, [status(thm)], [c_186, c_12])).
% 3.73/1.58  tff(c_10, plain, (![A_13, B_14, C_15, D_16]: (k7_relset_1(A_13, B_14, C_15, D_16)=k9_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.73/1.58  tff(c_906, plain, (![B_237, D_238, D_239]: (k7_relset_1(B_237, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_238), D_239)=k9_relat_1(k7_relat_1('#skF_4', D_238), D_239) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_238)), B_237))), inference(resolution, [status(thm)], [c_407, c_10])).
% 3.73/1.58  tff(c_911, plain, (![A_11, D_239]: (k7_relset_1(A_11, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_11), D_239)=k9_relat_1(k7_relat_1('#skF_4', A_11), D_239) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_906])).
% 3.73/1.58  tff(c_915, plain, (![A_240, D_241]: (k7_relset_1(A_240, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', A_240), D_241)=k9_relat_1(k7_relat_1('#skF_4', A_240), D_241))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_911])).
% 3.73/1.58  tff(c_1304, plain, (![D_287, D_288]: (k7_relset_1(u1_struct_0(D_287), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_287), D_288)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_287)), D_288) | ~m1_pre_topc(D_287, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_915])).
% 3.73/1.58  tff(c_72, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.73/1.58  tff(c_75, plain, (![D_82]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_82)=k9_relat_1('#skF_4', D_82))), inference(resolution, [status(thm)], [c_28, c_72])).
% 3.73/1.58  tff(c_22, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.58  tff(c_76, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_22])).
% 3.73/1.58  tff(c_1314, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1304, c_76])).
% 3.73/1.58  tff(c_1325, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1314])).
% 3.73/1.58  tff(c_1349, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_185, c_1325])).
% 3.73/1.58  tff(c_1355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_604, c_1349])).
% 3.73/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.58  
% 3.73/1.58  Inference rules
% 3.73/1.58  ----------------------
% 3.73/1.58  #Ref     : 0
% 3.73/1.58  #Sup     : 295
% 3.73/1.58  #Fact    : 0
% 3.73/1.58  #Define  : 0
% 3.73/1.58  #Split   : 1
% 3.73/1.58  #Chain   : 0
% 3.73/1.58  #Close   : 0
% 3.73/1.58  
% 3.73/1.58  Ordering : KBO
% 3.73/1.58  
% 3.73/1.58  Simplification rules
% 3.73/1.58  ----------------------
% 3.73/1.58  #Subsume      : 16
% 3.73/1.58  #Demod        : 288
% 3.73/1.58  #Tautology    : 78
% 3.73/1.58  #SimpNegUnit  : 25
% 3.73/1.58  #BackRed      : 7
% 3.73/1.58  
% 3.73/1.58  #Partial instantiations: 0
% 3.73/1.58  #Strategies tried      : 1
% 3.73/1.58  
% 3.73/1.58  Timing (in seconds)
% 3.73/1.58  ----------------------
% 3.73/1.59  Preprocessing        : 0.33
% 3.73/1.59  Parsing              : 0.19
% 3.73/1.59  CNF conversion       : 0.03
% 3.73/1.59  Main loop            : 0.56
% 3.73/1.59  Inferencing          : 0.21
% 3.73/1.59  Reduction            : 0.19
% 3.73/1.59  Demodulation         : 0.14
% 3.73/1.59  BG Simplification    : 0.03
% 3.73/1.59  Subsumption          : 0.08
% 3.73/1.59  Abstraction          : 0.04
% 3.73/1.59  MUC search           : 0.00
% 3.73/1.59  Cooper               : 0.00
% 3.73/1.59  Total                : 0.92
% 3.73/1.59  Index Insertion      : 0.00
% 3.73/1.59  Index Deletion       : 0.00
% 3.73/1.59  Index Matching       : 0.00
% 3.73/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
