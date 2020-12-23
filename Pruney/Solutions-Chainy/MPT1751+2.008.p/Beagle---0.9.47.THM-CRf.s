%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 377 expanded)
%              Number of leaves         :   39 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          :  211 (1919 expanded)
%              Number of equality atoms :   30 ( 201 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ~ v1_xboole_0(D)
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,A,D)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
         => ( ( r1_tarski(B,A)
              & r1_tarski(k7_relset_1(A,D,E,B),C) )
           => ( v1_funct_1(k2_partfun1(A,D,E,B))
              & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
              & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_32,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_73,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_180,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k2_partfun1(A_117,B_118,C_119,D_120) = k7_relat_1(C_119,D_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_185,plain,(
    ! [D_120] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_120) = k7_relat_1('#skF_4',D_120)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_180])).

tff(c_192,plain,(
    ! [D_120] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_120) = k7_relat_1('#skF_4',D_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_185])).

tff(c_451,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k2_partfun1(u1_struct_0(A_196),u1_struct_0(B_197),C_198,u1_struct_0(D_199)) = k2_tmap_1(A_196,B_197,C_198,D_199)
      | ~ m1_pre_topc(D_199,A_196)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196),u1_struct_0(B_197))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_196),u1_struct_0(B_197))
      | ~ v1_funct_1(C_198)
      | ~ l1_pre_topc(B_197)
      | ~ v2_pre_topc(B_197)
      | v2_struct_0(B_197)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_462,plain,(
    ! [D_199] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_199)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_199)
      | ~ m1_pre_topc(D_199,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_451])).

tff(c_471,plain,(
    ! [D_199] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_199)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_199)
      | ~ m1_pre_topc(D_199,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_40,c_38,c_192,c_462])).

tff(c_474,plain,(
    ! [D_200] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_200)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_200)
      | ~ m1_pre_topc(D_200,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_471])).

tff(c_6,plain,(
    ! [A_3,C_7,B_6] :
      ( k9_relat_1(k7_relat_1(A_3,C_7),B_6) = k9_relat_1(A_3,B_6)
      | ~ r1_tarski(B_6,C_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_501,plain,(
    ! [D_200,B_6] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_200),B_6) = k9_relat_1('#skF_4',B_6)
      | ~ r1_tarski(B_6,u1_struct_0(D_200))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_200,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_6])).

tff(c_512,plain,(
    ! [D_205,B_206] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_205),B_206) = k9_relat_1('#skF_4',B_206)
      | ~ r1_tarski(B_206,u1_struct_0(D_205))
      | ~ m1_pre_topc(D_205,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_501])).

tff(c_536,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_512])).

tff(c_545,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_536])).

tff(c_472,plain,(
    ! [D_199] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_199)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_199)
      | ~ m1_pre_topc(D_199,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_471])).

tff(c_89,plain,(
    ! [B_87,A_88] :
      ( m1_subset_1(u1_struct_0(B_87),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(u1_struct_0(B_87),u1_struct_0(A_88))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_104,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_relset_1(A_94,B_95,C_96,D_97) = k9_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    ! [D_97] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_97) = k9_relat_1('#skF_4',D_97) ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_127,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( m1_subset_1(k7_relset_1(A_103,B_104,C_105,D_106),k1_zfmisc_1(B_104))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,(
    ! [D_97] :
      ( m1_subset_1(k9_relat_1('#skF_4',D_97),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_127])).

tff(c_146,plain,(
    ! [D_107] : m1_subset_1(k9_relat_1('#skF_4',D_107),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_140])).

tff(c_150,plain,(
    ! [D_107] : r1_tarski(k9_relat_1('#skF_4',D_107),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_22,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_218,plain,(
    ! [B_133,E_132,D_134,C_131,A_135] :
      ( v1_funct_1(k2_partfun1(A_135,D_134,E_132,B_133))
      | ~ r1_tarski(k7_relset_1(A_135,D_134,E_132,B_133),C_131)
      | ~ r1_tarski(B_133,A_135)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_135,D_134)))
      | ~ v1_funct_2(E_132,A_135,D_134)
      | ~ v1_funct_1(E_132)
      | v1_xboole_0(D_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_222,plain,(
    ! [D_97,C_131] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_97))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_97),C_131)
      | ~ r1_tarski(D_97,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_218])).

tff(c_225,plain,(
    ! [D_97,C_131] :
      ( v1_funct_1(k7_relat_1('#skF_4',D_97))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_97),C_131)
      | ~ r1_tarski(D_97,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_192,c_222])).

tff(c_235,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_24,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_238,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_235,c_24])).

tff(c_241,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_238])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_244])).

tff(c_250,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_319,plain,(
    ! [E_174,D_176,A_177,C_173,B_175] :
      ( m1_subset_1(k2_partfun1(A_177,D_176,E_174,B_175),k1_zfmisc_1(k2_zfmisc_1(B_175,C_173)))
      | ~ r1_tarski(k7_relset_1(A_177,D_176,E_174,B_175),C_173)
      | ~ r1_tarski(B_175,A_177)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(A_177,D_176)))
      | ~ v1_funct_2(E_174,A_177,D_176)
      | ~ v1_funct_1(E_174)
      | v1_xboole_0(D_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_339,plain,(
    ! [D_120,C_173] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_120),k1_zfmisc_1(k2_zfmisc_1(D_120,C_173)))
      | ~ r1_tarski(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_120),C_173)
      | ~ r1_tarski(D_120,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_319])).

tff(c_348,plain,(
    ! [D_120,C_173] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_120),k1_zfmisc_1(k2_zfmisc_1(D_120,C_173)))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_120),C_173)
      | ~ r1_tarski(D_120,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_110,c_339])).

tff(c_350,plain,(
    ! [D_178,C_179] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_178),k1_zfmisc_1(k2_zfmisc_1(D_178,C_179)))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_178),C_179)
      | ~ r1_tarski(D_178,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_348])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( k7_relset_1(A_15,B_16,C_17,D_18) = k9_relat_1(C_17,D_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_578,plain,(
    ! [D_215,C_216,D_217] :
      ( k7_relset_1(D_215,C_216,k7_relat_1('#skF_4',D_215),D_217) = k9_relat_1(k7_relat_1('#skF_4',D_215),D_217)
      | ~ r1_tarski(k9_relat_1('#skF_4',D_215),C_216)
      | ~ r1_tarski(D_215,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_350,c_12])).

tff(c_597,plain,(
    ! [D_220,D_221] :
      ( k7_relset_1(D_220,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_220),D_221) = k9_relat_1(k7_relat_1('#skF_4',D_220),D_221)
      | ~ r1_tarski(D_220,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_150,c_578])).

tff(c_772,plain,(
    ! [D_252,D_253] :
      ( k7_relset_1(u1_struct_0(D_252),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_252),D_253) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_252)),D_253)
      | ~ r1_tarski(u1_struct_0(D_252),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_252,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_597])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_112,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_30])).

tff(c_788,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_112])).

tff(c_796,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_788])).

tff(c_798,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_801,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_798])).

tff(c_805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_801])).

tff(c_806,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_853,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_806])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_545,c_853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:43:16 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.53  
% 3.56/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.54  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.54  
% 3.56/1.54  %Foreground sorts:
% 3.56/1.54  
% 3.56/1.54  
% 3.56/1.54  %Background operators:
% 3.56/1.54  
% 3.56/1.54  
% 3.56/1.54  %Foreground operators:
% 3.56/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.56/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.56/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.56/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.56/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.56/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.54  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.56/1.54  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.56/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.54  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.56/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.54  
% 3.67/1.56  tff(f_156, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 3.67/1.56  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.67/1.56  tff(f_54, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.67/1.56  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.67/1.56  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 3.67/1.56  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.67/1.56  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.67/1.56  tff(f_48, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.67/1.56  tff(f_44, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.67/1.56  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.67/1.56  tff(f_74, axiom, (![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 3.67/1.56  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.67/1.56  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_32, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_73, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.56  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_73])).
% 3.67/1.56  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_180, plain, (![A_117, B_118, C_119, D_120]: (k2_partfun1(A_117, B_118, C_119, D_120)=k7_relat_1(C_119, D_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_1(C_119))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.67/1.56  tff(c_185, plain, (![D_120]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_120)=k7_relat_1('#skF_4', D_120) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_180])).
% 3.67/1.56  tff(c_192, plain, (![D_120]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_120)=k7_relat_1('#skF_4', D_120))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_185])).
% 3.67/1.56  tff(c_451, plain, (![A_196, B_197, C_198, D_199]: (k2_partfun1(u1_struct_0(A_196), u1_struct_0(B_197), C_198, u1_struct_0(D_199))=k2_tmap_1(A_196, B_197, C_198, D_199) | ~m1_pre_topc(D_199, A_196) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196), u1_struct_0(B_197)))) | ~v1_funct_2(C_198, u1_struct_0(A_196), u1_struct_0(B_197)) | ~v1_funct_1(C_198) | ~l1_pre_topc(B_197) | ~v2_pre_topc(B_197) | v2_struct_0(B_197) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.67/1.56  tff(c_462, plain, (![D_199]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_199))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_199) | ~m1_pre_topc(D_199, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_451])).
% 3.67/1.56  tff(c_471, plain, (![D_199]: (k7_relat_1('#skF_4', u1_struct_0(D_199))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_199) | ~m1_pre_topc(D_199, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_40, c_38, c_192, c_462])).
% 3.67/1.56  tff(c_474, plain, (![D_200]: (k7_relat_1('#skF_4', u1_struct_0(D_200))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_200) | ~m1_pre_topc(D_200, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_471])).
% 3.67/1.56  tff(c_6, plain, (![A_3, C_7, B_6]: (k9_relat_1(k7_relat_1(A_3, C_7), B_6)=k9_relat_1(A_3, B_6) | ~r1_tarski(B_6, C_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.56  tff(c_501, plain, (![D_200, B_6]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_200), B_6)=k9_relat_1('#skF_4', B_6) | ~r1_tarski(B_6, u1_struct_0(D_200)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_200, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_474, c_6])).
% 3.67/1.56  tff(c_512, plain, (![D_205, B_206]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_205), B_206)=k9_relat_1('#skF_4', B_206) | ~r1_tarski(B_206, u1_struct_0(D_205)) | ~m1_pre_topc(D_205, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_501])).
% 3.67/1.56  tff(c_536, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_512])).
% 3.67/1.56  tff(c_545, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_536])).
% 3.67/1.56  tff(c_472, plain, (![D_199]: (k7_relat_1('#skF_4', u1_struct_0(D_199))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_199) | ~m1_pre_topc(D_199, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_471])).
% 3.67/1.56  tff(c_89, plain, (![B_87, A_88]: (m1_subset_1(u1_struct_0(B_87), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.67/1.56  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.67/1.56  tff(c_93, plain, (![B_87, A_88]: (r1_tarski(u1_struct_0(B_87), u1_struct_0(A_88)) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_89, c_2])).
% 3.67/1.56  tff(c_104, plain, (![A_94, B_95, C_96, D_97]: (k7_relset_1(A_94, B_95, C_96, D_97)=k9_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.67/1.56  tff(c_110, plain, (![D_97]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_97)=k9_relat_1('#skF_4', D_97))), inference(resolution, [status(thm)], [c_36, c_104])).
% 3.67/1.56  tff(c_127, plain, (![A_103, B_104, C_105, D_106]: (m1_subset_1(k7_relset_1(A_103, B_104, C_105, D_106), k1_zfmisc_1(B_104)) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.67/1.56  tff(c_140, plain, (![D_97]: (m1_subset_1(k9_relat_1('#skF_4', D_97), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_110, c_127])).
% 3.67/1.56  tff(c_146, plain, (![D_107]: (m1_subset_1(k9_relat_1('#skF_4', D_107), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_140])).
% 3.67/1.56  tff(c_150, plain, (![D_107]: (r1_tarski(k9_relat_1('#skF_4', D_107), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_146, c_2])).
% 3.67/1.56  tff(c_22, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.67/1.56  tff(c_218, plain, (![B_133, E_132, D_134, C_131, A_135]: (v1_funct_1(k2_partfun1(A_135, D_134, E_132, B_133)) | ~r1_tarski(k7_relset_1(A_135, D_134, E_132, B_133), C_131) | ~r1_tarski(B_133, A_135) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_135, D_134))) | ~v1_funct_2(E_132, A_135, D_134) | ~v1_funct_1(E_132) | v1_xboole_0(D_134))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.67/1.56  tff(c_222, plain, (![D_97, C_131]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_97)) | ~r1_tarski(k9_relat_1('#skF_4', D_97), C_131) | ~r1_tarski(D_97, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_218])).
% 3.67/1.56  tff(c_225, plain, (![D_97, C_131]: (v1_funct_1(k7_relat_1('#skF_4', D_97)) | ~r1_tarski(k9_relat_1('#skF_4', D_97), C_131) | ~r1_tarski(D_97, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_192, c_222])).
% 3.67/1.56  tff(c_235, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_225])).
% 3.67/1.56  tff(c_24, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.67/1.56  tff(c_238, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_235, c_24])).
% 3.67/1.56  tff(c_241, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_238])).
% 3.67/1.56  tff(c_244, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_241])).
% 3.67/1.56  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_244])).
% 3.67/1.56  tff(c_250, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_225])).
% 3.67/1.56  tff(c_319, plain, (![E_174, D_176, A_177, C_173, B_175]: (m1_subset_1(k2_partfun1(A_177, D_176, E_174, B_175), k1_zfmisc_1(k2_zfmisc_1(B_175, C_173))) | ~r1_tarski(k7_relset_1(A_177, D_176, E_174, B_175), C_173) | ~r1_tarski(B_175, A_177) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(A_177, D_176))) | ~v1_funct_2(E_174, A_177, D_176) | ~v1_funct_1(E_174) | v1_xboole_0(D_176))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.67/1.56  tff(c_339, plain, (![D_120, C_173]: (m1_subset_1(k7_relat_1('#skF_4', D_120), k1_zfmisc_1(k2_zfmisc_1(D_120, C_173))) | ~r1_tarski(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_120), C_173) | ~r1_tarski(D_120, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_192, c_319])).
% 3.67/1.56  tff(c_348, plain, (![D_120, C_173]: (m1_subset_1(k7_relat_1('#skF_4', D_120), k1_zfmisc_1(k2_zfmisc_1(D_120, C_173))) | ~r1_tarski(k9_relat_1('#skF_4', D_120), C_173) | ~r1_tarski(D_120, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_110, c_339])).
% 3.67/1.56  tff(c_350, plain, (![D_178, C_179]: (m1_subset_1(k7_relat_1('#skF_4', D_178), k1_zfmisc_1(k2_zfmisc_1(D_178, C_179))) | ~r1_tarski(k9_relat_1('#skF_4', D_178), C_179) | ~r1_tarski(D_178, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_250, c_348])).
% 3.67/1.56  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k7_relset_1(A_15, B_16, C_17, D_18)=k9_relat_1(C_17, D_18) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.67/1.56  tff(c_578, plain, (![D_215, C_216, D_217]: (k7_relset_1(D_215, C_216, k7_relat_1('#skF_4', D_215), D_217)=k9_relat_1(k7_relat_1('#skF_4', D_215), D_217) | ~r1_tarski(k9_relat_1('#skF_4', D_215), C_216) | ~r1_tarski(D_215, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_350, c_12])).
% 3.67/1.56  tff(c_597, plain, (![D_220, D_221]: (k7_relset_1(D_220, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_220), D_221)=k9_relat_1(k7_relat_1('#skF_4', D_220), D_221) | ~r1_tarski(D_220, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_150, c_578])).
% 3.67/1.56  tff(c_772, plain, (![D_252, D_253]: (k7_relset_1(u1_struct_0(D_252), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_252), D_253)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_252)), D_253) | ~r1_tarski(u1_struct_0(D_252), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_252, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_472, c_597])).
% 3.67/1.56  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.67/1.56  tff(c_112, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_30])).
% 3.67/1.56  tff(c_788, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_772, c_112])).
% 3.67/1.56  tff(c_796, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_788])).
% 3.67/1.56  tff(c_798, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_796])).
% 3.67/1.56  tff(c_801, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_93, c_798])).
% 3.67/1.56  tff(c_805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_801])).
% 3.67/1.56  tff(c_806, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_796])).
% 3.67/1.56  tff(c_853, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_472, c_806])).
% 3.67/1.56  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_545, c_853])).
% 3.67/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.56  
% 3.67/1.56  Inference rules
% 3.67/1.56  ----------------------
% 3.67/1.56  #Ref     : 0
% 3.67/1.56  #Sup     : 179
% 3.67/1.56  #Fact    : 0
% 3.67/1.56  #Define  : 0
% 3.67/1.56  #Split   : 4
% 3.67/1.56  #Chain   : 0
% 3.67/1.56  #Close   : 0
% 3.67/1.56  
% 3.67/1.56  Ordering : KBO
% 3.67/1.56  
% 3.67/1.56  Simplification rules
% 3.67/1.56  ----------------------
% 3.67/1.56  #Subsume      : 26
% 3.67/1.56  #Demod        : 67
% 3.67/1.56  #Tautology    : 28
% 3.67/1.56  #SimpNegUnit  : 11
% 3.67/1.56  #BackRed      : 1
% 3.67/1.56  
% 3.67/1.56  #Partial instantiations: 0
% 3.67/1.56  #Strategies tried      : 1
% 3.67/1.56  
% 3.67/1.56  Timing (in seconds)
% 3.67/1.56  ----------------------
% 3.67/1.56  Preprocessing        : 0.34
% 3.67/1.56  Parsing              : 0.18
% 3.67/1.56  CNF conversion       : 0.03
% 3.67/1.56  Main loop            : 0.46
% 3.67/1.56  Inferencing          : 0.18
% 3.67/1.56  Reduction            : 0.13
% 3.67/1.56  Demodulation         : 0.09
% 3.67/1.56  BG Simplification    : 0.03
% 3.67/1.56  Subsumption          : 0.08
% 3.67/1.56  Abstraction          : 0.03
% 3.67/1.56  MUC search           : 0.00
% 3.67/1.56  Cooper               : 0.00
% 3.67/1.56  Total                : 0.84
% 3.67/1.56  Index Insertion      : 0.00
% 3.67/1.56  Index Deletion       : 0.00
% 3.67/1.56  Index Matching       : 0.00
% 3.67/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
