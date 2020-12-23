%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:39 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 119 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  182 ( 435 expanded)
%              Number of equality atoms :  147 ( 335 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_19] :
      ( k3_mcart_1('#skF_1'(A_1,B_2,C_3,D_19),'#skF_2'(A_1,B_2,C_3,D_19),'#skF_3'(A_1,B_2,C_3,D_19)) = D_19
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_1,B_2,C_3))
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k3_mcart_1('#skF_1'(A_79,B_80,C_81,D_82),'#skF_2'(A_79,B_80,C_81,D_82),'#skF_3'(A_79,B_80,C_81,D_82)) = D_82
      | ~ m1_subset_1(D_82,k3_zfmisc_1(A_79,B_80,C_81))
      | k1_xboole_0 = C_81
      | k1_xboole_0 = B_80
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [F_46,A_31,C_33,B_32,G_47,E_45] :
      ( k5_mcart_1(A_31,B_32,C_33,k3_mcart_1(E_45,F_46,G_47)) = E_45
      | ~ m1_subset_1(k3_mcart_1(E_45,F_46,G_47),k3_zfmisc_1(A_31,B_32,C_33))
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_166,plain,(
    ! [C_128,B_129,A_126,D_124,C_127,A_125,B_123] :
      ( k5_mcart_1(A_125,B_123,C_128,k3_mcart_1('#skF_1'(A_126,B_129,C_127,D_124),'#skF_2'(A_126,B_129,C_127,D_124),'#skF_3'(A_126,B_129,C_127,D_124))) = '#skF_1'(A_126,B_129,C_127,D_124)
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_125,B_123,C_128))
      | k1_xboole_0 = C_128
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_125
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_126,B_129,C_127))
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_129
      | k1_xboole_0 = A_126 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_14])).

tff(c_178,plain,(
    ! [A_132,C_133,B_136,C_130,B_131,D_134,A_135] :
      ( k5_mcart_1(A_132,B_136,C_130,D_134) = '#skF_1'(A_135,B_131,C_133,D_134)
      | ~ m1_subset_1(D_134,k3_zfmisc_1(A_132,B_136,C_130))
      | k1_xboole_0 = C_130
      | k1_xboole_0 = B_136
      | k1_xboole_0 = A_132
      | ~ m1_subset_1(D_134,k3_zfmisc_1(A_135,B_131,C_133))
      | k1_xboole_0 = C_133
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_135
      | ~ m1_subset_1(D_134,k3_zfmisc_1(A_135,B_131,C_133))
      | k1_xboole_0 = C_133
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_135 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_189,plain,(
    ! [A_135,B_131,C_133] :
      ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'(A_135,B_131,C_133,'#skF_7')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_135,B_131,C_133))
      | k1_xboole_0 = C_133
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_135 ) ),
    inference(resolution,[status(thm)],[c_18,c_178])).

tff(c_196,plain,(
    ! [A_137,B_138,C_139] :
      ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'(A_137,B_138,C_139,'#skF_7')
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_137,B_138,C_139))
      | k1_xboole_0 = C_139
      | k1_xboole_0 = B_138
      | k1_xboole_0 = A_137 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_189])).

tff(c_199,plain,
    ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_196])).

tff(c_202,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_199])).

tff(c_12,plain,(
    ! [F_46,A_31,C_33,B_32,G_47,E_45] :
      ( k6_mcart_1(A_31,B_32,C_33,k3_mcart_1(E_45,F_46,G_47)) = F_46
      | ~ m1_subset_1(k3_mcart_1(E_45,F_46,G_47),k3_zfmisc_1(A_31,B_32,C_33))
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_98,plain,(
    ! [A_102,C_104,C_105,D_101,A_103,B_100,B_106] :
      ( k6_mcart_1(A_102,B_100,C_105,k3_mcart_1('#skF_1'(A_103,B_106,C_104,D_101),'#skF_2'(A_103,B_106,C_104,D_101),'#skF_3'(A_103,B_106,C_104,D_101))) = '#skF_2'(A_103,B_106,C_104,D_101)
      | ~ m1_subset_1(D_101,k3_zfmisc_1(A_102,B_100,C_105))
      | k1_xboole_0 = C_105
      | k1_xboole_0 = B_100
      | k1_xboole_0 = A_102
      | ~ m1_subset_1(D_101,k3_zfmisc_1(A_103,B_106,C_104))
      | k1_xboole_0 = C_104
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_12])).

tff(c_124,plain,(
    ! [C_110,B_111,A_113,C_114,A_116,D_115,B_112] :
      ( k6_mcart_1(A_113,B_111,C_110,D_115) = '#skF_2'(A_116,B_112,C_114,D_115)
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_113,B_111,C_110))
      | k1_xboole_0 = C_110
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_113
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_116,B_112,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_112
      | k1_xboole_0 = A_116
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_116,B_112,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_112
      | k1_xboole_0 = A_116 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_135,plain,(
    ! [A_116,B_112,C_114] :
      ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'(A_116,B_112,C_114,'#skF_7')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_116,B_112,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_112
      | k1_xboole_0 = A_116 ) ),
    inference(resolution,[status(thm)],[c_18,c_124])).

tff(c_142,plain,(
    ! [A_117,B_118,C_119] :
      ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'(A_117,B_118,C_119,'#skF_7')
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_117,B_118,C_119))
      | k1_xboole_0 = C_119
      | k1_xboole_0 = B_118
      | k1_xboole_0 = A_117 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_135])).

tff(c_145,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_148,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_145])).

tff(c_10,plain,(
    ! [F_46,A_31,C_33,B_32,G_47,E_45] :
      ( k7_mcart_1(A_31,B_32,C_33,k3_mcart_1(E_45,F_46,G_47)) = G_47
      | ~ m1_subset_1(k3_mcart_1(E_45,F_46,G_47),k3_zfmisc_1(A_31,B_32,C_33))
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    ! [A_85,B_83,D_84,B_89,C_87,C_88,A_86] :
      ( k7_mcart_1(A_85,B_83,C_88,k3_mcart_1('#skF_1'(A_86,B_89,C_87,D_84),'#skF_2'(A_86,B_89,C_87,D_84),'#skF_3'(A_86,B_89,C_87,D_84))) = '#skF_3'(A_86,B_89,C_87,D_84)
      | ~ m1_subset_1(D_84,k3_zfmisc_1(A_85,B_83,C_88))
      | k1_xboole_0 = C_88
      | k1_xboole_0 = B_83
      | k1_xboole_0 = A_85
      | ~ m1_subset_1(D_84,k3_zfmisc_1(A_86,B_89,C_87))
      | k1_xboole_0 = C_87
      | k1_xboole_0 = B_89
      | k1_xboole_0 = A_86 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_10])).

tff(c_70,plain,(
    ! [A_96,A_95,B_92,D_94,C_90,B_91,C_93] :
      ( k7_mcart_1(A_96,B_91,C_90,D_94) = '#skF_3'(A_95,B_92,C_93,D_94)
      | ~ m1_subset_1(D_94,k3_zfmisc_1(A_96,B_91,C_90))
      | k1_xboole_0 = C_90
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_96
      | ~ m1_subset_1(D_94,k3_zfmisc_1(A_95,B_92,C_93))
      | k1_xboole_0 = C_93
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_95
      | ~ m1_subset_1(D_94,k3_zfmisc_1(A_95,B_92,C_93))
      | k1_xboole_0 = C_93
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_81,plain,(
    ! [A_95,B_92,C_93] :
      ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'(A_95,B_92,C_93,'#skF_7')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_95,B_92,C_93))
      | k1_xboole_0 = C_93
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_95 ) ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_88,plain,(
    ! [A_97,B_98,C_99] :
      ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'(A_97,B_98,C_99,'#skF_7')
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_97,B_98,C_99))
      | k1_xboole_0 = C_99
      | k1_xboole_0 = B_98
      | k1_xboole_0 = A_97 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_81])).

tff(c_91,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_88])).

tff(c_94,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_91])).

tff(c_16,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_111,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16])).

tff(c_150,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_111])).

tff(c_204,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_150])).

tff(c_211,plain,
    ( ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.40  
% 2.49/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.40  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.49/1.40  
% 2.49/1.40  %Foreground sorts:
% 2.49/1.40  
% 2.49/1.40  
% 2.49/1.40  %Background operators:
% 2.49/1.40  
% 2.49/1.40  
% 2.49/1.40  %Foreground operators:
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.40  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.49/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.40  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.49/1.40  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.40  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.40  
% 2.49/1.42  tff(f_90, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.49/1.42  tff(f_50, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.49/1.42  tff(f_73, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_mcart_1)).
% 2.49/1.42  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_22, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_20, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_18, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_2, plain, (![A_1, B_2, C_3, D_19]: (k3_mcart_1('#skF_1'(A_1, B_2, C_3, D_19), '#skF_2'(A_1, B_2, C_3, D_19), '#skF_3'(A_1, B_2, C_3, D_19))=D_19 | ~m1_subset_1(D_19, k3_zfmisc_1(A_1, B_2, C_3)) | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.42  tff(c_37, plain, (![A_79, B_80, C_81, D_82]: (k3_mcart_1('#skF_1'(A_79, B_80, C_81, D_82), '#skF_2'(A_79, B_80, C_81, D_82), '#skF_3'(A_79, B_80, C_81, D_82))=D_82 | ~m1_subset_1(D_82, k3_zfmisc_1(A_79, B_80, C_81)) | k1_xboole_0=C_81 | k1_xboole_0=B_80 | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.42  tff(c_14, plain, (![F_46, A_31, C_33, B_32, G_47, E_45]: (k5_mcart_1(A_31, B_32, C_33, k3_mcart_1(E_45, F_46, G_47))=E_45 | ~m1_subset_1(k3_mcart_1(E_45, F_46, G_47), k3_zfmisc_1(A_31, B_32, C_33)) | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.49/1.42  tff(c_166, plain, (![C_128, B_129, A_126, D_124, C_127, A_125, B_123]: (k5_mcart_1(A_125, B_123, C_128, k3_mcart_1('#skF_1'(A_126, B_129, C_127, D_124), '#skF_2'(A_126, B_129, C_127, D_124), '#skF_3'(A_126, B_129, C_127, D_124)))='#skF_1'(A_126, B_129, C_127, D_124) | ~m1_subset_1(D_124, k3_zfmisc_1(A_125, B_123, C_128)) | k1_xboole_0=C_128 | k1_xboole_0=B_123 | k1_xboole_0=A_125 | ~m1_subset_1(D_124, k3_zfmisc_1(A_126, B_129, C_127)) | k1_xboole_0=C_127 | k1_xboole_0=B_129 | k1_xboole_0=A_126)), inference(superposition, [status(thm), theory('equality')], [c_37, c_14])).
% 2.49/1.42  tff(c_178, plain, (![A_132, C_133, B_136, C_130, B_131, D_134, A_135]: (k5_mcart_1(A_132, B_136, C_130, D_134)='#skF_1'(A_135, B_131, C_133, D_134) | ~m1_subset_1(D_134, k3_zfmisc_1(A_132, B_136, C_130)) | k1_xboole_0=C_130 | k1_xboole_0=B_136 | k1_xboole_0=A_132 | ~m1_subset_1(D_134, k3_zfmisc_1(A_135, B_131, C_133)) | k1_xboole_0=C_133 | k1_xboole_0=B_131 | k1_xboole_0=A_135 | ~m1_subset_1(D_134, k3_zfmisc_1(A_135, B_131, C_133)) | k1_xboole_0=C_133 | k1_xboole_0=B_131 | k1_xboole_0=A_135)), inference(superposition, [status(thm), theory('equality')], [c_2, c_166])).
% 2.49/1.42  tff(c_189, plain, (![A_135, B_131, C_133]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'(A_135, B_131, C_133, '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_135, B_131, C_133)) | k1_xboole_0=C_133 | k1_xboole_0=B_131 | k1_xboole_0=A_135)), inference(resolution, [status(thm)], [c_18, c_178])).
% 2.49/1.42  tff(c_196, plain, (![A_137, B_138, C_139]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'(A_137, B_138, C_139, '#skF_7') | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_137, B_138, C_139)) | k1_xboole_0=C_139 | k1_xboole_0=B_138 | k1_xboole_0=A_137)), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_189])).
% 2.49/1.42  tff(c_199, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_196])).
% 2.49/1.42  tff(c_202, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_199])).
% 2.49/1.42  tff(c_12, plain, (![F_46, A_31, C_33, B_32, G_47, E_45]: (k6_mcart_1(A_31, B_32, C_33, k3_mcart_1(E_45, F_46, G_47))=F_46 | ~m1_subset_1(k3_mcart_1(E_45, F_46, G_47), k3_zfmisc_1(A_31, B_32, C_33)) | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.49/1.42  tff(c_98, plain, (![A_102, C_104, C_105, D_101, A_103, B_100, B_106]: (k6_mcart_1(A_102, B_100, C_105, k3_mcart_1('#skF_1'(A_103, B_106, C_104, D_101), '#skF_2'(A_103, B_106, C_104, D_101), '#skF_3'(A_103, B_106, C_104, D_101)))='#skF_2'(A_103, B_106, C_104, D_101) | ~m1_subset_1(D_101, k3_zfmisc_1(A_102, B_100, C_105)) | k1_xboole_0=C_105 | k1_xboole_0=B_100 | k1_xboole_0=A_102 | ~m1_subset_1(D_101, k3_zfmisc_1(A_103, B_106, C_104)) | k1_xboole_0=C_104 | k1_xboole_0=B_106 | k1_xboole_0=A_103)), inference(superposition, [status(thm), theory('equality')], [c_37, c_12])).
% 2.49/1.42  tff(c_124, plain, (![C_110, B_111, A_113, C_114, A_116, D_115, B_112]: (k6_mcart_1(A_113, B_111, C_110, D_115)='#skF_2'(A_116, B_112, C_114, D_115) | ~m1_subset_1(D_115, k3_zfmisc_1(A_113, B_111, C_110)) | k1_xboole_0=C_110 | k1_xboole_0=B_111 | k1_xboole_0=A_113 | ~m1_subset_1(D_115, k3_zfmisc_1(A_116, B_112, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_112 | k1_xboole_0=A_116 | ~m1_subset_1(D_115, k3_zfmisc_1(A_116, B_112, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_112 | k1_xboole_0=A_116)), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 2.49/1.42  tff(c_135, plain, (![A_116, B_112, C_114]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'(A_116, B_112, C_114, '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_116, B_112, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_112 | k1_xboole_0=A_116)), inference(resolution, [status(thm)], [c_18, c_124])).
% 2.49/1.42  tff(c_142, plain, (![A_117, B_118, C_119]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'(A_117, B_118, C_119, '#skF_7') | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_117, B_118, C_119)) | k1_xboole_0=C_119 | k1_xboole_0=B_118 | k1_xboole_0=A_117)), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_135])).
% 2.49/1.42  tff(c_145, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_142])).
% 2.49/1.42  tff(c_148, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_145])).
% 2.49/1.42  tff(c_10, plain, (![F_46, A_31, C_33, B_32, G_47, E_45]: (k7_mcart_1(A_31, B_32, C_33, k3_mcart_1(E_45, F_46, G_47))=G_47 | ~m1_subset_1(k3_mcart_1(E_45, F_46, G_47), k3_zfmisc_1(A_31, B_32, C_33)) | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.49/1.42  tff(c_58, plain, (![A_85, B_83, D_84, B_89, C_87, C_88, A_86]: (k7_mcart_1(A_85, B_83, C_88, k3_mcart_1('#skF_1'(A_86, B_89, C_87, D_84), '#skF_2'(A_86, B_89, C_87, D_84), '#skF_3'(A_86, B_89, C_87, D_84)))='#skF_3'(A_86, B_89, C_87, D_84) | ~m1_subset_1(D_84, k3_zfmisc_1(A_85, B_83, C_88)) | k1_xboole_0=C_88 | k1_xboole_0=B_83 | k1_xboole_0=A_85 | ~m1_subset_1(D_84, k3_zfmisc_1(A_86, B_89, C_87)) | k1_xboole_0=C_87 | k1_xboole_0=B_89 | k1_xboole_0=A_86)), inference(superposition, [status(thm), theory('equality')], [c_37, c_10])).
% 2.49/1.42  tff(c_70, plain, (![A_96, A_95, B_92, D_94, C_90, B_91, C_93]: (k7_mcart_1(A_96, B_91, C_90, D_94)='#skF_3'(A_95, B_92, C_93, D_94) | ~m1_subset_1(D_94, k3_zfmisc_1(A_96, B_91, C_90)) | k1_xboole_0=C_90 | k1_xboole_0=B_91 | k1_xboole_0=A_96 | ~m1_subset_1(D_94, k3_zfmisc_1(A_95, B_92, C_93)) | k1_xboole_0=C_93 | k1_xboole_0=B_92 | k1_xboole_0=A_95 | ~m1_subset_1(D_94, k3_zfmisc_1(A_95, B_92, C_93)) | k1_xboole_0=C_93 | k1_xboole_0=B_92 | k1_xboole_0=A_95)), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 2.49/1.42  tff(c_81, plain, (![A_95, B_92, C_93]: (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'(A_95, B_92, C_93, '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_95, B_92, C_93)) | k1_xboole_0=C_93 | k1_xboole_0=B_92 | k1_xboole_0=A_95)), inference(resolution, [status(thm)], [c_18, c_70])).
% 2.49/1.42  tff(c_88, plain, (![A_97, B_98, C_99]: (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'(A_97, B_98, C_99, '#skF_7') | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_97, B_98, C_99)) | k1_xboole_0=C_99 | k1_xboole_0=B_98 | k1_xboole_0=A_97)), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_81])).
% 2.49/1.42  tff(c_91, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_88])).
% 2.49/1.42  tff(c_94, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_91])).
% 2.49/1.42  tff(c_16, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.42  tff(c_111, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_16])).
% 2.49/1.42  tff(c_150, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_111])).
% 2.49/1.42  tff(c_204, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_150])).
% 2.49/1.42  tff(c_211, plain, (~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 2.49/1.42  tff(c_214, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_211])).
% 2.49/1.42  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_214])).
% 2.49/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  Inference rules
% 2.49/1.42  ----------------------
% 2.49/1.42  #Ref     : 0
% 2.49/1.42  #Sup     : 38
% 2.49/1.42  #Fact    : 0
% 2.49/1.42  #Define  : 0
% 2.49/1.42  #Split   : 0
% 2.49/1.42  #Chain   : 0
% 2.49/1.42  #Close   : 0
% 2.49/1.42  
% 2.49/1.42  Ordering : KBO
% 2.49/1.42  
% 2.49/1.42  Simplification rules
% 2.49/1.42  ----------------------
% 2.49/1.42  #Subsume      : 0
% 2.49/1.42  #Demod        : 7
% 2.49/1.42  #Tautology    : 16
% 2.49/1.42  #SimpNegUnit  : 9
% 2.49/1.42  #BackRed      : 6
% 2.49/1.42  
% 2.49/1.42  #Partial instantiations: 0
% 2.49/1.42  #Strategies tried      : 1
% 2.49/1.42  
% 2.49/1.42  Timing (in seconds)
% 2.49/1.42  ----------------------
% 2.49/1.42  Preprocessing        : 0.36
% 2.49/1.42  Parsing              : 0.17
% 2.49/1.42  CNF conversion       : 0.03
% 2.49/1.42  Main loop            : 0.25
% 2.49/1.42  Inferencing          : 0.11
% 2.49/1.42  Reduction            : 0.06
% 2.49/1.42  Demodulation         : 0.04
% 2.49/1.42  BG Simplification    : 0.02
% 2.49/1.42  Subsumption          : 0.05
% 2.49/1.42  Abstraction          : 0.02
% 2.49/1.42  MUC search           : 0.00
% 2.49/1.42  Cooper               : 0.00
% 2.49/1.42  Total                : 0.65
% 2.49/1.42  Index Insertion      : 0.00
% 2.49/1.42  Index Deletion       : 0.00
% 2.49/1.42  Index Matching       : 0.00
% 2.49/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
