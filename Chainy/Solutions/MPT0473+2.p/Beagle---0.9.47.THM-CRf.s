%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0473+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:26 EST 2020

% Result     : Theorem 16.63s
% Output     : CNFRefutation 16.95s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 327 expanded)
%              Number of leaves         :  249 ( 270 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 143 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > v1_subset_1 > r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_setfam_1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > m1_subset_1 > m1_setfam_1 > v2_setfam_1 > v1_zfmisc_1 > v1_xboole_0 > v1_setfam_1 > v1_relat_1 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > o_2_1_setfam_1 > o_2_0_setfam_1 > k8_setfam_1 > k7_setfam_1 > k6_subset_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k4_setfam_1 > k3_xboole_0 > k3_subset_1 > k3_setfam_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k2_setfam_1 > #nlpp > o_1_1_relat_1 > o_1_0_setfam_1 > k4_relat_1 > k3_tarski > k3_relat_1 > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_142 > #skF_91 > #skF_76 > #skF_114 > #skF_175 > #skF_47 > #skF_118 > #skF_26 > #skF_106 > #skF_11 > #skF_75 > #skF_133 > #skF_41 > #skF_73 > #skF_65 > #skF_166 > #skF_93 > #skF_33 > #skF_57 > #skF_86 > #skF_18 > #skF_146 > #skF_121 > #skF_113 > #skF_45 > #skF_61 > #skF_66 > #skF_111 > #skF_171 > #skF_6 > #skF_152 > #skF_131 > #skF_87 > #skF_127 > #skF_155 > #skF_1 > #skF_68 > #skF_17 > #skF_48 > #skF_112 > #skF_115 > #skF_32 > #skF_116 > #skF_94 > #skF_72 > #skF_70 > #skF_99 > #skF_60 > #skF_92 > #skF_31 > #skF_136 > #skF_4 > #skF_36 > #skF_108 > #skF_138 > #skF_79 > #skF_69 > #skF_10 > #skF_81 > #skF_117 > #skF_151 > #skF_95 > #skF_84 > #skF_100 > #skF_37 > #skF_82 > #skF_12 > #skF_123 > #skF_96 > #skF_168 > #skF_56 > #skF_143 > #skF_78 > #skF_172 > #skF_173 > #skF_88 > #skF_28 > #skF_156 > #skF_67 > #skF_46 > #skF_160 > #skF_35 > #skF_74 > #skF_5 > #skF_49 > #skF_19 > #skF_167 > #skF_44 > #skF_150 > #skF_30 > #skF_144 > #skF_141 > #skF_27 > #skF_110 > #skF_97 > #skF_153 > #skF_107 > #skF_85 > #skF_80 > #skF_51 > #skF_162 > #skF_9 > #skF_90 > #skF_126 > #skF_71 > #skF_165 > #skF_7 > #skF_119 > #skF_64 > #skF_103 > #skF_20 > #skF_24 > #skF_164 > #skF_34 > #skF_23 > #skF_128 > #skF_149 > #skF_14 > #skF_50 > #skF_89 > #skF_140 > #skF_130 > #skF_77 > #skF_145 > #skF_63 > #skF_59 > #skF_104 > #skF_58 > #skF_170 > #skF_43 > #skF_52 > #skF_137 > #skF_54 > #skF_125 > #skF_3 > #skF_62 > #skF_55 > #skF_157 > #skF_38 > #skF_2 > #skF_163 > #skF_21 > #skF_101 > #skF_169 > #skF_161 > #skF_176 > #skF_120 > #skF_102 > #skF_105 > #skF_40 > #skF_174 > #skF_154 > #skF_135 > #skF_122 > #skF_8 > #skF_159 > #skF_158 > #skF_25 > #skF_147 > #skF_132 > #skF_124 > #skF_29 > #skF_16 > #skF_129 > #skF_148 > #skF_98 > #skF_134 > #skF_83 > #skF_22 > #skF_15 > #skF_139 > #skF_42 > #skF_53 > #skF_39 > #skF_109

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_142',type,(
    '#skF_142': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_91',type,(
    '#skF_91': $i > $i )).

tff('#skF_76',type,(
    '#skF_76': ( $i * $i ) > $i )).

tff('#skF_114',type,(
    '#skF_114': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_175',type,(
    '#skF_175': $i > $i )).

tff('#skF_47',type,(
    '#skF_47': ( $i * $i ) > $i )).

tff('#skF_118',type,(
    '#skF_118': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_106',type,(
    '#skF_106': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_75',type,(
    '#skF_75': ( $i * $i ) > $i )).

tff('#skF_133',type,(
    '#skF_133': $i > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff('#skF_73',type,(
    '#skF_73': ( $i * $i ) > $i )).

tff('#skF_65',type,(
    '#skF_65': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_166',type,(
    '#skF_166': ( $i * ( $i * $i ) ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_93',type,(
    '#skF_93': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * $i ) > $i )).

tff('#skF_86',type,(
    '#skF_86': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff('#skF_146',type,(
    '#skF_146': ( $i * $i ) > $i )).

tff('#skF_121',type,(
    '#skF_121': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_113',type,(
    '#skF_113': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_45',type,(
    '#skF_45': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_61',type,(
    '#skF_61': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_66',type,(
    '#skF_66': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_111',type,(
    '#skF_111': ( $i * ( $i * $i ) ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(o_2_1_setfam_1,type,(
    o_2_1_setfam_1: ( $i * $i ) > $i )).

tff('#skF_171',type,(
    '#skF_171': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_152',type,(
    '#skF_152': ( $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_131',type,(
    '#skF_131': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_87',type,(
    '#skF_87': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_127',type,(
    '#skF_127': ( $i * ( $i * $i ) ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_155',type,(
    '#skF_155': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_68',type,(
    '#skF_68': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_48',type,(
    '#skF_48': ( $i * $i ) > $i )).

tff('#skF_112',type,(
    '#skF_112': ( $i * $i ) > $i )).

tff('#skF_115',type,(
    '#skF_115': ( $i * ( $i * $i ) ) > $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff('#skF_116',type,(
    '#skF_116': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_94',type,(
    '#skF_94': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_72',type,(
    '#skF_72': ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_70',type,(
    '#skF_70': ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_99',type,(
    '#skF_99': ( $i * ( $i * $i ) ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_60',type,(
    '#skF_60': ( $i * $i ) > $i )).

tff('#skF_92',type,(
    '#skF_92': ( $i * $i ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i ) > $i )).

tff('#skF_136',type,(
    '#skF_136': $i > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_36',type,(
    '#skF_36': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_108',type,(
    '#skF_108': ( $i * $i ) > $i )).

tff('#skF_138',type,(
    '#skF_138': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_79',type,(
    '#skF_79': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_69',type,(
    '#skF_69': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_81',type,(
    '#skF_81': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_117',type,(
    '#skF_117': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_151',type,(
    '#skF_151': ( $i * $i ) > $i )).

tff('#skF_95',type,(
    '#skF_95': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_84',type,(
    '#skF_84': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_100',type,(
    '#skF_100': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_82',type,(
    '#skF_82': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_123',type,(
    '#skF_123': ( $i * ( $i * $i ) ) > $i )).

tff(v1_setfam_1,type,(
    v1_setfam_1: $i > $o )).

tff(o_1_0_setfam_1,type,(
    o_1_0_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_96',type,(
    '#skF_96': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_168',type,(
    '#skF_168': ( $i * ( $i * $i ) ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': $i > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_143',type,(
    '#skF_143': ( $i * $i ) > $i )).

tff('#skF_78',type,(
    '#skF_78': ( $i * $i ) > $i )).

tff('#skF_172',type,(
    '#skF_172': ( $i * $i ) > $i )).

tff('#skF_173',type,(
    '#skF_173': ( $i * $i ) > $i )).

tff('#skF_88',type,(
    '#skF_88': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_156',type,(
    '#skF_156': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_67',type,(
    '#skF_67': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_160',type,(
    '#skF_160': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_74',type,(
    '#skF_74': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(k4_setfam_1,type,(
    k4_setfam_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_49',type,(
    '#skF_49': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_167',type,(
    '#skF_167': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_44',type,(
    '#skF_44': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_150',type,(
    '#skF_150': ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_144',type,(
    '#skF_144': $i > $i )).

tff('#skF_141',type,(
    '#skF_141': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_110',type,(
    '#skF_110': ( $i * $i ) > $i )).

tff('#skF_97',type,(
    '#skF_97': ( $i * ( $i * $i ) ) > $i )).

tff(r2_setfam_1,type,(
    r2_setfam_1: ( $i * $i ) > $o )).

tff('#skF_153',type,(
    '#skF_153': ( $i * $i ) > $i )).

tff('#skF_107',type,(
    '#skF_107': ( $i * $i ) > $i )).

tff('#skF_85',type,(
    '#skF_85': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_80',type,(
    '#skF_80': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_51',type,(
    '#skF_51': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_162',type,(
    '#skF_162': ( $i * $i ) > $i )).

tff(v2_setfam_1,type,(
    v2_setfam_1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_90',type,(
    '#skF_90': $i > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff('#skF_126',type,(
    '#skF_126': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_71',type,(
    '#skF_71': ( $i * $i ) > $i )).

tff('#skF_165',type,(
    '#skF_165': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_119',type,(
    '#skF_119': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_64',type,(
    '#skF_64': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_103',type,(
    '#skF_103': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i ) > $i )).

tff('#skF_164',type,(
    '#skF_164': ( $i * $i ) > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_128',type,(
    '#skF_128': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_149',type,(
    '#skF_149': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_50',type,(
    '#skF_50': ( $i * $i ) > $i )).

tff('#skF_89',type,(
    '#skF_89': $i > $i )).

tff(o_2_0_setfam_1,type,(
    o_2_0_setfam_1: ( $i * $i ) > $i )).

tff('#skF_140',type,(
    '#skF_140': ( $i * ( $i * $i ) ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_130',type,(
    '#skF_130': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_77',type,(
    '#skF_77': $i > $i )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_145',type,(
    '#skF_145': ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_63',type,(
    '#skF_63': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * $i ) > $i )).

tff('#skF_104',type,(
    '#skF_104': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_58',type,(
    '#skF_58': ( $i * $i ) > $i )).

tff('#skF_170',type,(
    '#skF_170': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_43',type,(
    '#skF_43': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_52',type,(
    '#skF_52': ( $i * $i ) > $i )).

tff('#skF_137',type,(
    '#skF_137': $i > $i )).

tff('#skF_54',type,(
    '#skF_54': ( $i * ( $i * $i ) ) > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#skF_125',type,(
    '#skF_125': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_62',type,(
    '#skF_62': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#skF_55',type,(
    '#skF_55': ( $i * $i ) > $i )).

tff('#skF_157',type,(
    '#skF_157': ( $i * $i ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_163',type,(
    '#skF_163': ( $i * $i ) > $i )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_101',type,(
    '#skF_101': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_169',type,(
    '#skF_169': ( $i * ( $i * $i ) ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_161',type,(
    '#skF_161': ( $i * $i ) > $i )).

tff('#skF_176',type,(
    '#skF_176': $i )).

tff('#skF_120',type,(
    '#skF_120': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_102',type,(
    '#skF_102': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_105',type,(
    '#skF_105': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff('#skF_174',type,(
    '#skF_174': $i > $i )).

tff('#skF_154',type,(
    '#skF_154': ( $i * $i ) > $i )).

tff('#skF_135',type,(
    '#skF_135': $i )).

tff('#skF_122',type,(
    '#skF_122': ( $i * ( $i * $i ) ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_159',type,(
    '#skF_159': ( $i * $i ) > $i )).

tff(o_1_1_relat_1,type,(
    o_1_1_relat_1: $i > $i )).

tff('#skF_158',type,(
    '#skF_158': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_147',type,(
    '#skF_147': ( $i * $i ) > $i )).

tff('#skF_132',type,(
    '#skF_132': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_124',type,(
    '#skF_124': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff('#skF_129',type,(
    '#skF_129': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_148',type,(
    '#skF_148': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_98',type,(
    '#skF_98': ( $i * $i ) > $i )).

tff('#skF_134',type,(
    '#skF_134': $i )).

tff('#skF_83',type,(
    '#skF_83': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_139',type,(
    '#skF_139': $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff('#skF_109',type,(
    '#skF_109': ( $i * $i ) > $i )).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_661,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t6_boole)).

tff(f_4116,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k1_relat_1(A) = k1_xboole_0
        <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_3787,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_3747,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_3779,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_3751,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5824,plain,(
    ! [A_3482] :
      ( k1_xboole_0 = A_3482
      | ~ v1_xboole_0(A_3482) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_5837,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_5824])).

tff(c_2835,plain,(
    ! [A_3173] :
      ( k1_xboole_0 = A_3173
      | ~ v1_xboole_0(A_3173) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_2848,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_2835])).

tff(c_2610,plain,
    ( k2_relat_1('#skF_176') != k1_xboole_0
    | k1_relat_1('#skF_176') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_4116])).

tff(c_2741,plain,(
    k1_relat_1('#skF_176') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2610])).

tff(c_2856,plain,(
    k1_relat_1('#skF_176') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2741])).

tff(c_2608,plain,(
    v1_relat_1('#skF_176') ),
    inference(cnfTransformation,[status(thm)],[f_4116])).

tff(c_2616,plain,
    ( k1_relat_1('#skF_176') = k1_xboole_0
    | k2_relat_1('#skF_176') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_4116])).

tff(c_2761,plain,(
    k2_relat_1('#skF_176') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2616])).

tff(c_2852,plain,(
    k2_relat_1('#skF_176') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2761])).

tff(c_5674,plain,(
    ! [A_3448] :
      ( ~ v1_xboole_0(k2_relat_1(A_3448))
      | ~ v1_relat_1(A_3448)
      | v1_xboole_0(A_3448) ) ),
    inference(cnfTransformation,[status(thm)],[f_3787])).

tff(c_5680,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_relat_1('#skF_176')
    | v1_xboole_0('#skF_176') ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_5674])).

tff(c_5686,plain,(
    v1_xboole_0('#skF_176') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2608,c_112,c_5680])).

tff(c_3165,plain,(
    ! [A_3218] :
      ( v1_xboole_0(k1_relat_1(A_3218))
      | ~ v1_xboole_0(A_3218) ) ),
    inference(cnfTransformation,[status(thm)],[f_3747])).

tff(c_424,plain,(
    ! [A_327] :
      ( k1_xboole_0 = A_327
      | ~ v1_xboole_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_661])).

tff(c_2849,plain,(
    ! [A_327] :
      ( A_327 = '#skF_9'
      | ~ v1_xboole_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_424])).

tff(c_3175,plain,(
    ! [A_3218] :
      ( k1_relat_1(A_3218) = '#skF_9'
      | ~ v1_xboole_0(A_3218) ) ),
    inference(resolution,[status(thm)],[c_3165,c_2849])).

tff(c_5693,plain,(
    k1_relat_1('#skF_176') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5686,c_3175])).

tff(c_5707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2856,c_5693])).

tff(c_5708,plain,(
    k1_relat_1('#skF_176') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2616])).

tff(c_5741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5708,c_2741])).

tff(c_5742,plain,(
    k2_relat_1('#skF_176') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2610])).

tff(c_5847,plain,(
    k2_relat_1('#skF_176') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_5742])).

tff(c_5743,plain,(
    k1_relat_1('#skF_176') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2610])).

tff(c_5848,plain,(
    k1_relat_1('#skF_176') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_5743])).

tff(c_8797,plain,(
    ! [A_3764] :
      ( ~ v1_xboole_0(k1_relat_1(A_3764))
      | ~ v1_relat_1(A_3764)
      | v1_xboole_0(A_3764) ) ),
    inference(cnfTransformation,[status(thm)],[f_3779])).

tff(c_8806,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_relat_1('#skF_176')
    | v1_xboole_0('#skF_176') ),
    inference(superposition,[status(thm),theory(equality)],[c_5848,c_8797])).

tff(c_8811,plain,(
    v1_xboole_0('#skF_176') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2608,c_112,c_8806])).

tff(c_6272,plain,(
    ! [A_3540] :
      ( v1_xboole_0(k2_relat_1(A_3540))
      | ~ v1_xboole_0(A_3540) ) ),
    inference(cnfTransformation,[status(thm)],[f_3751])).

tff(c_5838,plain,(
    ! [A_327] :
      ( A_327 = '#skF_9'
      | ~ v1_xboole_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_424])).

tff(c_6282,plain,(
    ! [A_3540] :
      ( k2_relat_1(A_3540) = '#skF_9'
      | ~ v1_xboole_0(A_3540) ) ),
    inference(resolution,[status(thm)],[c_6272,c_5838])).

tff(c_8819,plain,(
    k2_relat_1('#skF_176') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8811,c_6282])).

tff(c_8832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5847,c_8819])).
%------------------------------------------------------------------------------
