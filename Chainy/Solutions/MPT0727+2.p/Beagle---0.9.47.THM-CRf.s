%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0727+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:28 EST 2020

% Result     : Theorem 36.89s
% Output     : CNFRefutation 36.94s
% Verified   : 
% Statistics : Number of formulae       :  394 ( 429 expanded)
%              Number of leaves         :  372 ( 386 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 (  99 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v5_funct_1 > v4_relat_1 > v3_setfam_1 > v1_subset_1 > r3_xboole_0 > r2_xboole_0 > r2_tarski > r2_setfam_1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > r1_setfam_1 > m1_subset_1 > m1_setfam_1 > v4_funct_1 > v3_relat_1 > v3_funct_1 > v2_setfam_1 > v2_relat_1 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_setfam_1 > v1_relat_1 > v1_funct_1 > k8_enumset1 > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k8_subset_1 > k7_subset_1 > k5_subset_1 > k4_subset_1 > k1_enumset1 > o_2_1_setfam_1 > o_2_1_relat_1 > o_2_0_setfam_1 > o_2_0_relat_1 > k9_relat_1 > k8_setfam_1 > k8_relat_1 > k7_setfam_1 > k7_relat_1 > k6_subset_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k4_setfam_1 > k3_xboole_0 > k3_subset_1 > k3_setfam_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k2_setfam_1 > k1_funct_1 > k11_relat_1 > k10_relat_1 > #nlpp > o_1_6_relat_1 > o_1_5_relat_1 > o_1_4_relat_1 > o_1_3_relat_1 > o_1_2_relat_1 > o_1_1_relat_1 > o_1_0_setfam_1 > o_1_0_funct_1 > k6_relat_1 > k4_relat_1 > k3_tarski > k3_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > np__1 > k1_xboole_0 > #skF_13 > #skF_142 > #skF_238 > #skF_91 > #skF_76 > #skF_114 > #skF_199 > #skF_47 > #skF_118 > #skF_168 > #skF_26 > #skF_106 > #skF_248 > #skF_11 > #skF_225 > #skF_75 > #skF_254 > #skF_133 > #skF_41 > #skF_73 > #skF_219 > #skF_228 > #skF_190 > #skF_175 > #skF_65 > #skF_183 > #skF_93 > #skF_33 > #skF_57 > #skF_148 > #skF_198 > #skF_86 > #skF_18 > #skF_144 > #skF_146 > #skF_266 > #skF_121 > #skF_113 > #skF_270 > #skF_45 > #skF_200 > #skF_268 > #skF_264 > #skF_61 > #skF_66 > #skF_111 > #skF_180 > #skF_265 > #skF_6 > #skF_131 > #skF_218 > #skF_87 > #skF_127 > #skF_1 > #skF_68 > #skF_17 > #skF_269 > #skF_162 > #skF_217 > #skF_188 > #skF_48 > #skF_208 > #skF_149 > #skF_112 > #skF_202 > #skF_115 > #skF_171 > #skF_255 > #skF_257 > #skF_247 > #skF_32 > #skF_116 > #skF_94 > #skF_203 > #skF_165 > #skF_72 > #skF_70 > #skF_271 > #skF_153 > #skF_155 > #skF_99 > #skF_60 > #skF_92 > #skF_31 > #skF_136 > #skF_209 > #skF_161 > #skF_4 > #skF_36 > #skF_108 > #skF_235 > #skF_138 > #skF_261 > #skF_79 > #skF_69 > #skF_10 > #skF_81 > #skF_117 > #skF_192 > #skF_95 > #skF_159 > #skF_84 > #skF_253 > #skF_100 > #skF_187 > #skF_176 > #skF_37 > #skF_221 > #skF_82 > #skF_167 > #skF_12 > #skF_123 > #skF_169 > #skF_96 > #skF_56 > #skF_143 > #skF_78 > #skF_172 > #skF_240 > #skF_173 > #skF_88 > #skF_28 > #skF_156 > #skF_67 > #skF_197 > #skF_46 > #skF_160 > #skF_35 > #skF_74 > #skF_5 > #skF_196 > #skF_267 > #skF_49 > #skF_19 > #skF_44 > #skF_215 > #skF_163 > #skF_30 > #skF_232 > #skF_141 > #skF_27 > #skF_224 > #skF_110 > #skF_97 > #skF_244 > #skF_154 > #skF_251 > #skF_184 > #skF_107 > #skF_164 > #skF_85 > #skF_80 > #skF_193 > #skF_51 > #skF_9 > #skF_220 > #skF_231 > #skF_201 > #skF_166 > #skF_212 > #skF_90 > #skF_206 > #skF_126 > #skF_71 > #skF_234 > #skF_222 > #skF_195 > #skF_7 > #skF_119 > #skF_64 > #skF_223 > #skF_252 > #skF_170 > #skF_103 > #skF_216 > #skF_229 > #skF_20 > #skF_260 > #skF_189 > #skF_211 > #skF_236 > #skF_24 > #skF_34 > #skF_23 > #skF_182 > #skF_185 > #skF_128 > #skF_151 > #skF_14 > #skF_50 > #skF_89 > #skF_140 > #skF_178 > #skF_205 > #skF_130 > #skF_77 > #skF_186 > #skF_263 > #skF_204 > #skF_152 > #skF_145 > #skF_242 > #skF_174 > #skF_233 > #skF_249 > #skF_63 > #skF_59 > #skF_230 > #skF_207 > #skF_104 > #skF_58 > #skF_181 > #skF_43 > #skF_52 > #skF_137 > #skF_54 > #skF_125 > #skF_191 > #skF_3 > #skF_62 > #skF_55 > #skF_38 > #skF_2 > #skF_157 > #skF_21 > #skF_101 > #skF_179 > #skF_243 > #skF_241 > #skF_226 > #skF_177 > #skF_120 > #skF_102 > #skF_105 > #skF_40 > #skF_214 > #skF_135 > #skF_122 > #skF_8 > #skF_262 > #skF_25 > #skF_258 > #skF_227 > #skF_147 > #skF_259 > #skF_213 > #skF_132 > #skF_124 > #skF_29 > #skF_237 > #skF_210 > #skF_250 > #skF_16 > #skF_129 > #skF_150 > #skF_98 > #skF_134 > #skF_83 > #skF_22 > #skF_15 > #skF_139 > #skF_239 > #skF_158 > #skF_42 > #skF_53 > #skF_194 > #skF_245 > #skF_256 > #skF_39 > #skF_246 > #skF_109

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_142',type,(
    '#skF_142': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_238',type,(
    '#skF_238': ( $i * $i ) > $i )).

tff('#skF_91',type,(
    '#skF_91': $i > $i )).

tff('#skF_76',type,(
    '#skF_76': ( $i * $i ) > $i )).

tff('#skF_114',type,(
    '#skF_114': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_199',type,(
    '#skF_199': $i > $i )).

tff('#skF_47',type,(
    '#skF_47': ( $i * $i ) > $i )).

tff('#skF_118',type,(
    '#skF_118': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_168',type,(
    '#skF_168': ( $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_106',type,(
    '#skF_106': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_248',type,(
    '#skF_248': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff('#skF_225',type,(
    '#skF_225': ( $i * $i ) > $i )).

tff(np__1,type,(
    np__1: $i )).

tff('#skF_75',type,(
    '#skF_75': ( $i * $i ) > $i )).

tff('#skF_254',type,(
    '#skF_254': ( $i * $i ) > $i )).

tff('#skF_133',type,(
    '#skF_133': $i > $i )).

tff('#skF_41',type,(
    '#skF_41': ( $i * $i ) > $i )).

tff('#skF_73',type,(
    '#skF_73': ( $i * $i ) > $i )).

tff('#skF_219',type,(
    '#skF_219': $i )).

tff('#skF_228',type,(
    '#skF_228': ( $i * $i ) > $i )).

tff(o_2_1_relat_1,type,(
    o_2_1_relat_1: ( $i * $i ) > $i )).

tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff('#skF_190',type,(
    '#skF_190': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_175',type,(
    '#skF_175': ( $i * $i ) > $i )).

tff('#skF_65',type,(
    '#skF_65': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_183',type,(
    '#skF_183': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_93',type,(
    '#skF_93': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * ( $i * $i ) ) > $i )).

tff(o_1_4_relat_1,type,(
    o_1_4_relat_1: $i > $i )).

tff('#skF_57',type,(
    '#skF_57': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_148',type,(
    '#skF_148': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_198',type,(
    '#skF_198': ( $i * $i ) > $i )).

tff('#skF_86',type,(
    '#skF_86': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff('#skF_144',type,(
    '#skF_144': ( $i * $i ) > $i )).

tff('#skF_146',type,(
    '#skF_146': ( $i * $i ) > $i )).

tff('#skF_266',type,(
    '#skF_266': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_121',type,(
    '#skF_121': ( $i * ( $i * $i ) ) > $i )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff('#skF_113',type,(
    '#skF_113': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_270',type,(
    '#skF_270': $i )).

tff('#skF_45',type,(
    '#skF_45': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_200',type,(
    '#skF_200': $i > $i )).

tff('#skF_268',type,(
    '#skF_268': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_264',type,(
    '#skF_264': ( $i * $i ) > $i )).

tff('#skF_61',type,(
    '#skF_61': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_66',type,(
    '#skF_66': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_111',type,(
    '#skF_111': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_180',type,(
    '#skF_180': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_265',type,(
    '#skF_265': ( $i * ( $i * $i ) ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(o_2_1_setfam_1,type,(
    o_2_1_setfam_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_131',type,(
    '#skF_131': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_218',type,(
    '#skF_218': $i )).

tff('#skF_87',type,(
    '#skF_87': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_127',type,(
    '#skF_127': ( $i * ( $i * $i ) ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_68',type,(
    '#skF_68': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff('#skF_269',type,(
    '#skF_269': ( $i * $i ) > $i )).

tff('#skF_162',type,(
    '#skF_162': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_217',type,(
    '#skF_217': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_188',type,(
    '#skF_188': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_48',type,(
    '#skF_48': ( $i * $i ) > $i )).

tff('#skF_208',type,(
    '#skF_208': $i > $i )).

tff('#skF_149',type,(
    '#skF_149': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_112',type,(
    '#skF_112': ( $i * $i ) > $i )).

tff('#skF_202',type,(
    '#skF_202': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_115',type,(
    '#skF_115': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_171',type,(
    '#skF_171': ( $i * $i ) > $i )).

tff('#skF_255',type,(
    '#skF_255': ( $i * $i ) > $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff('#skF_257',type,(
    '#skF_257': $i > $i )).

tff('#skF_247',type,(
    '#skF_247': $i > $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i ) > $i )).

tff(o_1_5_relat_1,type,(
    o_1_5_relat_1: $i > $i )).

tff('#skF_116',type,(
    '#skF_116': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_94',type,(
    '#skF_94': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_203',type,(
    '#skF_203': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_165',type,(
    '#skF_165': ( $i * $i ) > $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_72',type,(
    '#skF_72': ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_70',type,(
    '#skF_70': ( $i * $i ) > $i )).

tff('#skF_271',type,(
    '#skF_271': $i )).

tff('#skF_153',type,(
    '#skF_153': ( $i * ( $i * $i ) ) > $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff('#skF_155',type,(
    '#skF_155': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_209',type,(
    '#skF_209': ( $i * $i ) > $i )).

tff('#skF_161',type,(
    '#skF_161': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_235',type,(
    '#skF_235': $i > $i )).

tff('#skF_138',type,(
    '#skF_138': $i > $i )).

tff('#skF_261',type,(
    '#skF_261': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_79',type,(
    '#skF_79': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

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

tff('#skF_192',type,(
    '#skF_192': $i )).

tff('#skF_95',type,(
    '#skF_95': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_159',type,(
    '#skF_159': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_84',type,(
    '#skF_84': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff(k5_subset_1,type,(
    k5_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_253',type,(
    '#skF_253': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_100',type,(
    '#skF_100': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_187',type,(
    '#skF_187': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_176',type,(
    '#skF_176': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_37',type,(
    '#skF_37': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_221',type,(
    '#skF_221': $i )).

tff('#skF_82',type,(
    '#skF_82': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_167',type,(
    '#skF_167': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_123',type,(
    '#skF_123': ( $i * ( $i * $i ) ) > $i )).

tff(v1_setfam_1,type,(
    v1_setfam_1: $i > $o )).

tff('#skF_169',type,(
    '#skF_169': ( $i * $i ) > $i )).

tff(o_1_0_setfam_1,type,(
    o_1_0_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_96',type,(
    '#skF_96': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_56',type,(
    '#skF_56': $i > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_143',type,(
    '#skF_143': ( $i * $i ) > $i )).

tff(v4_funct_1,type,(
    v4_funct_1: $i > $o )).

tff('#skF_78',type,(
    '#skF_78': ( $i * $i ) > $i )).

tff('#skF_172',type,(
    '#skF_172': ( $i * $i ) > $i )).

tff('#skF_240',type,(
    '#skF_240': ( $i * $i ) > $i )).

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

tff('#skF_197',type,(
    '#skF_197': ( $i * $i ) > $i )).

tff('#skF_46',type,(
    '#skF_46': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff('#skF_160',type,(
    '#skF_160': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_35',type,(
    '#skF_35': ( $i * ( $i * $i ) ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_74',type,(
    '#skF_74': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_196',type,(
    '#skF_196': $i > $i )).

tff('#skF_267',type,(
    '#skF_267': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_44',type,(
    '#skF_44': ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_215',type,(
    '#skF_215': $i > $i )).

tff('#skF_163',type,(
    '#skF_163': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_232',type,(
    '#skF_232': $i > $i )).

tff('#skF_141',type,(
    '#skF_141': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_224',type,(
    '#skF_224': ( $i * $i ) > $i )).

tff('#skF_110',type,(
    '#skF_110': ( $i * $i ) > $i )).

tff('#skF_97',type,(
    '#skF_97': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_244',type,(
    '#skF_244': ( $i * $i ) > $i )).

tff('#skF_154',type,(
    '#skF_154': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_251',type,(
    '#skF_251': ( $i * ( $i * $i ) ) > $i )).

tff(r2_setfam_1,type,(
    r2_setfam_1: ( $i * $i ) > $o )).

tff('#skF_184',type,(
    '#skF_184': ( $i * $i ) > $i )).

tff('#skF_107',type,(
    '#skF_107': ( $i * $i ) > $i )).

tff('#skF_164',type,(
    '#skF_164': $i > $i )).

tff('#skF_85',type,(
    '#skF_85': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_80',type,(
    '#skF_80': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_193',type,(
    '#skF_193': ( $i * $i ) > $i )).

tff('#skF_51',type,(
    '#skF_51': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) > $i )).

tff(v2_setfam_1,type,(
    v2_setfam_1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_220',type,(
    '#skF_220': $i )).

tff('#skF_231',type,(
    '#skF_231': $i > $i )).

tff('#skF_201',type,(
    '#skF_201': ( $i * $i ) > $i )).

tff('#skF_166',type,(
    '#skF_166': ( $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#skF_212',type,(
    '#skF_212': ( $i * $i ) > $i )).

tff('#skF_90',type,(
    '#skF_90': $i > $i )).

tff('#skF_206',type,(
    '#skF_206': ( $i * ( $i * $i ) ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff('#skF_126',type,(
    '#skF_126': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_71',type,(
    '#skF_71': ( $i * $i ) > $i )).

tff('#skF_234',type,(
    '#skF_234': $i > $i )).

tff('#skF_222',type,(
    '#skF_222': ( $i * $i ) > $i )).

tff('#skF_195',type,(
    '#skF_195': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_223',type,(
    '#skF_223': ( $i * $i ) > $i )).

tff('#skF_252',type,(
    '#skF_252': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_170',type,(
    '#skF_170': ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_103',type,(
    '#skF_103': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_216',type,(
    '#skF_216': $i )).

tff('#skF_229',type,(
    '#skF_229': ( $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': ( $i * ( $i * $i ) ) > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#skF_260',type,(
    '#skF_260': ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) > $i )).

tff('#skF_189',type,(
    '#skF_189': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_211',type,(
    '#skF_211': ( $i * $i ) > $i )).

tff('#skF_236',type,(
    '#skF_236': $i > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i ) > $i )).

tff(o_1_6_relat_1,type,(
    o_1_6_relat_1: $i > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#skF_182',type,(
    '#skF_182': ( $i * $i ) > $i )).

tff('#skF_185',type,(
    '#skF_185': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_128',type,(
    '#skF_128': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_151',type,(
    '#skF_151': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_178',type,(
    '#skF_178': ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_205',type,(
    '#skF_205': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_130',type,(
    '#skF_130': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_77',type,(
    '#skF_77': $i > $i )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_186',type,(
    '#skF_186': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_263',type,(
    '#skF_263': ( $i * $i ) > $i )).

tff('#skF_204',type,(
    '#skF_204': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_152',type,(
    '#skF_152': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_145',type,(
    '#skF_145': ( $i * $i ) > $i )).

tff('#skF_242',type,(
    '#skF_242': ( $i * $i ) > $i )).

tff('#skF_174',type,(
    '#skF_174': ( $i * $i ) > $i )).

tff('#skF_233',type,(
    '#skF_233': $i > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_249',type,(
    '#skF_249': ( $i * $i ) > $i )).

tff('#skF_63',type,(
    '#skF_63': ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) > $i )).

tff('#skF_59',type,(
    '#skF_59': ( $i * $i ) > $i )).

tff('#skF_230',type,(
    '#skF_230': $i > $i )).

tff('#skF_207',type,(
    '#skF_207': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_104',type,(
    '#skF_104': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_58',type,(
    '#skF_58': ( $i * $i ) > $i )).

tff('#skF_181',type,(
    '#skF_181': ( $i * $i ) > $i )).

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

tff('#skF_191',type,(
    '#skF_191': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#skF_62',type,(
    '#skF_62': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#skF_55',type,(
    '#skF_55': ( $i * $i ) > $i )).

tff('#skF_38',type,(
    '#skF_38': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_157',type,(
    '#skF_157': ( $i * ( $i * $i ) ) > $i )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff('#skF_21',type,(
    '#skF_21': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_101',type,(
    '#skF_101': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_179',type,(
    '#skF_179': ( $i * $i ) > $i )).

tff('#skF_243',type,(
    '#skF_243': $i > $i )).

tff('#skF_241',type,(
    '#skF_241': $i > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_226',type,(
    '#skF_226': ( $i * $i ) > $i )).

tff('#skF_177',type,(
    '#skF_177': ( $i * $i ) > $i )).

tff('#skF_120',type,(
    '#skF_120': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_102',type,(
    '#skF_102': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_105',type,(
    '#skF_105': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_40',type,(
    '#skF_40': ( $i * $i ) > $i )).

tff('#skF_214',type,(
    '#skF_214': $i > $i )).

tff('#skF_135',type,(
    '#skF_135': $i )).

tff('#skF_122',type,(
    '#skF_122': ( $i * ( $i * $i ) ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(o_2_0_relat_1,type,(
    o_2_0_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_262',type,(
    '#skF_262': ( $i * $i ) > $i )).

tff(v3_funct_1,type,(
    v3_funct_1: $i > $o )).

tff(o_1_1_relat_1,type,(
    o_1_1_relat_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * ( $i * $i ) ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) > $i )).

tff('#skF_258',type,(
    '#skF_258': $i > $i )).

tff('#skF_227',type,(
    '#skF_227': $i > $i )).

tff('#skF_147',type,(
    '#skF_147': ( $i * $i ) > $i )).

tff(o_1_2_relat_1,type,(
    o_1_2_relat_1: $i > $i )).

tff('#skF_259',type,(
    '#skF_259': ( $i * $i ) > $i )).

tff('#skF_213',type,(
    '#skF_213': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_132',type,(
    '#skF_132': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_124',type,(
    '#skF_124': ( $i * ( $i * ( $i * $i ) ) ) > $i )).

tff('#skF_29',type,(
    '#skF_29': ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * ( $i * $i ) ) ) ) ) ) ) ) ) ) > $i )).

tff('#skF_237',type,(
    '#skF_237': $i > $i )).

tff('#skF_210',type,(
    '#skF_210': ( $i * $i ) > $i )).

tff('#skF_250',type,(
    '#skF_250': ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff('#skF_129',type,(
    '#skF_129': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_150',type,(
    '#skF_150': ( $i * ( $i * $i ) ) > $i )).

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

tff('#skF_239',type,(
    '#skF_239': $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_158',type,(
    '#skF_158': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_42',type,(
    '#skF_42': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_53',type,(
    '#skF_53': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_194',type,(
    '#skF_194': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_245',type,(
    '#skF_245': ( $i * ( $i * $i ) ) > $i )).

tff(o_1_3_relat_1,type,(
    o_1_3_relat_1: $i > $i )).

tff('#skF_256',type,(
    '#skF_256': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * ( $i * $i ) ) > $i )).

tff('#skF_39',type,(
    '#skF_39': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff('#skF_246',type,(
    '#skF_246': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_109',type,(
    '#skF_109': ( $i * $i ) > $i )).

tff(f_7135,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_473,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t28_xboole_1)).

tff(f_515,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t39_xboole_1)).

tff(f_539,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t45_xboole_1)).

tff(f_475,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t29_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',antisymmetry_r2_hidden)).

tff(c_4190,plain,(
    r2_hidden('#skF_270','#skF_271') ),
    inference(cnfTransformation,[status(thm)],[f_7135])).

tff(c_4188,plain,(
    r1_tarski('#skF_271','#skF_270') ),
    inference(cnfTransformation,[status(thm)],[f_7135])).

tff(c_12881,plain,(
    ! [A_5002,B_5003] :
      ( k3_xboole_0(A_5002,B_5003) = A_5002
      | ~ r1_tarski(A_5002,B_5003) ) ),
    inference(cnfTransformation,[status(thm)],[f_473])).

tff(c_12978,plain,(
    k3_xboole_0('#skF_271','#skF_270') = '#skF_271' ),
    inference(resolution,[status(thm)],[c_4188,c_12881])).

tff(c_348,plain,(
    ! [A_242,B_243] : k2_xboole_0(A_242,k4_xboole_0(B_243,A_242)) = k2_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_515])).

tff(c_364,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,k4_xboole_0(B_261,A_260)) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_539])).

tff(c_17052,plain,(
    ! [A_5139,B_5140] :
      ( k2_xboole_0(A_5139,B_5140) = B_5140
      | ~ r1_tarski(A_5139,B_5140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_17180,plain,(
    k2_xboole_0('#skF_271','#skF_270') = '#skF_270' ),
    inference(resolution,[status(thm)],[c_4188,c_17052])).

tff(c_322,plain,(
    ! [A_213,B_214,C_215] : r1_tarski(k3_xboole_0(A_213,B_214),k2_xboole_0(A_213,C_215)) ),
    inference(cnfTransformation,[status(thm)],[f_475])).

tff(c_17247,plain,(
    ! [B_5141] : r1_tarski(k3_xboole_0('#skF_271',B_5141),'#skF_270') ),
    inference(superposition,[status(thm),theory(equality)],[c_17180,c_322])).

tff(c_4313,plain,(
    ! [A_260,B_261] :
      ( k2_xboole_0(A_260,B_261) = B_261
      | ~ r1_tarski(A_260,B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_364])).

tff(c_18119,plain,(
    ! [B_5165] : k2_xboole_0(k3_xboole_0('#skF_271',B_5165),'#skF_270') = '#skF_270' ),
    inference(resolution,[status(thm)],[c_17247,c_4313])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_xboole_0(B_6,A_5) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18865,plain,(
    ! [B_5210] : k2_xboole_0('#skF_270',k3_xboole_0('#skF_271',B_5210)) = '#skF_270' ),
    inference(superposition,[status(thm),theory(equality)],[c_18119,c_6])).

tff(c_18905,plain,(
    k2_xboole_0('#skF_270','#skF_271') = '#skF_270' ),
    inference(superposition,[status(thm),theory(equality)],[c_12978,c_18865])).

tff(c_22878,plain,(
    ! [D_5371,B_5372,A_5373] :
      ( ~ r2_hidden(D_5371,B_5372)
      | r2_hidden(D_5371,k2_xboole_0(A_5373,B_5372)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22944,plain,(
    ! [D_5371] :
      ( ~ r2_hidden(D_5371,'#skF_271')
      | r2_hidden(D_5371,'#skF_270') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18905,c_22878])).

tff(c_23184,plain,(
    ! [D_5379] :
      ( ~ r2_hidden(D_5379,'#skF_271')
      | r2_hidden(D_5379,'#skF_270') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18905,c_22878])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39070,plain,(
    ! [D_5761] :
      ( ~ r2_hidden('#skF_270',D_5761)
      | ~ r2_hidden(D_5761,'#skF_271') ) ),
    inference(resolution,[status(thm)],[c_23184,c_2])).

tff(c_39085,plain,(
    ~ r2_hidden('#skF_270','#skF_271') ),
    inference(resolution,[status(thm)],[c_22944,c_39070])).

tff(c_39143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4190,c_39085])).
%------------------------------------------------------------------------------
