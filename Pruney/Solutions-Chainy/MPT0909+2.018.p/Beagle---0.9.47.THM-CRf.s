%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:59 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 207 expanded)
%              Number of leaves         :   23 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          :  192 (1061 expanded)
%              Number of equality atoms :  136 ( 664 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_2 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_1 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ( E = k5_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = F ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_55,B_56,C_57,D_73] :
      ( m1_subset_1('#skF_5'(A_55,B_56,C_57,D_73),B_56)
      | ~ m1_subset_1(D_73,k3_zfmisc_1(A_55,B_56,C_57))
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_55,B_56,C_57,D_73] :
      ( m1_subset_1('#skF_4'(A_55,B_56,C_57,D_73),A_55)
      | ~ m1_subset_1(D_73,k3_zfmisc_1(A_55,B_56,C_57))
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_55,B_56,C_57,D_73] :
      ( m1_subset_1('#skF_6'(A_55,B_56,C_57,D_73),C_57)
      | ~ m1_subset_1(D_73,k3_zfmisc_1(A_55,B_56,C_57))
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_59,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k3_mcart_1('#skF_4'(A_143,B_144,C_145,D_146),'#skF_5'(A_143,B_144,C_145,D_146),'#skF_6'(A_143,B_144,C_145,D_146)) = D_146
      | ~ m1_subset_1(D_146,k3_zfmisc_1(A_143,B_144,C_145))
      | k1_xboole_0 = C_145
      | k1_xboole_0 = B_144
      | k1_xboole_0 = A_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [F_98,G_102,H_104] :
      ( F_98 = '#skF_10'
      | k3_mcart_1(F_98,G_102,H_104) != '#skF_11'
      | ~ m1_subset_1(H_104,'#skF_9')
      | ~ m1_subset_1(G_102,'#skF_8')
      | ~ m1_subset_1(F_98,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_109,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( '#skF_4'(A_167,B_168,C_169,D_170) = '#skF_10'
      | D_170 != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_167,B_168,C_169,D_170),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_167,B_168,C_169,D_170),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_167,B_168,C_169,D_170),'#skF_7')
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169))
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_168
      | k1_xboole_0 = A_167 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_30])).

tff(c_113,plain,(
    ! [A_55,B_56,D_73] :
      ( '#skF_4'(A_55,B_56,'#skF_9',D_73) = '#skF_10'
      | D_73 != '#skF_11'
      | ~ m1_subset_1('#skF_5'(A_55,B_56,'#skF_9',D_73),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_55,B_56,'#skF_9',D_73),'#skF_7')
      | ~ m1_subset_1(D_73,k3_zfmisc_1(A_55,B_56,'#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_195,plain,(
    ! [A_201,B_202,D_203] :
      ( '#skF_4'(A_201,B_202,'#skF_9',D_203) = '#skF_10'
      | D_203 != '#skF_11'
      | ~ m1_subset_1('#skF_5'(A_201,B_202,'#skF_9',D_203),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_201,B_202,'#skF_9',D_203),'#skF_7')
      | ~ m1_subset_1(D_203,k3_zfmisc_1(A_201,B_202,'#skF_9'))
      | k1_xboole_0 = B_202
      | k1_xboole_0 = A_201 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_113])).

tff(c_199,plain,(
    ! [B_56,D_73] :
      ( '#skF_4'('#skF_7',B_56,'#skF_9',D_73) = '#skF_10'
      | D_73 != '#skF_11'
      | ~ m1_subset_1('#skF_5'('#skF_7',B_56,'#skF_9',D_73),'#skF_8')
      | ~ m1_subset_1(D_73,k3_zfmisc_1('#skF_7',B_56,'#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = B_56
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_204,plain,(
    ! [B_204,D_205] :
      ( '#skF_4'('#skF_7',B_204,'#skF_9',D_205) = '#skF_10'
      | D_205 != '#skF_11'
      | ~ m1_subset_1('#skF_5'('#skF_7',B_204,'#skF_9',D_205),'#skF_8')
      | ~ m1_subset_1(D_205,k3_zfmisc_1('#skF_7',B_204,'#skF_9'))
      | k1_xboole_0 = B_204 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_28,c_199])).

tff(c_208,plain,(
    ! [D_73] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_9',D_73) = '#skF_10'
      | D_73 != '#skF_11'
      | ~ m1_subset_1(D_73,k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_12,c_204])).

tff(c_213,plain,(
    ! [D_206] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_9',D_206) = '#skF_10'
      | D_206 != '#skF_11'
      | ~ m1_subset_1(D_206,k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_26,c_208])).

tff(c_232,plain,(
    '#skF_4'('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32,c_213])).

tff(c_242,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_14])).

tff(c_253,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_242])).

tff(c_254,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_253])).

tff(c_8,plain,(
    ! [A_55,B_56,C_57,D_73] :
      ( k3_mcart_1('#skF_4'(A_55,B_56,C_57,D_73),'#skF_5'(A_55,B_56,C_57,D_73),'#skF_6'(A_55,B_56,C_57,D_73)) = D_73
      | ~ m1_subset_1(D_73,k3_zfmisc_1(A_55,B_56,C_57))
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_239,plain,
    ( k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_8])).

tff(c_250,plain,
    ( k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_239])).

tff(c_251,plain,(
    k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_250])).

tff(c_144,plain,(
    ! [A_200,C_199,D_198,B_197,E_196] :
      ( k3_mcart_1('#skF_1'(E_196,B_197,D_198,C_199,A_200),'#skF_2'(E_196,B_197,D_198,C_199,A_200),'#skF_3'(E_196,B_197,D_198,C_199,A_200)) = D_198
      | k5_mcart_1(A_200,B_197,C_199,D_198) = E_196
      | ~ m1_subset_1(E_196,A_200)
      | ~ m1_subset_1(D_198,k3_zfmisc_1(A_200,B_197,C_199))
      | k1_xboole_0 = C_199
      | k1_xboole_0 = B_197
      | k1_xboole_0 = A_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_85,D_88,F_90,C_87,E_89,B_86] :
      ( D_88 = A_85
      | k3_mcart_1(D_88,E_89,F_90) != k3_mcart_1(A_85,B_86,C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_407,plain,(
    ! [C_244,F_247,E_245,E_242,B_243,D_248,A_249,D_246] :
      ( D_246 = '#skF_1'(E_242,B_243,D_248,C_244,A_249)
      | k3_mcart_1(D_246,E_245,F_247) != D_248
      | k5_mcart_1(A_249,B_243,C_244,D_248) = E_242
      | ~ m1_subset_1(E_242,A_249)
      | ~ m1_subset_1(D_248,k3_zfmisc_1(A_249,B_243,C_244))
      | k1_xboole_0 = C_244
      | k1_xboole_0 = B_243
      | k1_xboole_0 = A_249 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_20])).

tff(c_465,plain,(
    ! [A_261,E_259,C_258,D_262,B_260] :
      ( '#skF_1'(E_259,B_260,D_262,C_258,A_261) = '#skF_10'
      | D_262 != '#skF_11'
      | k5_mcart_1(A_261,B_260,C_258,D_262) = E_259
      | ~ m1_subset_1(E_259,A_261)
      | ~ m1_subset_1(D_262,k3_zfmisc_1(A_261,B_260,C_258))
      | k1_xboole_0 = C_258
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_261 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_407])).

tff(c_467,plain,(
    ! [B_260,D_262,C_258] :
      ( '#skF_1'('#skF_10',B_260,D_262,C_258,'#skF_7') = '#skF_10'
      | D_262 != '#skF_11'
      | k5_mcart_1('#skF_7',B_260,C_258,D_262) = '#skF_10'
      | ~ m1_subset_1(D_262,k3_zfmisc_1('#skF_7',B_260,C_258))
      | k1_xboole_0 = C_258
      | k1_xboole_0 = B_260
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_254,c_465])).

tff(c_485,plain,(
    ! [B_266,D_267,C_268] :
      ( '#skF_1'('#skF_10',B_266,D_267,C_268,'#skF_7') = '#skF_10'
      | D_267 != '#skF_11'
      | k5_mcart_1('#skF_7',B_266,C_268,D_267) = '#skF_10'
      | ~ m1_subset_1(D_267,k3_zfmisc_1('#skF_7',B_266,C_268))
      | k1_xboole_0 = C_268
      | k1_xboole_0 = B_266 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_467])).

tff(c_500,plain,
    ( '#skF_1'('#skF_10','#skF_8','#skF_11','#skF_9','#skF_7') = '#skF_10'
    | k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32,c_485])).

tff(c_506,plain,(
    '#skF_1'('#skF_10','#skF_8','#skF_11','#skF_9','#skF_7') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_500])).

tff(c_4,plain,(
    ! [B_2,C_3,A_1,D_31,E_45] :
      ( '#skF_1'(E_45,B_2,D_31,C_3,A_1) != E_45
      | k5_mcart_1(A_1,B_2,C_3,D_31) = E_45
      | ~ m1_subset_1(E_45,A_1)
      | ~ m1_subset_1(D_31,k3_zfmisc_1(A_1,B_2,C_3))
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_512,plain,
    ( k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_4])).

tff(c_520,plain,
    ( k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_254,c_512])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:39:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.39  %$ m1_subset_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_2 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_1 > #skF_8 > #skF_5
% 2.78/1.39  
% 2.78/1.39  %Foreground sorts:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Background operators:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Foreground operators:
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.39  tff('#skF_11', type, '#skF_11': $i).
% 2.78/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.39  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.78/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.78/1.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.78/1.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.78/1.39  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.39  
% 3.01/1.41  tff(f_106, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 3.01/1.41  tff(f_74, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 3.01/1.41  tff(f_49, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (![E]: (m1_subset_1(E, A) => ((E = k5_mcart_1(A, B, C, D)) <=> (![F, G, H]: ((D = k3_mcart_1(F, G, H)) => (E = F)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_mcart_1)).
% 3.01/1.41  tff(f_82, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 3.01/1.41  tff(c_28, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.41  tff(c_26, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.41  tff(c_24, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.41  tff(c_22, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.41  tff(c_32, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.41  tff(c_12, plain, (![A_55, B_56, C_57, D_73]: (m1_subset_1('#skF_5'(A_55, B_56, C_57, D_73), B_56) | ~m1_subset_1(D_73, k3_zfmisc_1(A_55, B_56, C_57)) | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.41  tff(c_14, plain, (![A_55, B_56, C_57, D_73]: (m1_subset_1('#skF_4'(A_55, B_56, C_57, D_73), A_55) | ~m1_subset_1(D_73, k3_zfmisc_1(A_55, B_56, C_57)) | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.41  tff(c_10, plain, (![A_55, B_56, C_57, D_73]: (m1_subset_1('#skF_6'(A_55, B_56, C_57, D_73), C_57) | ~m1_subset_1(D_73, k3_zfmisc_1(A_55, B_56, C_57)) | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.41  tff(c_59, plain, (![A_143, B_144, C_145, D_146]: (k3_mcart_1('#skF_4'(A_143, B_144, C_145, D_146), '#skF_5'(A_143, B_144, C_145, D_146), '#skF_6'(A_143, B_144, C_145, D_146))=D_146 | ~m1_subset_1(D_146, k3_zfmisc_1(A_143, B_144, C_145)) | k1_xboole_0=C_145 | k1_xboole_0=B_144 | k1_xboole_0=A_143)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.41  tff(c_30, plain, (![F_98, G_102, H_104]: (F_98='#skF_10' | k3_mcart_1(F_98, G_102, H_104)!='#skF_11' | ~m1_subset_1(H_104, '#skF_9') | ~m1_subset_1(G_102, '#skF_8') | ~m1_subset_1(F_98, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.01/1.41  tff(c_109, plain, (![A_167, B_168, C_169, D_170]: ('#skF_4'(A_167, B_168, C_169, D_170)='#skF_10' | D_170!='#skF_11' | ~m1_subset_1('#skF_6'(A_167, B_168, C_169, D_170), '#skF_9') | ~m1_subset_1('#skF_5'(A_167, B_168, C_169, D_170), '#skF_8') | ~m1_subset_1('#skF_4'(A_167, B_168, C_169, D_170), '#skF_7') | ~m1_subset_1(D_170, k3_zfmisc_1(A_167, B_168, C_169)) | k1_xboole_0=C_169 | k1_xboole_0=B_168 | k1_xboole_0=A_167)), inference(superposition, [status(thm), theory('equality')], [c_59, c_30])).
% 3.01/1.41  tff(c_113, plain, (![A_55, B_56, D_73]: ('#skF_4'(A_55, B_56, '#skF_9', D_73)='#skF_10' | D_73!='#skF_11' | ~m1_subset_1('#skF_5'(A_55, B_56, '#skF_9', D_73), '#skF_8') | ~m1_subset_1('#skF_4'(A_55, B_56, '#skF_9', D_73), '#skF_7') | ~m1_subset_1(D_73, k3_zfmisc_1(A_55, B_56, '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(resolution, [status(thm)], [c_10, c_109])).
% 3.01/1.41  tff(c_195, plain, (![A_201, B_202, D_203]: ('#skF_4'(A_201, B_202, '#skF_9', D_203)='#skF_10' | D_203!='#skF_11' | ~m1_subset_1('#skF_5'(A_201, B_202, '#skF_9', D_203), '#skF_8') | ~m1_subset_1('#skF_4'(A_201, B_202, '#skF_9', D_203), '#skF_7') | ~m1_subset_1(D_203, k3_zfmisc_1(A_201, B_202, '#skF_9')) | k1_xboole_0=B_202 | k1_xboole_0=A_201)), inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_113])).
% 3.01/1.41  tff(c_199, plain, (![B_56, D_73]: ('#skF_4'('#skF_7', B_56, '#skF_9', D_73)='#skF_10' | D_73!='#skF_11' | ~m1_subset_1('#skF_5'('#skF_7', B_56, '#skF_9', D_73), '#skF_8') | ~m1_subset_1(D_73, k3_zfmisc_1('#skF_7', B_56, '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0=B_56 | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_14, c_195])).
% 3.01/1.41  tff(c_204, plain, (![B_204, D_205]: ('#skF_4'('#skF_7', B_204, '#skF_9', D_205)='#skF_10' | D_205!='#skF_11' | ~m1_subset_1('#skF_5'('#skF_7', B_204, '#skF_9', D_205), '#skF_8') | ~m1_subset_1(D_205, k3_zfmisc_1('#skF_7', B_204, '#skF_9')) | k1_xboole_0=B_204)), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_28, c_199])).
% 3.01/1.41  tff(c_208, plain, (![D_73]: ('#skF_4'('#skF_7', '#skF_8', '#skF_9', D_73)='#skF_10' | D_73!='#skF_11' | ~m1_subset_1(D_73, k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_12, c_204])).
% 3.01/1.41  tff(c_213, plain, (![D_206]: ('#skF_4'('#skF_7', '#skF_8', '#skF_9', D_206)='#skF_10' | D_206!='#skF_11' | ~m1_subset_1(D_206, k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_26, c_208])).
% 3.01/1.41  tff(c_232, plain, ('#skF_4'('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10'), inference(resolution, [status(thm)], [c_32, c_213])).
% 3.01/1.41  tff(c_242, plain, (m1_subset_1('#skF_10', '#skF_7') | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_232, c_14])).
% 3.01/1.41  tff(c_253, plain, (m1_subset_1('#skF_10', '#skF_7') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_242])).
% 3.01/1.41  tff(c_254, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_253])).
% 3.01/1.41  tff(c_8, plain, (![A_55, B_56, C_57, D_73]: (k3_mcart_1('#skF_4'(A_55, B_56, C_57, D_73), '#skF_5'(A_55, B_56, C_57, D_73), '#skF_6'(A_55, B_56, C_57, D_73))=D_73 | ~m1_subset_1(D_73, k3_zfmisc_1(A_55, B_56, C_57)) | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.41  tff(c_239, plain, (k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_232, c_8])).
% 3.01/1.41  tff(c_250, plain, (k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_239])).
% 3.01/1.41  tff(c_251, plain, (k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_250])).
% 3.01/1.41  tff(c_144, plain, (![A_200, C_199, D_198, B_197, E_196]: (k3_mcart_1('#skF_1'(E_196, B_197, D_198, C_199, A_200), '#skF_2'(E_196, B_197, D_198, C_199, A_200), '#skF_3'(E_196, B_197, D_198, C_199, A_200))=D_198 | k5_mcart_1(A_200, B_197, C_199, D_198)=E_196 | ~m1_subset_1(E_196, A_200) | ~m1_subset_1(D_198, k3_zfmisc_1(A_200, B_197, C_199)) | k1_xboole_0=C_199 | k1_xboole_0=B_197 | k1_xboole_0=A_200)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.41  tff(c_20, plain, (![A_85, D_88, F_90, C_87, E_89, B_86]: (D_88=A_85 | k3_mcart_1(D_88, E_89, F_90)!=k3_mcart_1(A_85, B_86, C_87))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.01/1.41  tff(c_407, plain, (![C_244, F_247, E_245, E_242, B_243, D_248, A_249, D_246]: (D_246='#skF_1'(E_242, B_243, D_248, C_244, A_249) | k3_mcart_1(D_246, E_245, F_247)!=D_248 | k5_mcart_1(A_249, B_243, C_244, D_248)=E_242 | ~m1_subset_1(E_242, A_249) | ~m1_subset_1(D_248, k3_zfmisc_1(A_249, B_243, C_244)) | k1_xboole_0=C_244 | k1_xboole_0=B_243 | k1_xboole_0=A_249)), inference(superposition, [status(thm), theory('equality')], [c_144, c_20])).
% 3.01/1.41  tff(c_465, plain, (![A_261, E_259, C_258, D_262, B_260]: ('#skF_1'(E_259, B_260, D_262, C_258, A_261)='#skF_10' | D_262!='#skF_11' | k5_mcart_1(A_261, B_260, C_258, D_262)=E_259 | ~m1_subset_1(E_259, A_261) | ~m1_subset_1(D_262, k3_zfmisc_1(A_261, B_260, C_258)) | k1_xboole_0=C_258 | k1_xboole_0=B_260 | k1_xboole_0=A_261)), inference(superposition, [status(thm), theory('equality')], [c_251, c_407])).
% 3.01/1.41  tff(c_467, plain, (![B_260, D_262, C_258]: ('#skF_1'('#skF_10', B_260, D_262, C_258, '#skF_7')='#skF_10' | D_262!='#skF_11' | k5_mcart_1('#skF_7', B_260, C_258, D_262)='#skF_10' | ~m1_subset_1(D_262, k3_zfmisc_1('#skF_7', B_260, C_258)) | k1_xboole_0=C_258 | k1_xboole_0=B_260 | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_254, c_465])).
% 3.01/1.41  tff(c_485, plain, (![B_266, D_267, C_268]: ('#skF_1'('#skF_10', B_266, D_267, C_268, '#skF_7')='#skF_10' | D_267!='#skF_11' | k5_mcart_1('#skF_7', B_266, C_268, D_267)='#skF_10' | ~m1_subset_1(D_267, k3_zfmisc_1('#skF_7', B_266, C_268)) | k1_xboole_0=C_268 | k1_xboole_0=B_266)), inference(negUnitSimplification, [status(thm)], [c_28, c_467])).
% 3.01/1.41  tff(c_500, plain, ('#skF_1'('#skF_10', '#skF_8', '#skF_11', '#skF_9', '#skF_7')='#skF_10' | k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_32, c_485])).
% 3.01/1.41  tff(c_506, plain, ('#skF_1'('#skF_10', '#skF_8', '#skF_11', '#skF_9', '#skF_7')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_500])).
% 3.01/1.41  tff(c_4, plain, (![B_2, C_3, A_1, D_31, E_45]: ('#skF_1'(E_45, B_2, D_31, C_3, A_1)!=E_45 | k5_mcart_1(A_1, B_2, C_3, D_31)=E_45 | ~m1_subset_1(E_45, A_1) | ~m1_subset_1(D_31, k3_zfmisc_1(A_1, B_2, C_3)) | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.41  tff(c_512, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_506, c_4])).
% 3.01/1.41  tff(c_520, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_254, c_512])).
% 3.01/1.41  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_520])).
% 3.01/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.41  
% 3.01/1.41  Inference rules
% 3.01/1.41  ----------------------
% 3.01/1.41  #Ref     : 8
% 3.01/1.41  #Sup     : 103
% 3.01/1.41  #Fact    : 0
% 3.01/1.41  #Define  : 0
% 3.01/1.41  #Split   : 0
% 3.01/1.41  #Chain   : 0
% 3.01/1.41  #Close   : 0
% 3.01/1.41  
% 3.01/1.41  Ordering : KBO
% 3.01/1.41  
% 3.01/1.41  Simplification rules
% 3.01/1.41  ----------------------
% 3.01/1.41  #Subsume      : 12
% 3.01/1.41  #Demod        : 16
% 3.01/1.41  #Tautology    : 23
% 3.01/1.41  #SimpNegUnit  : 16
% 3.01/1.41  #BackRed      : 0
% 3.01/1.41  
% 3.01/1.41  #Partial instantiations: 0
% 3.01/1.41  #Strategies tried      : 1
% 3.01/1.41  
% 3.01/1.41  Timing (in seconds)
% 3.01/1.41  ----------------------
% 3.01/1.41  Preprocessing        : 0.30
% 3.01/1.41  Parsing              : 0.15
% 3.01/1.41  CNF conversion       : 0.03
% 3.01/1.41  Main loop            : 0.33
% 3.01/1.41  Inferencing          : 0.13
% 3.01/1.41  Reduction            : 0.07
% 3.01/1.41  Demodulation         : 0.04
% 3.01/1.41  BG Simplification    : 0.03
% 3.01/1.41  Subsumption          : 0.09
% 3.01/1.41  Abstraction          : 0.02
% 3.01/1.41  MUC search           : 0.00
% 3.01/1.41  Cooper               : 0.00
% 3.01/1.41  Total                : 0.66
% 3.01/1.41  Index Insertion      : 0.00
% 3.01/1.41  Index Deletion       : 0.00
% 3.01/1.41  Index Matching       : 0.00
% 3.01/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
