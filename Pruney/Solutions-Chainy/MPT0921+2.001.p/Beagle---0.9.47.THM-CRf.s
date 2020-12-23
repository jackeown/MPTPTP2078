%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:17 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 262 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          :  248 (1617 expanded)
%              Number of equality atoms :  178 ( 999 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_6 > #skF_5 > #skF_10 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_9 > #skF_3 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = I ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k10_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ! [F] :
                ( m1_subset_1(F,A)
               => ! [G] :
                    ( m1_subset_1(G,B)
                   => ! [H] :
                        ( m1_subset_1(H,C)
                       => ! [I] :
                            ( m1_subset_1(I,D)
                           => E != k4_mcart_1(F,G,H,I) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ! [F] :
                  ( m1_subset_1(F,C)
                 => ( F = k10_mcart_1(A,B,C,D,E)
                  <=> ! [G,H,I,J] :
                        ( E = k4_mcart_1(G,H,I,J)
                       => F = I ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
     => ( A = E
        & B = F
        & C = G
        & D = H ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    k10_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_12,plain,(
    ! [D_74,C_73,B_72,E_106,A_71] :
      ( m1_subset_1('#skF_7'(E_106,A_71,B_72,D_74,C_73),C_73)
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_71,B_72,C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [D_74,C_73,B_72,E_106,A_71] :
      ( m1_subset_1('#skF_8'(E_106,A_71,B_72,D_74,C_73),D_74)
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_71,B_72,C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    ! [D_74,C_73,B_72,E_106,A_71] :
      ( m1_subset_1('#skF_5'(E_106,A_71,B_72,D_74,C_73),A_71)
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_71,B_72,C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [D_74,C_73,B_72,E_106,A_71] :
      ( m1_subset_1('#skF_6'(E_106,A_71,B_72,D_74,C_73),B_72)
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_71,B_72,C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    ! [C_237,A_234,E_233,D_236,B_235] :
      ( k4_mcart_1('#skF_5'(E_233,A_234,B_235,D_236,C_237),'#skF_6'(E_233,A_234,B_235,D_236,C_237),'#skF_7'(E_233,A_234,B_235,D_236,C_237),'#skF_8'(E_233,A_234,B_235,D_236,C_237)) = E_233
      | ~ m1_subset_1(E_233,k4_zfmisc_1(A_234,B_235,C_237,D_236))
      | k1_xboole_0 = D_236
      | k1_xboole_0 = C_237
      | k1_xboole_0 = B_235
      | k1_xboole_0 = A_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [I_168,G_156,H_164,J_170] :
      ( I_168 = '#skF_13'
      | k4_mcart_1(G_156,H_164,I_168,J_170) != '#skF_14'
      | ~ m1_subset_1(J_170,'#skF_12')
      | ~ m1_subset_1(I_168,'#skF_11')
      | ~ m1_subset_1(H_164,'#skF_10')
      | ~ m1_subset_1(G_156,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_125,plain,(
    ! [C_256,B_260,D_258,A_259,E_257] :
      ( '#skF_7'(E_257,A_259,B_260,D_258,C_256) = '#skF_13'
      | E_257 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(E_257,A_259,B_260,D_258,C_256),'#skF_12')
      | ~ m1_subset_1('#skF_7'(E_257,A_259,B_260,D_258,C_256),'#skF_11')
      | ~ m1_subset_1('#skF_6'(E_257,A_259,B_260,D_258,C_256),'#skF_10')
      | ~ m1_subset_1('#skF_5'(E_257,A_259,B_260,D_258,C_256),'#skF_9')
      | ~ m1_subset_1(E_257,k4_zfmisc_1(A_259,B_260,C_256,D_258))
      | k1_xboole_0 = D_258
      | k1_xboole_0 = C_256
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_259 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_36])).

tff(c_129,plain,(
    ! [E_106,A_71,D_74,C_73] :
      ( '#skF_7'(E_106,A_71,'#skF_10',D_74,C_73) = '#skF_13'
      | E_106 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(E_106,A_71,'#skF_10',D_74,C_73),'#skF_12')
      | ~ m1_subset_1('#skF_7'(E_106,A_71,'#skF_10',D_74,C_73),'#skF_11')
      | ~ m1_subset_1('#skF_5'(E_106,A_71,'#skF_10',D_74,C_73),'#skF_9')
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_71,'#skF_10',C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_162,plain,(
    ! [E_303,A_304,D_305,C_306] :
      ( '#skF_7'(E_303,A_304,'#skF_10',D_305,C_306) = '#skF_13'
      | E_303 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(E_303,A_304,'#skF_10',D_305,C_306),'#skF_12')
      | ~ m1_subset_1('#skF_7'(E_303,A_304,'#skF_10',D_305,C_306),'#skF_11')
      | ~ m1_subset_1('#skF_5'(E_303,A_304,'#skF_10',D_305,C_306),'#skF_9')
      | ~ m1_subset_1(E_303,k4_zfmisc_1(A_304,'#skF_10',C_306,D_305))
      | k1_xboole_0 = D_305
      | k1_xboole_0 = C_306
      | k1_xboole_0 = A_304 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_129])).

tff(c_166,plain,(
    ! [E_106,D_74,C_73] :
      ( '#skF_7'(E_106,'#skF_9','#skF_10',D_74,C_73) = '#skF_13'
      | E_106 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(E_106,'#skF_9','#skF_10',D_74,C_73),'#skF_12')
      | ~ m1_subset_1('#skF_7'(E_106,'#skF_9','#skF_10',D_74,C_73),'#skF_11')
      | ~ m1_subset_1(E_106,k4_zfmisc_1('#skF_9','#skF_10',C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_16,c_162])).

tff(c_179,plain,(
    ! [E_323,D_324,C_325] :
      ( '#skF_7'(E_323,'#skF_9','#skF_10',D_324,C_325) = '#skF_13'
      | E_323 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(E_323,'#skF_9','#skF_10',D_324,C_325),'#skF_12')
      | ~ m1_subset_1('#skF_7'(E_323,'#skF_9','#skF_10',D_324,C_325),'#skF_11')
      | ~ m1_subset_1(E_323,k4_zfmisc_1('#skF_9','#skF_10',C_325,D_324))
      | k1_xboole_0 = D_324
      | k1_xboole_0 = C_325 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_34,c_166])).

tff(c_183,plain,(
    ! [E_106,C_73] :
      ( '#skF_7'(E_106,'#skF_9','#skF_10','#skF_12',C_73) = '#skF_13'
      | E_106 != '#skF_14'
      | ~ m1_subset_1('#skF_7'(E_106,'#skF_9','#skF_10','#skF_12',C_73),'#skF_11')
      | ~ m1_subset_1(E_106,k4_zfmisc_1('#skF_9','#skF_10',C_73,'#skF_12'))
      | k1_xboole_0 = '#skF_12'
      | k1_xboole_0 = C_73
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_10,c_179])).

tff(c_188,plain,(
    ! [E_326,C_327] :
      ( '#skF_7'(E_326,'#skF_9','#skF_10','#skF_12',C_327) = '#skF_13'
      | E_326 != '#skF_14'
      | ~ m1_subset_1('#skF_7'(E_326,'#skF_9','#skF_10','#skF_12',C_327),'#skF_11')
      | ~ m1_subset_1(E_326,k4_zfmisc_1('#skF_9','#skF_10',C_327,'#skF_12'))
      | k1_xboole_0 = C_327 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_28,c_28,c_183])).

tff(c_192,plain,(
    ! [E_106] :
      ( '#skF_7'(E_106,'#skF_9','#skF_10','#skF_12','#skF_11') = '#skF_13'
      | E_106 != '#skF_14'
      | ~ m1_subset_1(E_106,k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
      | k1_xboole_0 = '#skF_12'
      | k1_xboole_0 = '#skF_11'
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_197,plain,(
    ! [E_328] :
      ( '#skF_7'(E_328,'#skF_9','#skF_10','#skF_12','#skF_11') = '#skF_13'
      | E_328 != '#skF_14'
      | ~ m1_subset_1(E_328,k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_30,c_192])).

tff(c_221,plain,(
    '#skF_7'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_38,c_197])).

tff(c_302,plain,
    ( m1_subset_1('#skF_13','#skF_11')
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_12])).

tff(c_313,plain,
    ( m1_subset_1('#skF_13','#skF_11')
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_302])).

tff(c_314,plain,(
    m1_subset_1('#skF_13','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_313])).

tff(c_8,plain,(
    ! [D_74,C_73,B_72,E_106,A_71] :
      ( k4_mcart_1('#skF_5'(E_106,A_71,B_72,D_74,C_73),'#skF_6'(E_106,A_71,B_72,D_74,C_73),'#skF_7'(E_106,A_71,B_72,D_74,C_73),'#skF_8'(E_106,A_71,B_72,D_74,C_73)) = E_106
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_71,B_72,C_73,D_74))
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_299,plain,
    ( k4_mcart_1('#skF_5'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_6'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_13','#skF_8'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11')) = '#skF_14'
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_8])).

tff(c_310,plain,
    ( k4_mcart_1('#skF_5'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_6'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_13','#skF_8'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11')) = '#skF_14'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_299])).

tff(c_311,plain,(
    k4_mcart_1('#skF_5'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_6'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_13','#skF_8'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11')) = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_310])).

tff(c_231,plain,(
    ! [C_331,B_330,A_332,E_333,F_334,D_329] :
      ( k4_mcart_1('#skF_1'(D_329,B_330,C_331,A_332,E_333,F_334),'#skF_2'(D_329,B_330,C_331,A_332,E_333,F_334),'#skF_3'(D_329,B_330,C_331,A_332,E_333,F_334),'#skF_4'(D_329,B_330,C_331,A_332,E_333,F_334)) = E_333
      | k10_mcart_1(A_332,B_330,C_331,D_329,E_333) = F_334
      | ~ m1_subset_1(F_334,C_331)
      | ~ m1_subset_1(E_333,k4_zfmisc_1(A_332,B_330,C_331,D_329))
      | k1_xboole_0 = D_329
      | k1_xboole_0 = C_331
      | k1_xboole_0 = B_330
      | k1_xboole_0 = A_332 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [H_140,A_133,F_138,E_137,D_136,G_139,B_134,C_135] :
      ( G_139 = C_135
      | k4_mcart_1(E_137,F_138,G_139,H_140) != k4_mcart_1(A_133,B_134,C_135,D_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_420,plain,(
    ! [D_361,C_353,B_357,B_356,F_362,A_354,C_355,A_360,E_359,D_358] :
      ( C_355 = '#skF_3'(D_358,B_357,C_353,A_360,E_359,F_362)
      | k4_mcart_1(A_354,B_356,C_355,D_361) != E_359
      | k10_mcart_1(A_360,B_357,C_353,D_358,E_359) = F_362
      | ~ m1_subset_1(F_362,C_353)
      | ~ m1_subset_1(E_359,k4_zfmisc_1(A_360,B_357,C_353,D_358))
      | k1_xboole_0 = D_358
      | k1_xboole_0 = C_353
      | k1_xboole_0 = B_357
      | k1_xboole_0 = A_360 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_20])).

tff(c_601,plain,(
    ! [F_416,E_414,D_413,A_418,B_417,C_415] :
      ( '#skF_3'(D_413,B_417,C_415,A_418,E_414,F_416) = '#skF_13'
      | E_414 != '#skF_14'
      | k10_mcart_1(A_418,B_417,C_415,D_413,E_414) = F_416
      | ~ m1_subset_1(F_416,C_415)
      | ~ m1_subset_1(E_414,k4_zfmisc_1(A_418,B_417,C_415,D_413))
      | k1_xboole_0 = D_413
      | k1_xboole_0 = C_415
      | k1_xboole_0 = B_417
      | k1_xboole_0 = A_418 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_420])).

tff(c_603,plain,(
    ! [D_413,B_417,A_418,E_414] :
      ( '#skF_3'(D_413,B_417,'#skF_11',A_418,E_414,'#skF_13') = '#skF_13'
      | E_414 != '#skF_14'
      | k10_mcart_1(A_418,B_417,'#skF_11',D_413,E_414) = '#skF_13'
      | ~ m1_subset_1(E_414,k4_zfmisc_1(A_418,B_417,'#skF_11',D_413))
      | k1_xboole_0 = D_413
      | k1_xboole_0 = '#skF_11'
      | k1_xboole_0 = B_417
      | k1_xboole_0 = A_418 ) ),
    inference(resolution,[status(thm)],[c_314,c_601])).

tff(c_624,plain,(
    ! [D_423,B_424,A_425,E_426] :
      ( '#skF_3'(D_423,B_424,'#skF_11',A_425,E_426,'#skF_13') = '#skF_13'
      | E_426 != '#skF_14'
      | k10_mcart_1(A_425,B_424,'#skF_11',D_423,E_426) = '#skF_13'
      | ~ m1_subset_1(E_426,k4_zfmisc_1(A_425,B_424,'#skF_11',D_423))
      | k1_xboole_0 = D_423
      | k1_xboole_0 = B_424
      | k1_xboole_0 = A_425 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_603])).

tff(c_643,plain,
    ( '#skF_3'('#skF_12','#skF_10','#skF_11','#skF_9','#skF_14','#skF_13') = '#skF_13'
    | k10_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_624])).

tff(c_650,plain,(
    '#skF_3'('#skF_12','#skF_10','#skF_11','#skF_9','#skF_14','#skF_13') = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_28,c_26,c_643])).

tff(c_4,plain,(
    ! [B_2,C_3,E_40,A_1,D_4,F_58] :
      ( '#skF_3'(D_4,B_2,C_3,A_1,E_40,F_58) != F_58
      | k10_mcart_1(A_1,B_2,C_3,D_4,E_40) = F_58
      | ~ m1_subset_1(F_58,C_3)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_669,plain,
    ( k10_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | ~ m1_subset_1('#skF_13','#skF_11')
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_4])).

tff(c_677,plain,
    ( k10_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_314,c_669])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_26,c_677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.53  
% 3.62/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.54  %$ m1_subset_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_6 > #skF_5 > #skF_10 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_9 > #skF_3 > #skF_12 > #skF_4
% 3.62/1.54  
% 3.62/1.54  %Foreground sorts:
% 3.62/1.54  
% 3.62/1.54  
% 3.62/1.54  %Background operators:
% 3.62/1.54  
% 3.62/1.54  
% 3.62/1.54  %Foreground operators:
% 3.62/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_11', type, '#skF_11': $i).
% 3.62/1.54  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.54  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_10', type, '#skF_10': $i).
% 3.62/1.54  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_14', type, '#skF_14': $i).
% 3.62/1.54  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_13', type, '#skF_13': $i).
% 3.62/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.62/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.54  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.62/1.54  tff('#skF_12', type, '#skF_12': $i).
% 3.62/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.54  
% 3.68/1.55  tff(f_122, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_mcart_1)).
% 3.68/1.55  tff(f_83, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.68/1.55  tff(f_52, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, C) => ((F = k10_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = I)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_mcart_1)).
% 3.68/1.55  tff(f_93, axiom, (![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.68/1.55  tff(c_34, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_32, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_30, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_28, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_26, plain, (k10_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_38, plain, (m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_12, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_7'(E_106, A_71, B_72, D_74, C_73), C_73) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.55  tff(c_10, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_8'(E_106, A_71, B_72, D_74, C_73), D_74) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.55  tff(c_16, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_5'(E_106, A_71, B_72, D_74, C_73), A_71) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.55  tff(c_14, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_6'(E_106, A_71, B_72, D_74, C_73), B_72) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.55  tff(c_73, plain, (![C_237, A_234, E_233, D_236, B_235]: (k4_mcart_1('#skF_5'(E_233, A_234, B_235, D_236, C_237), '#skF_6'(E_233, A_234, B_235, D_236, C_237), '#skF_7'(E_233, A_234, B_235, D_236, C_237), '#skF_8'(E_233, A_234, B_235, D_236, C_237))=E_233 | ~m1_subset_1(E_233, k4_zfmisc_1(A_234, B_235, C_237, D_236)) | k1_xboole_0=D_236 | k1_xboole_0=C_237 | k1_xboole_0=B_235 | k1_xboole_0=A_234)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.55  tff(c_36, plain, (![I_168, G_156, H_164, J_170]: (I_168='#skF_13' | k4_mcart_1(G_156, H_164, I_168, J_170)!='#skF_14' | ~m1_subset_1(J_170, '#skF_12') | ~m1_subset_1(I_168, '#skF_11') | ~m1_subset_1(H_164, '#skF_10') | ~m1_subset_1(G_156, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.55  tff(c_125, plain, (![C_256, B_260, D_258, A_259, E_257]: ('#skF_7'(E_257, A_259, B_260, D_258, C_256)='#skF_13' | E_257!='#skF_14' | ~m1_subset_1('#skF_8'(E_257, A_259, B_260, D_258, C_256), '#skF_12') | ~m1_subset_1('#skF_7'(E_257, A_259, B_260, D_258, C_256), '#skF_11') | ~m1_subset_1('#skF_6'(E_257, A_259, B_260, D_258, C_256), '#skF_10') | ~m1_subset_1('#skF_5'(E_257, A_259, B_260, D_258, C_256), '#skF_9') | ~m1_subset_1(E_257, k4_zfmisc_1(A_259, B_260, C_256, D_258)) | k1_xboole_0=D_258 | k1_xboole_0=C_256 | k1_xboole_0=B_260 | k1_xboole_0=A_259)), inference(superposition, [status(thm), theory('equality')], [c_73, c_36])).
% 3.68/1.55  tff(c_129, plain, (![E_106, A_71, D_74, C_73]: ('#skF_7'(E_106, A_71, '#skF_10', D_74, C_73)='#skF_13' | E_106!='#skF_14' | ~m1_subset_1('#skF_8'(E_106, A_71, '#skF_10', D_74, C_73), '#skF_12') | ~m1_subset_1('#skF_7'(E_106, A_71, '#skF_10', D_74, C_73), '#skF_11') | ~m1_subset_1('#skF_5'(E_106, A_71, '#skF_10', D_74, C_73), '#skF_9') | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, '#skF_10', C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0='#skF_10' | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_14, c_125])).
% 3.68/1.55  tff(c_162, plain, (![E_303, A_304, D_305, C_306]: ('#skF_7'(E_303, A_304, '#skF_10', D_305, C_306)='#skF_13' | E_303!='#skF_14' | ~m1_subset_1('#skF_8'(E_303, A_304, '#skF_10', D_305, C_306), '#skF_12') | ~m1_subset_1('#skF_7'(E_303, A_304, '#skF_10', D_305, C_306), '#skF_11') | ~m1_subset_1('#skF_5'(E_303, A_304, '#skF_10', D_305, C_306), '#skF_9') | ~m1_subset_1(E_303, k4_zfmisc_1(A_304, '#skF_10', C_306, D_305)) | k1_xboole_0=D_305 | k1_xboole_0=C_306 | k1_xboole_0=A_304)), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_129])).
% 3.68/1.55  tff(c_166, plain, (![E_106, D_74, C_73]: ('#skF_7'(E_106, '#skF_9', '#skF_10', D_74, C_73)='#skF_13' | E_106!='#skF_14' | ~m1_subset_1('#skF_8'(E_106, '#skF_9', '#skF_10', D_74, C_73), '#skF_12') | ~m1_subset_1('#skF_7'(E_106, '#skF_9', '#skF_10', D_74, C_73), '#skF_11') | ~m1_subset_1(E_106, k4_zfmisc_1('#skF_9', '#skF_10', C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_16, c_162])).
% 3.68/1.55  tff(c_179, plain, (![E_323, D_324, C_325]: ('#skF_7'(E_323, '#skF_9', '#skF_10', D_324, C_325)='#skF_13' | E_323!='#skF_14' | ~m1_subset_1('#skF_8'(E_323, '#skF_9', '#skF_10', D_324, C_325), '#skF_12') | ~m1_subset_1('#skF_7'(E_323, '#skF_9', '#skF_10', D_324, C_325), '#skF_11') | ~m1_subset_1(E_323, k4_zfmisc_1('#skF_9', '#skF_10', C_325, D_324)) | k1_xboole_0=D_324 | k1_xboole_0=C_325)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_34, c_166])).
% 3.68/1.55  tff(c_183, plain, (![E_106, C_73]: ('#skF_7'(E_106, '#skF_9', '#skF_10', '#skF_12', C_73)='#skF_13' | E_106!='#skF_14' | ~m1_subset_1('#skF_7'(E_106, '#skF_9', '#skF_10', '#skF_12', C_73), '#skF_11') | ~m1_subset_1(E_106, k4_zfmisc_1('#skF_9', '#skF_10', C_73, '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0=C_73 | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_10, c_179])).
% 3.68/1.55  tff(c_188, plain, (![E_326, C_327]: ('#skF_7'(E_326, '#skF_9', '#skF_10', '#skF_12', C_327)='#skF_13' | E_326!='#skF_14' | ~m1_subset_1('#skF_7'(E_326, '#skF_9', '#skF_10', '#skF_12', C_327), '#skF_11') | ~m1_subset_1(E_326, k4_zfmisc_1('#skF_9', '#skF_10', C_327, '#skF_12')) | k1_xboole_0=C_327)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_28, c_28, c_183])).
% 3.68/1.55  tff(c_192, plain, (![E_106]: ('#skF_7'(E_106, '#skF_9', '#skF_10', '#skF_12', '#skF_11')='#skF_13' | E_106!='#skF_14' | ~m1_subset_1(E_106, k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_12, c_188])).
% 3.68/1.55  tff(c_197, plain, (![E_328]: ('#skF_7'(E_328, '#skF_9', '#skF_10', '#skF_12', '#skF_11')='#skF_13' | E_328!='#skF_14' | ~m1_subset_1(E_328, k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_30, c_192])).
% 3.68/1.55  tff(c_221, plain, ('#skF_7'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11')='#skF_13'), inference(resolution, [status(thm)], [c_38, c_197])).
% 3.68/1.55  tff(c_302, plain, (m1_subset_1('#skF_13', '#skF_11') | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_221, c_12])).
% 3.68/1.55  tff(c_313, plain, (m1_subset_1('#skF_13', '#skF_11') | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_302])).
% 3.68/1.55  tff(c_314, plain, (m1_subset_1('#skF_13', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_313])).
% 3.68/1.55  tff(c_8, plain, (![D_74, C_73, B_72, E_106, A_71]: (k4_mcart_1('#skF_5'(E_106, A_71, B_72, D_74, C_73), '#skF_6'(E_106, A_71, B_72, D_74, C_73), '#skF_7'(E_106, A_71, B_72, D_74, C_73), '#skF_8'(E_106, A_71, B_72, D_74, C_73))=E_106 | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.55  tff(c_299, plain, (k4_mcart_1('#skF_5'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_6'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_13', '#skF_8'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'))='#skF_14' | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_221, c_8])).
% 3.68/1.55  tff(c_310, plain, (k4_mcart_1('#skF_5'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_6'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_13', '#skF_8'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'))='#skF_14' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_299])).
% 3.68/1.55  tff(c_311, plain, (k4_mcart_1('#skF_5'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_6'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_13', '#skF_8'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'))='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_310])).
% 3.68/1.55  tff(c_231, plain, (![C_331, B_330, A_332, E_333, F_334, D_329]: (k4_mcart_1('#skF_1'(D_329, B_330, C_331, A_332, E_333, F_334), '#skF_2'(D_329, B_330, C_331, A_332, E_333, F_334), '#skF_3'(D_329, B_330, C_331, A_332, E_333, F_334), '#skF_4'(D_329, B_330, C_331, A_332, E_333, F_334))=E_333 | k10_mcart_1(A_332, B_330, C_331, D_329, E_333)=F_334 | ~m1_subset_1(F_334, C_331) | ~m1_subset_1(E_333, k4_zfmisc_1(A_332, B_330, C_331, D_329)) | k1_xboole_0=D_329 | k1_xboole_0=C_331 | k1_xboole_0=B_330 | k1_xboole_0=A_332)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.55  tff(c_20, plain, (![H_140, A_133, F_138, E_137, D_136, G_139, B_134, C_135]: (G_139=C_135 | k4_mcart_1(E_137, F_138, G_139, H_140)!=k4_mcart_1(A_133, B_134, C_135, D_136))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.68/1.55  tff(c_420, plain, (![D_361, C_353, B_357, B_356, F_362, A_354, C_355, A_360, E_359, D_358]: (C_355='#skF_3'(D_358, B_357, C_353, A_360, E_359, F_362) | k4_mcart_1(A_354, B_356, C_355, D_361)!=E_359 | k10_mcart_1(A_360, B_357, C_353, D_358, E_359)=F_362 | ~m1_subset_1(F_362, C_353) | ~m1_subset_1(E_359, k4_zfmisc_1(A_360, B_357, C_353, D_358)) | k1_xboole_0=D_358 | k1_xboole_0=C_353 | k1_xboole_0=B_357 | k1_xboole_0=A_360)), inference(superposition, [status(thm), theory('equality')], [c_231, c_20])).
% 3.68/1.55  tff(c_601, plain, (![F_416, E_414, D_413, A_418, B_417, C_415]: ('#skF_3'(D_413, B_417, C_415, A_418, E_414, F_416)='#skF_13' | E_414!='#skF_14' | k10_mcart_1(A_418, B_417, C_415, D_413, E_414)=F_416 | ~m1_subset_1(F_416, C_415) | ~m1_subset_1(E_414, k4_zfmisc_1(A_418, B_417, C_415, D_413)) | k1_xboole_0=D_413 | k1_xboole_0=C_415 | k1_xboole_0=B_417 | k1_xboole_0=A_418)), inference(superposition, [status(thm), theory('equality')], [c_311, c_420])).
% 3.68/1.55  tff(c_603, plain, (![D_413, B_417, A_418, E_414]: ('#skF_3'(D_413, B_417, '#skF_11', A_418, E_414, '#skF_13')='#skF_13' | E_414!='#skF_14' | k10_mcart_1(A_418, B_417, '#skF_11', D_413, E_414)='#skF_13' | ~m1_subset_1(E_414, k4_zfmisc_1(A_418, B_417, '#skF_11', D_413)) | k1_xboole_0=D_413 | k1_xboole_0='#skF_11' | k1_xboole_0=B_417 | k1_xboole_0=A_418)), inference(resolution, [status(thm)], [c_314, c_601])).
% 3.68/1.55  tff(c_624, plain, (![D_423, B_424, A_425, E_426]: ('#skF_3'(D_423, B_424, '#skF_11', A_425, E_426, '#skF_13')='#skF_13' | E_426!='#skF_14' | k10_mcart_1(A_425, B_424, '#skF_11', D_423, E_426)='#skF_13' | ~m1_subset_1(E_426, k4_zfmisc_1(A_425, B_424, '#skF_11', D_423)) | k1_xboole_0=D_423 | k1_xboole_0=B_424 | k1_xboole_0=A_425)), inference(negUnitSimplification, [status(thm)], [c_30, c_603])).
% 3.68/1.55  tff(c_643, plain, ('#skF_3'('#skF_12', '#skF_10', '#skF_11', '#skF_9', '#skF_14', '#skF_13')='#skF_13' | k10_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_38, c_624])).
% 3.68/1.55  tff(c_650, plain, ('#skF_3'('#skF_12', '#skF_10', '#skF_11', '#skF_9', '#skF_14', '#skF_13')='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_28, c_26, c_643])).
% 3.68/1.55  tff(c_4, plain, (![B_2, C_3, E_40, A_1, D_4, F_58]: ('#skF_3'(D_4, B_2, C_3, A_1, E_40, F_58)!=F_58 | k10_mcart_1(A_1, B_2, C_3, D_4, E_40)=F_58 | ~m1_subset_1(F_58, C_3) | ~m1_subset_1(E_40, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.55  tff(c_669, plain, (k10_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | ~m1_subset_1('#skF_13', '#skF_11') | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_650, c_4])).
% 3.68/1.55  tff(c_677, plain, (k10_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_314, c_669])).
% 3.68/1.55  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_677])).
% 3.68/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.55  
% 3.68/1.55  Inference rules
% 3.68/1.55  ----------------------
% 3.68/1.55  #Ref     : 11
% 3.68/1.55  #Sup     : 134
% 3.68/1.55  #Fact    : 0
% 3.68/1.55  #Define  : 0
% 3.68/1.55  #Split   : 0
% 3.68/1.55  #Chain   : 0
% 3.68/1.55  #Close   : 0
% 3.68/1.55  
% 3.68/1.55  Ordering : KBO
% 3.68/1.55  
% 3.68/1.55  Simplification rules
% 3.68/1.55  ----------------------
% 3.68/1.55  #Subsume      : 15
% 3.68/1.55  #Demod        : 17
% 3.68/1.55  #Tautology    : 27
% 3.68/1.55  #SimpNegUnit  : 19
% 3.68/1.55  #BackRed      : 0
% 3.68/1.55  
% 3.68/1.55  #Partial instantiations: 0
% 3.68/1.55  #Strategies tried      : 1
% 3.68/1.55  
% 3.68/1.55  Timing (in seconds)
% 3.68/1.55  ----------------------
% 3.68/1.56  Preprocessing        : 0.34
% 3.68/1.56  Parsing              : 0.17
% 3.68/1.56  CNF conversion       : 0.04
% 3.68/1.56  Main loop            : 0.43
% 3.68/1.56  Inferencing          : 0.17
% 3.68/1.56  Reduction            : 0.09
% 3.68/1.56  Demodulation         : 0.05
% 3.68/1.56  BG Simplification    : 0.03
% 3.68/1.56  Subsumption          : 0.13
% 3.68/1.56  Abstraction          : 0.03
% 3.68/1.56  MUC search           : 0.00
% 3.68/1.56  Cooper               : 0.00
% 3.68/1.56  Total                : 0.81
% 3.68/1.56  Index Insertion      : 0.00
% 3.68/1.56  Index Deletion       : 0.00
% 3.68/1.56  Index Matching       : 0.00
% 3.68/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
