%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:17 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 262 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :   23
%              Number of atoms          :  241 (1610 expanded)
%              Number of equality atoms :  173 ( 994 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_6 > #skF_5 > #skF_10 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_9 > #skF_3 > #skF_12 > #skF_4

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

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

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
                           => E = H ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k9_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( F = k9_mcart_1(A,B,C,D,E)
                  <=> ! [G,H,I,J] :
                        ( E = k4_mcart_1(G,H,I,J)
                       => F = H ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_mcart_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
     => ( A = E
        & B = F
        & C = G
        & D = H ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

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
    k9_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') != '#skF_13' ),
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
    ! [H_164,G_156,I_168,J_170] :
      ( H_164 = '#skF_13'
      | k4_mcart_1(G_156,H_164,I_168,J_170) != '#skF_14'
      | ~ m1_subset_1(J_170,'#skF_12')
      | ~ m1_subset_1(I_168,'#skF_11')
      | ~ m1_subset_1(H_164,'#skF_10')
      | ~ m1_subset_1(G_156,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_125,plain,(
    ! [C_256,B_260,D_258,A_259,E_257] :
      ( '#skF_6'(E_257,A_259,B_260,D_258,C_256) = '#skF_13'
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
      ( '#skF_6'(E_106,A_71,'#skF_10',D_74,C_73) = '#skF_13'
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
      ( '#skF_6'(E_303,A_304,'#skF_10',D_305,C_306) = '#skF_13'
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
      ( '#skF_6'(E_106,'#skF_9','#skF_10',D_74,C_73) = '#skF_13'
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
      ( '#skF_6'(E_323,'#skF_9','#skF_10',D_324,C_325) = '#skF_13'
      | E_323 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(E_323,'#skF_9','#skF_10',D_324,C_325),'#skF_12')
      | ~ m1_subset_1('#skF_7'(E_323,'#skF_9','#skF_10',D_324,C_325),'#skF_11')
      | ~ m1_subset_1(E_323,k4_zfmisc_1('#skF_9','#skF_10',C_325,D_324))
      | k1_xboole_0 = D_324
      | k1_xboole_0 = C_325 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_34,c_166])).

tff(c_183,plain,(
    ! [E_106,C_73] :
      ( '#skF_6'(E_106,'#skF_9','#skF_10','#skF_12',C_73) = '#skF_13'
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
      ( '#skF_6'(E_326,'#skF_9','#skF_10','#skF_12',C_327) = '#skF_13'
      | E_326 != '#skF_14'
      | ~ m1_subset_1('#skF_7'(E_326,'#skF_9','#skF_10','#skF_12',C_327),'#skF_11')
      | ~ m1_subset_1(E_326,k4_zfmisc_1('#skF_9','#skF_10',C_327,'#skF_12'))
      | k1_xboole_0 = C_327 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_28,c_28,c_183])).

tff(c_192,plain,(
    ! [E_106] :
      ( '#skF_6'(E_106,'#skF_9','#skF_10','#skF_12','#skF_11') = '#skF_13'
      | E_106 != '#skF_14'
      | ~ m1_subset_1(E_106,k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
      | k1_xboole_0 = '#skF_12'
      | k1_xboole_0 = '#skF_11'
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_197,plain,(
    ! [E_328] :
      ( '#skF_6'(E_328,'#skF_9','#skF_10','#skF_12','#skF_11') = '#skF_13'
      | E_328 != '#skF_14'
      | ~ m1_subset_1(E_328,k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_30,c_192])).

tff(c_221,plain,(
    '#skF_6'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_38,c_197])).

tff(c_302,plain,
    ( m1_subset_1('#skF_13','#skF_10')
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_14])).

tff(c_313,plain,
    ( m1_subset_1('#skF_13','#skF_10')
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_302])).

tff(c_314,plain,(
    m1_subset_1('#skF_13','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_313])).

tff(c_6,plain,(
    ! [B_2,C_3,E_40,A_1,D_4,F_58] :
      ( k4_mcart_1('#skF_1'(D_4,B_2,C_3,A_1,E_40,F_58),'#skF_2'(D_4,B_2,C_3,A_1,E_40,F_58),'#skF_3'(D_4,B_2,C_3,A_1,E_40,F_58),'#skF_4'(D_4,B_2,C_3,A_1,E_40,F_58)) = E_40
      | k9_mcart_1(A_1,B_2,C_3,D_4,E_40) = F_58
      | ~ m1_subset_1(F_58,B_2)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

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
    ( k4_mcart_1('#skF_5'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_13','#skF_7'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_8'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11')) = '#skF_14'
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_8])).

tff(c_310,plain,
    ( k4_mcart_1('#skF_5'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_13','#skF_7'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_8'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11')) = '#skF_14'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_299])).

tff(c_311,plain,(
    k4_mcart_1('#skF_5'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_13','#skF_7'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11'),'#skF_8'('#skF_14','#skF_9','#skF_10','#skF_12','#skF_11')) = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_310])).

tff(c_22,plain,(
    ! [H_140,A_133,F_138,E_137,D_136,G_139,B_134,C_135] :
      ( F_138 = B_134
      | k4_mcart_1(E_137,F_138,G_139,H_140) != k4_mcart_1(A_133,B_134,C_135,D_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_380,plain,(
    ! [B_341,A_342,C_343,D_344] :
      ( B_341 = '#skF_13'
      | k4_mcart_1(A_342,B_341,C_343,D_344) != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_22])).

tff(c_624,plain,(
    ! [F_428,A_426,B_424,D_423,C_425,E_427] :
      ( '#skF_2'(D_423,B_424,C_425,A_426,E_427,F_428) = '#skF_13'
      | E_427 != '#skF_14'
      | k9_mcart_1(A_426,B_424,C_425,D_423,E_427) = F_428
      | ~ m1_subset_1(F_428,B_424)
      | ~ m1_subset_1(E_427,k4_zfmisc_1(A_426,B_424,C_425,D_423))
      | k1_xboole_0 = D_423
      | k1_xboole_0 = C_425
      | k1_xboole_0 = B_424
      | k1_xboole_0 = A_426 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_380])).

tff(c_626,plain,(
    ! [D_423,C_425,A_426,E_427] :
      ( '#skF_2'(D_423,'#skF_10',C_425,A_426,E_427,'#skF_13') = '#skF_13'
      | E_427 != '#skF_14'
      | k9_mcart_1(A_426,'#skF_10',C_425,D_423,E_427) = '#skF_13'
      | ~ m1_subset_1(E_427,k4_zfmisc_1(A_426,'#skF_10',C_425,D_423))
      | k1_xboole_0 = D_423
      | k1_xboole_0 = C_425
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = A_426 ) ),
    inference(resolution,[status(thm)],[c_314,c_624])).

tff(c_646,plain,(
    ! [D_429,C_430,A_431,E_432] :
      ( '#skF_2'(D_429,'#skF_10',C_430,A_431,E_432,'#skF_13') = '#skF_13'
      | E_432 != '#skF_14'
      | k9_mcart_1(A_431,'#skF_10',C_430,D_429,E_432) = '#skF_13'
      | ~ m1_subset_1(E_432,k4_zfmisc_1(A_431,'#skF_10',C_430,D_429))
      | k1_xboole_0 = D_429
      | k1_xboole_0 = C_430
      | k1_xboole_0 = A_431 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_626])).

tff(c_665,plain,
    ( '#skF_2'('#skF_12','#skF_10','#skF_11','#skF_9','#skF_14','#skF_13') = '#skF_13'
    | k9_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_646])).

tff(c_672,plain,(
    '#skF_2'('#skF_12','#skF_10','#skF_11','#skF_9','#skF_14','#skF_13') = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_30,c_28,c_26,c_665])).

tff(c_4,plain,(
    ! [B_2,C_3,E_40,A_1,D_4,F_58] :
      ( '#skF_2'(D_4,B_2,C_3,A_1,E_40,F_58) != F_58
      | k9_mcart_1(A_1,B_2,C_3,D_4,E_40) = F_58
      | ~ m1_subset_1(F_58,B_2)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_678,plain,
    ( k9_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | ~ m1_subset_1('#skF_13','#skF_10')
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_4])).

tff(c_686,plain,
    ( k9_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_314,c_678])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_26,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:40:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.60  
% 3.61/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.60  %$ m1_subset_1 > k9_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_6 > #skF_5 > #skF_10 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_9 > #skF_3 > #skF_12 > #skF_4
% 3.61/1.60  
% 3.61/1.60  %Foreground sorts:
% 3.61/1.60  
% 3.61/1.60  
% 3.61/1.60  %Background operators:
% 3.61/1.60  
% 3.61/1.60  
% 3.61/1.60  %Foreground operators:
% 3.61/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_11', type, '#skF_11': $i).
% 3.61/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.60  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_10', type, '#skF_10': $i).
% 3.61/1.60  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_14', type, '#skF_14': $i).
% 3.61/1.60  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_13', type, '#skF_13': $i).
% 3.61/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.61/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.60  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.61/1.60  tff('#skF_12', type, '#skF_12': $i).
% 3.61/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.60  
% 3.61/1.61  tff(f_122, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_mcart_1)).
% 3.61/1.61  tff(f_83, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.61/1.61  tff(f_52, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, B) => ((F = k9_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = H)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_mcart_1)).
% 3.61/1.61  tff(f_93, axiom, (![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.61/1.61  tff(c_34, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_32, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_30, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_28, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_26, plain, (k9_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_38, plain, (m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_12, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_7'(E_106, A_71, B_72, D_74, C_73), C_73) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.61  tff(c_10, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_8'(E_106, A_71, B_72, D_74, C_73), D_74) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.61  tff(c_16, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_5'(E_106, A_71, B_72, D_74, C_73), A_71) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.61  tff(c_14, plain, (![D_74, C_73, B_72, E_106, A_71]: (m1_subset_1('#skF_6'(E_106, A_71, B_72, D_74, C_73), B_72) | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.61  tff(c_73, plain, (![C_237, A_234, E_233, D_236, B_235]: (k4_mcart_1('#skF_5'(E_233, A_234, B_235, D_236, C_237), '#skF_6'(E_233, A_234, B_235, D_236, C_237), '#skF_7'(E_233, A_234, B_235, D_236, C_237), '#skF_8'(E_233, A_234, B_235, D_236, C_237))=E_233 | ~m1_subset_1(E_233, k4_zfmisc_1(A_234, B_235, C_237, D_236)) | k1_xboole_0=D_236 | k1_xboole_0=C_237 | k1_xboole_0=B_235 | k1_xboole_0=A_234)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.61  tff(c_36, plain, (![H_164, G_156, I_168, J_170]: (H_164='#skF_13' | k4_mcart_1(G_156, H_164, I_168, J_170)!='#skF_14' | ~m1_subset_1(J_170, '#skF_12') | ~m1_subset_1(I_168, '#skF_11') | ~m1_subset_1(H_164, '#skF_10') | ~m1_subset_1(G_156, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.61  tff(c_125, plain, (![C_256, B_260, D_258, A_259, E_257]: ('#skF_6'(E_257, A_259, B_260, D_258, C_256)='#skF_13' | E_257!='#skF_14' | ~m1_subset_1('#skF_8'(E_257, A_259, B_260, D_258, C_256), '#skF_12') | ~m1_subset_1('#skF_7'(E_257, A_259, B_260, D_258, C_256), '#skF_11') | ~m1_subset_1('#skF_6'(E_257, A_259, B_260, D_258, C_256), '#skF_10') | ~m1_subset_1('#skF_5'(E_257, A_259, B_260, D_258, C_256), '#skF_9') | ~m1_subset_1(E_257, k4_zfmisc_1(A_259, B_260, C_256, D_258)) | k1_xboole_0=D_258 | k1_xboole_0=C_256 | k1_xboole_0=B_260 | k1_xboole_0=A_259)), inference(superposition, [status(thm), theory('equality')], [c_73, c_36])).
% 3.61/1.61  tff(c_129, plain, (![E_106, A_71, D_74, C_73]: ('#skF_6'(E_106, A_71, '#skF_10', D_74, C_73)='#skF_13' | E_106!='#skF_14' | ~m1_subset_1('#skF_8'(E_106, A_71, '#skF_10', D_74, C_73), '#skF_12') | ~m1_subset_1('#skF_7'(E_106, A_71, '#skF_10', D_74, C_73), '#skF_11') | ~m1_subset_1('#skF_5'(E_106, A_71, '#skF_10', D_74, C_73), '#skF_9') | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, '#skF_10', C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0='#skF_10' | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_14, c_125])).
% 3.61/1.61  tff(c_162, plain, (![E_303, A_304, D_305, C_306]: ('#skF_6'(E_303, A_304, '#skF_10', D_305, C_306)='#skF_13' | E_303!='#skF_14' | ~m1_subset_1('#skF_8'(E_303, A_304, '#skF_10', D_305, C_306), '#skF_12') | ~m1_subset_1('#skF_7'(E_303, A_304, '#skF_10', D_305, C_306), '#skF_11') | ~m1_subset_1('#skF_5'(E_303, A_304, '#skF_10', D_305, C_306), '#skF_9') | ~m1_subset_1(E_303, k4_zfmisc_1(A_304, '#skF_10', C_306, D_305)) | k1_xboole_0=D_305 | k1_xboole_0=C_306 | k1_xboole_0=A_304)), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_129])).
% 3.61/1.61  tff(c_166, plain, (![E_106, D_74, C_73]: ('#skF_6'(E_106, '#skF_9', '#skF_10', D_74, C_73)='#skF_13' | E_106!='#skF_14' | ~m1_subset_1('#skF_8'(E_106, '#skF_9', '#skF_10', D_74, C_73), '#skF_12') | ~m1_subset_1('#skF_7'(E_106, '#skF_9', '#skF_10', D_74, C_73), '#skF_11') | ~m1_subset_1(E_106, k4_zfmisc_1('#skF_9', '#skF_10', C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_16, c_162])).
% 3.61/1.61  tff(c_179, plain, (![E_323, D_324, C_325]: ('#skF_6'(E_323, '#skF_9', '#skF_10', D_324, C_325)='#skF_13' | E_323!='#skF_14' | ~m1_subset_1('#skF_8'(E_323, '#skF_9', '#skF_10', D_324, C_325), '#skF_12') | ~m1_subset_1('#skF_7'(E_323, '#skF_9', '#skF_10', D_324, C_325), '#skF_11') | ~m1_subset_1(E_323, k4_zfmisc_1('#skF_9', '#skF_10', C_325, D_324)) | k1_xboole_0=D_324 | k1_xboole_0=C_325)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_34, c_166])).
% 3.61/1.61  tff(c_183, plain, (![E_106, C_73]: ('#skF_6'(E_106, '#skF_9', '#skF_10', '#skF_12', C_73)='#skF_13' | E_106!='#skF_14' | ~m1_subset_1('#skF_7'(E_106, '#skF_9', '#skF_10', '#skF_12', C_73), '#skF_11') | ~m1_subset_1(E_106, k4_zfmisc_1('#skF_9', '#skF_10', C_73, '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0=C_73 | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_10, c_179])).
% 3.61/1.61  tff(c_188, plain, (![E_326, C_327]: ('#skF_6'(E_326, '#skF_9', '#skF_10', '#skF_12', C_327)='#skF_13' | E_326!='#skF_14' | ~m1_subset_1('#skF_7'(E_326, '#skF_9', '#skF_10', '#skF_12', C_327), '#skF_11') | ~m1_subset_1(E_326, k4_zfmisc_1('#skF_9', '#skF_10', C_327, '#skF_12')) | k1_xboole_0=C_327)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_28, c_28, c_183])).
% 3.61/1.61  tff(c_192, plain, (![E_106]: ('#skF_6'(E_106, '#skF_9', '#skF_10', '#skF_12', '#skF_11')='#skF_13' | E_106!='#skF_14' | ~m1_subset_1(E_106, k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_12, c_188])).
% 3.61/1.61  tff(c_197, plain, (![E_328]: ('#skF_6'(E_328, '#skF_9', '#skF_10', '#skF_12', '#skF_11')='#skF_13' | E_328!='#skF_14' | ~m1_subset_1(E_328, k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_30, c_192])).
% 3.61/1.61  tff(c_221, plain, ('#skF_6'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11')='#skF_13'), inference(resolution, [status(thm)], [c_38, c_197])).
% 3.61/1.61  tff(c_302, plain, (m1_subset_1('#skF_13', '#skF_10') | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_221, c_14])).
% 3.61/1.61  tff(c_313, plain, (m1_subset_1('#skF_13', '#skF_10') | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_302])).
% 3.61/1.61  tff(c_314, plain, (m1_subset_1('#skF_13', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_313])).
% 3.61/1.61  tff(c_6, plain, (![B_2, C_3, E_40, A_1, D_4, F_58]: (k4_mcart_1('#skF_1'(D_4, B_2, C_3, A_1, E_40, F_58), '#skF_2'(D_4, B_2, C_3, A_1, E_40, F_58), '#skF_3'(D_4, B_2, C_3, A_1, E_40, F_58), '#skF_4'(D_4, B_2, C_3, A_1, E_40, F_58))=E_40 | k9_mcart_1(A_1, B_2, C_3, D_4, E_40)=F_58 | ~m1_subset_1(F_58, B_2) | ~m1_subset_1(E_40, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.61  tff(c_8, plain, (![D_74, C_73, B_72, E_106, A_71]: (k4_mcart_1('#skF_5'(E_106, A_71, B_72, D_74, C_73), '#skF_6'(E_106, A_71, B_72, D_74, C_73), '#skF_7'(E_106, A_71, B_72, D_74, C_73), '#skF_8'(E_106, A_71, B_72, D_74, C_73))=E_106 | ~m1_subset_1(E_106, k4_zfmisc_1(A_71, B_72, C_73, D_74)) | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.61  tff(c_299, plain, (k4_mcart_1('#skF_5'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_13', '#skF_7'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_8'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'))='#skF_14' | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_221, c_8])).
% 3.61/1.61  tff(c_310, plain, (k4_mcart_1('#skF_5'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_13', '#skF_7'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_8'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'))='#skF_14' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_299])).
% 3.61/1.61  tff(c_311, plain, (k4_mcart_1('#skF_5'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_13', '#skF_7'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'), '#skF_8'('#skF_14', '#skF_9', '#skF_10', '#skF_12', '#skF_11'))='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_310])).
% 3.61/1.61  tff(c_22, plain, (![H_140, A_133, F_138, E_137, D_136, G_139, B_134, C_135]: (F_138=B_134 | k4_mcart_1(E_137, F_138, G_139, H_140)!=k4_mcart_1(A_133, B_134, C_135, D_136))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.61/1.61  tff(c_380, plain, (![B_341, A_342, C_343, D_344]: (B_341='#skF_13' | k4_mcart_1(A_342, B_341, C_343, D_344)!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_311, c_22])).
% 3.61/1.61  tff(c_624, plain, (![F_428, A_426, B_424, D_423, C_425, E_427]: ('#skF_2'(D_423, B_424, C_425, A_426, E_427, F_428)='#skF_13' | E_427!='#skF_14' | k9_mcart_1(A_426, B_424, C_425, D_423, E_427)=F_428 | ~m1_subset_1(F_428, B_424) | ~m1_subset_1(E_427, k4_zfmisc_1(A_426, B_424, C_425, D_423)) | k1_xboole_0=D_423 | k1_xboole_0=C_425 | k1_xboole_0=B_424 | k1_xboole_0=A_426)), inference(superposition, [status(thm), theory('equality')], [c_6, c_380])).
% 3.61/1.61  tff(c_626, plain, (![D_423, C_425, A_426, E_427]: ('#skF_2'(D_423, '#skF_10', C_425, A_426, E_427, '#skF_13')='#skF_13' | E_427!='#skF_14' | k9_mcart_1(A_426, '#skF_10', C_425, D_423, E_427)='#skF_13' | ~m1_subset_1(E_427, k4_zfmisc_1(A_426, '#skF_10', C_425, D_423)) | k1_xboole_0=D_423 | k1_xboole_0=C_425 | k1_xboole_0='#skF_10' | k1_xboole_0=A_426)), inference(resolution, [status(thm)], [c_314, c_624])).
% 3.61/1.61  tff(c_646, plain, (![D_429, C_430, A_431, E_432]: ('#skF_2'(D_429, '#skF_10', C_430, A_431, E_432, '#skF_13')='#skF_13' | E_432!='#skF_14' | k9_mcart_1(A_431, '#skF_10', C_430, D_429, E_432)='#skF_13' | ~m1_subset_1(E_432, k4_zfmisc_1(A_431, '#skF_10', C_430, D_429)) | k1_xboole_0=D_429 | k1_xboole_0=C_430 | k1_xboole_0=A_431)), inference(negUnitSimplification, [status(thm)], [c_32, c_626])).
% 3.61/1.61  tff(c_665, plain, ('#skF_2'('#skF_12', '#skF_10', '#skF_11', '#skF_9', '#skF_14', '#skF_13')='#skF_13' | k9_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_38, c_646])).
% 3.61/1.61  tff(c_672, plain, ('#skF_2'('#skF_12', '#skF_10', '#skF_11', '#skF_9', '#skF_14', '#skF_13')='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_34, c_30, c_28, c_26, c_665])).
% 3.61/1.61  tff(c_4, plain, (![B_2, C_3, E_40, A_1, D_4, F_58]: ('#skF_2'(D_4, B_2, C_3, A_1, E_40, F_58)!=F_58 | k9_mcart_1(A_1, B_2, C_3, D_4, E_40)=F_58 | ~m1_subset_1(F_58, B_2) | ~m1_subset_1(E_40, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.61  tff(c_678, plain, (k9_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | ~m1_subset_1('#skF_13', '#skF_10') | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_672, c_4])).
% 3.61/1.61  tff(c_686, plain, (k9_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_314, c_678])).
% 3.61/1.61  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_686])).
% 3.61/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.61  
% 3.61/1.61  Inference rules
% 3.61/1.61  ----------------------
% 3.61/1.61  #Ref     : 10
% 3.61/1.61  #Sup     : 137
% 3.61/1.61  #Fact    : 0
% 3.61/1.61  #Define  : 0
% 3.61/1.61  #Split   : 0
% 3.61/1.61  #Chain   : 0
% 3.61/1.61  #Close   : 0
% 3.61/1.61  
% 3.61/1.61  Ordering : KBO
% 3.61/1.61  
% 3.61/1.61  Simplification rules
% 3.61/1.61  ----------------------
% 3.61/1.61  #Subsume      : 16
% 3.61/1.61  #Demod        : 17
% 3.61/1.61  #Tautology    : 27
% 3.61/1.61  #SimpNegUnit  : 20
% 3.61/1.61  #BackRed      : 0
% 3.61/1.61  
% 3.61/1.61  #Partial instantiations: 0
% 3.61/1.61  #Strategies tried      : 1
% 3.61/1.61  
% 3.61/1.61  Timing (in seconds)
% 3.61/1.61  ----------------------
% 3.72/1.62  Preprocessing        : 0.36
% 3.72/1.62  Parsing              : 0.17
% 3.72/1.62  CNF conversion       : 0.04
% 3.72/1.62  Main loop            : 0.43
% 3.72/1.62  Inferencing          : 0.16
% 3.72/1.62  Reduction            : 0.09
% 3.72/1.62  Demodulation         : 0.05
% 3.72/1.62  BG Simplification    : 0.04
% 3.72/1.62  Subsumption          : 0.13
% 3.72/1.62  Abstraction          : 0.03
% 3.72/1.62  MUC search           : 0.00
% 3.72/1.62  Cooper               : 0.00
% 3.72/1.62  Total                : 0.82
% 3.72/1.62  Index Insertion      : 0.00
% 3.72/1.62  Index Deletion       : 0.00
% 3.72/1.62  Index Matching       : 0.00
% 3.72/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
