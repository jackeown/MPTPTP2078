%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 494 expanded)
%              Number of leaves         :   31 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (3310 expanded)
%              Number of equality atoms :  192 (2141 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
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
                           => E = J ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k11_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ? [F,G,H,I] :
              ( E = k4_mcart_1(F,G,H,I)
              & ~ ( k8_mcart_1(A,B,C,D,E) = F
                  & k9_mcart_1(A,B,C,D,E) = G
                  & k10_mcart_1(A,B,C,D,E) = H
                  & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_149,plain,(
    ! [A_124,C_126,B_122,E_123,D_125] :
      ( k11_mcart_1(A_124,B_122,C_126,D_125,E_123) = k2_mcart_1(E_123)
      | ~ m1_subset_1(E_123,k4_zfmisc_1(A_124,B_122,C_126,D_125))
      | k1_xboole_0 = D_125
      | k1_xboole_0 = C_126
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_152,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_149])).

tff(c_155,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_152])).

tff(c_36,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_156,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_36])).

tff(c_28,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1('#skF_4'(D_34,B_32,E_35,A_31,F_36,C_33),D_34)
      | k10_mcart_1(A_31,B_32,C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(F_36,k4_zfmisc_1(A_31,B_32,C_33,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1('#skF_3'(D_34,B_32,E_35,A_31,F_36,C_33),C_33)
      | k10_mcart_1(A_31,B_32,C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(F_36,k4_zfmisc_1(A_31,B_32,C_33,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1('#skF_1'(D_34,B_32,E_35,A_31,F_36,C_33),A_31)
      | k10_mcart_1(A_31,B_32,C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(F_36,k4_zfmisc_1(A_31,B_32,C_33,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1('#skF_2'(D_34,B_32,E_35,A_31,F_36,C_33),B_32)
      | k10_mcart_1(A_31,B_32,C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(F_36,k4_zfmisc_1(A_31,B_32,C_33,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_371,plain,(
    ! [C_244,B_240,E_241,D_239,F_243,A_242] :
      ( k4_mcart_1('#skF_1'(D_239,B_240,E_241,A_242,F_243,C_244),'#skF_2'(D_239,B_240,E_241,A_242,F_243,C_244),'#skF_3'(D_239,B_240,E_241,A_242,F_243,C_244),'#skF_4'(D_239,B_240,E_241,A_242,F_243,C_244)) = F_243
      | k10_mcart_1(A_242,B_240,C_244,D_239,F_243) = E_241
      | k1_xboole_0 = D_239
      | k1_xboole_0 = C_244
      | k1_xboole_0 = B_240
      | k1_xboole_0 = A_242
      | ~ m1_subset_1(F_243,k4_zfmisc_1(A_242,B_240,C_244,D_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [J_92,G_78,H_86,I_90] :
      ( J_92 = '#skF_9'
      | k4_mcart_1(G_78,H_86,I_90,J_92) != '#skF_10'
      | ~ m1_subset_1(J_92,'#skF_8')
      | ~ m1_subset_1(I_90,'#skF_7')
      | ~ m1_subset_1(H_86,'#skF_6')
      | ~ m1_subset_1(G_78,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_441,plain,(
    ! [B_278,E_274,C_275,A_277,F_279,D_276] :
      ( '#skF_4'(D_276,B_278,E_274,A_277,F_279,C_275) = '#skF_9'
      | F_279 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_276,B_278,E_274,A_277,F_279,C_275),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_276,B_278,E_274,A_277,F_279,C_275),'#skF_7')
      | ~ m1_subset_1('#skF_2'(D_276,B_278,E_274,A_277,F_279,C_275),'#skF_6')
      | ~ m1_subset_1('#skF_1'(D_276,B_278,E_274,A_277,F_279,C_275),'#skF_5')
      | k10_mcart_1(A_277,B_278,C_275,D_276,F_279) = E_274
      | k1_xboole_0 = D_276
      | k1_xboole_0 = C_275
      | k1_xboole_0 = B_278
      | k1_xboole_0 = A_277
      | ~ m1_subset_1(F_279,k4_zfmisc_1(A_277,B_278,C_275,D_276)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_46])).

tff(c_445,plain,(
    ! [A_31,C_33,F_36,E_35,D_34] :
      ( '#skF_4'(D_34,'#skF_6',E_35,A_31,F_36,C_33) = '#skF_9'
      | F_36 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_34,'#skF_6',E_35,A_31,F_36,C_33),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_34,'#skF_6',E_35,A_31,F_36,C_33),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_34,'#skF_6',E_35,A_31,F_36,C_33),'#skF_5')
      | k10_mcart_1(A_31,'#skF_6',C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(F_36,k4_zfmisc_1(A_31,'#skF_6',C_33,D_34)) ) ),
    inference(resolution,[status(thm)],[c_32,c_441])).

tff(c_503,plain,(
    ! [C_322,E_319,A_320,F_321,D_318] :
      ( '#skF_4'(D_318,'#skF_6',E_319,A_320,F_321,C_322) = '#skF_9'
      | F_321 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_318,'#skF_6',E_319,A_320,F_321,C_322),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_318,'#skF_6',E_319,A_320,F_321,C_322),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_318,'#skF_6',E_319,A_320,F_321,C_322),'#skF_5')
      | k10_mcart_1(A_320,'#skF_6',C_322,D_318,F_321) = E_319
      | k1_xboole_0 = D_318
      | k1_xboole_0 = C_322
      | k1_xboole_0 = A_320
      | ~ m1_subset_1(F_321,k4_zfmisc_1(A_320,'#skF_6',C_322,D_318)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_445])).

tff(c_507,plain,(
    ! [D_34,E_35,F_36,C_33] :
      ( '#skF_4'(D_34,'#skF_6',E_35,'#skF_5',F_36,C_33) = '#skF_9'
      | F_36 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_34,'#skF_6',E_35,'#skF_5',F_36,C_33),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_34,'#skF_6',E_35,'#skF_5',F_36,C_33),'#skF_7')
      | k10_mcart_1('#skF_5','#skF_6',C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_36,k4_zfmisc_1('#skF_5','#skF_6',C_33,D_34)) ) ),
    inference(resolution,[status(thm)],[c_34,c_503])).

tff(c_512,plain,(
    ! [D_323,E_324,F_325,C_326] :
      ( '#skF_4'(D_323,'#skF_6',E_324,'#skF_5',F_325,C_326) = '#skF_9'
      | F_325 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_323,'#skF_6',E_324,'#skF_5',F_325,C_326),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_323,'#skF_6',E_324,'#skF_5',F_325,C_326),'#skF_7')
      | k10_mcart_1('#skF_5','#skF_6',C_326,D_323,F_325) = E_324
      | k1_xboole_0 = D_323
      | k1_xboole_0 = C_326
      | ~ m1_subset_1(F_325,k4_zfmisc_1('#skF_5','#skF_6',C_326,D_323)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_44,c_507])).

tff(c_516,plain,(
    ! [D_34,E_35,F_36] :
      ( '#skF_4'(D_34,'#skF_6',E_35,'#skF_5',F_36,'#skF_7') = '#skF_9'
      | F_36 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_34,'#skF_6',E_35,'#skF_5',F_36,'#skF_7'),'#skF_8')
      | k10_mcart_1('#skF_5','#skF_6','#skF_7',D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_36,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_34)) ) ),
    inference(resolution,[status(thm)],[c_30,c_512])).

tff(c_521,plain,(
    ! [D_327,E_328,F_329] :
      ( '#skF_4'(D_327,'#skF_6',E_328,'#skF_5',F_329,'#skF_7') = '#skF_9'
      | F_329 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_327,'#skF_6',E_328,'#skF_5',F_329,'#skF_7'),'#skF_8')
      | k10_mcart_1('#skF_5','#skF_6','#skF_7',D_327,F_329) = E_328
      | k1_xboole_0 = D_327
      | ~ m1_subset_1(F_329,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_327)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_40,c_516])).

tff(c_525,plain,(
    ! [E_35,F_36] :
      ( '#skF_4'('#skF_8','#skF_6',E_35,'#skF_5',F_36,'#skF_7') = '#skF_9'
      | F_36 != '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_36) = E_35
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_36,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_28,c_521])).

tff(c_530,plain,(
    ! [E_330,F_331] :
      ( '#skF_4'('#skF_8','#skF_6',E_330,'#skF_5',F_331,'#skF_7') = '#skF_9'
      | F_331 != '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_331) = E_330
      | ~ m1_subset_1(F_331,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_38,c_525])).

tff(c_552,plain,(
    ! [E_332] :
      ( '#skF_4'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7') = '#skF_9'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ) ),
    inference(resolution,[status(thm)],[c_48,c_530])).

tff(c_26,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( k4_mcart_1('#skF_1'(D_34,B_32,E_35,A_31,F_36,C_33),'#skF_2'(D_34,B_32,E_35,A_31,F_36,C_33),'#skF_3'(D_34,B_32,E_35,A_31,F_36,C_33),'#skF_4'(D_34,B_32,E_35,A_31,F_36,C_33)) = F_36
      | k10_mcart_1(A_31,B_32,C_33,D_34,F_36) = E_35
      | k1_xboole_0 = D_34
      | k1_xboole_0 = C_33
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(F_36,k4_zfmisc_1(A_31,B_32,C_33,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_561,plain,(
    ! [E_332] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_2'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_3'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_9') = '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_26])).

tff(c_1061,plain,(
    ! [E_332] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_2'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_3'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_9') = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_561])).

tff(c_1062,plain,(
    ! [E_332] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_2'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_3'('#skF_8','#skF_6',E_332,'#skF_5','#skF_10','#skF_7'),'#skF_9') = '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_1061])).

tff(c_1135,plain,(
    ! [E_3809] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_6',E_3809,'#skF_5','#skF_10','#skF_7'),'#skF_2'('#skF_8','#skF_6',E_3809,'#skF_5','#skF_10','#skF_7'),'#skF_3'('#skF_8','#skF_6',E_3809,'#skF_5','#skF_10','#skF_7'),'#skF_9') = '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3809 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_1061])).

tff(c_16,plain,(
    ! [G_28,F_27,D_21,A_18,H_29,C_20,B_19,I_30] :
      ( k11_mcart_1(A_18,B_19,C_20,D_21,k4_mcart_1(F_27,G_28,H_29,I_30)) = I_30
      | k1_xboole_0 = D_21
      | k1_xboole_0 = C_20
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k4_mcart_1(F_27,G_28,H_29,I_30),k4_zfmisc_1(A_18,B_19,C_20,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1525,plain,(
    ! [C_4607,A_4606,D_4608,B_4609,E_4605] :
      ( k11_mcart_1(A_4606,B_4609,C_4607,D_4608,k4_mcart_1('#skF_1'('#skF_8','#skF_6',E_4605,'#skF_5','#skF_10','#skF_7'),'#skF_2'('#skF_8','#skF_6',E_4605,'#skF_5','#skF_10','#skF_7'),'#skF_3'('#skF_8','#skF_6',E_4605,'#skF_5','#skF_10','#skF_7'),'#skF_9')) = '#skF_9'
      | k1_xboole_0 = D_4608
      | k1_xboole_0 = C_4607
      | k1_xboole_0 = B_4609
      | k1_xboole_0 = A_4606
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_4606,B_4609,C_4607,D_4608))
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_4605 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1135,c_16])).

tff(c_1534,plain,(
    ! [C_4607,A_4606,D_4608,B_4609,E_332] :
      ( k11_mcart_1(A_4606,B_4609,C_4607,D_4608,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_4608
      | k1_xboole_0 = C_4607
      | k1_xboole_0 = B_4609
      | k1_xboole_0 = A_4606
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_4606,B_4609,C_4607,D_4608))
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_1525])).

tff(c_1562,plain,(
    ! [E_332] :
      ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ) ),
    inference(splitLeft,[status(thm)],[c_1534])).

tff(c_3208,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_6' ),
    inference(factorization,[status(thm),theory(equality)],[c_1562])).

tff(c_1583,plain,(
    ! [E_332] : k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_332 ),
    inference(factorization,[status(thm),theory(equality)],[c_1562])).

tff(c_4349,plain,(
    ! [E_21707] : E_21707 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3208,c_1583])).

tff(c_4765,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4349,c_42])).

tff(c_4767,plain,(
    ! [A_25996,B_25997,C_25998,D_25999] :
      ( k11_mcart_1(A_25996,B_25997,C_25998,D_25999,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_25999
      | k1_xboole_0 = C_25998
      | k1_xboole_0 = B_25997
      | k1_xboole_0 = A_25996
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_25996,B_25997,C_25998,D_25999)) ) ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_4771,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_4767])).

tff(c_4773,plain,
    ( k2_mcart_1('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_4771])).

tff(c_4775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_156,c_4773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.05  
% 5.39/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.05  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 5.39/2.05  
% 5.39/2.05  %Foreground sorts:
% 5.39/2.05  
% 5.39/2.05  
% 5.39/2.05  %Background operators:
% 5.39/2.05  
% 5.39/2.05  
% 5.39/2.05  %Foreground operators:
% 5.39/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.39/2.05  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.39/2.05  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.39/2.05  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.39/2.05  tff('#skF_7', type, '#skF_7': $i).
% 5.39/2.05  tff('#skF_10', type, '#skF_10': $i).
% 5.39/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.39/2.05  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff('#skF_6', type, '#skF_6': $i).
% 5.39/2.05  tff('#skF_9', type, '#skF_9': $i).
% 5.39/2.05  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.39/2.05  tff('#skF_8', type, '#skF_8': $i).
% 5.39/2.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/2.05  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.39/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.39/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/2.05  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.39/2.05  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.39/2.05  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 5.39/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.39/2.05  
% 5.39/2.07  tff(f_140, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_mcart_1)).
% 5.39/2.07  tff(f_56, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 5.39/2.07  tff(f_111, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 5.39/2.07  tff(f_83, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 5.39/2.07  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_40, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_38, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_48, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_149, plain, (![A_124, C_126, B_122, E_123, D_125]: (k11_mcart_1(A_124, B_122, C_126, D_125, E_123)=k2_mcart_1(E_123) | ~m1_subset_1(E_123, k4_zfmisc_1(A_124, B_122, C_126, D_125)) | k1_xboole_0=D_125 | k1_xboole_0=C_126 | k1_xboole_0=B_122 | k1_xboole_0=A_124)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.39/2.07  tff(c_152, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_149])).
% 5.39/2.07  tff(c_155, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_152])).
% 5.39/2.07  tff(c_36, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_156, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_36])).
% 5.39/2.07  tff(c_28, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1('#skF_4'(D_34, B_32, E_35, A_31, F_36, C_33), D_34) | k10_mcart_1(A_31, B_32, C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31 | ~m1_subset_1(F_36, k4_zfmisc_1(A_31, B_32, C_33, D_34)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.39/2.07  tff(c_30, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1('#skF_3'(D_34, B_32, E_35, A_31, F_36, C_33), C_33) | k10_mcart_1(A_31, B_32, C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31 | ~m1_subset_1(F_36, k4_zfmisc_1(A_31, B_32, C_33, D_34)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.39/2.07  tff(c_34, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1('#skF_1'(D_34, B_32, E_35, A_31, F_36, C_33), A_31) | k10_mcart_1(A_31, B_32, C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31 | ~m1_subset_1(F_36, k4_zfmisc_1(A_31, B_32, C_33, D_34)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.39/2.07  tff(c_32, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1('#skF_2'(D_34, B_32, E_35, A_31, F_36, C_33), B_32) | k10_mcart_1(A_31, B_32, C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31 | ~m1_subset_1(F_36, k4_zfmisc_1(A_31, B_32, C_33, D_34)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.39/2.07  tff(c_371, plain, (![C_244, B_240, E_241, D_239, F_243, A_242]: (k4_mcart_1('#skF_1'(D_239, B_240, E_241, A_242, F_243, C_244), '#skF_2'(D_239, B_240, E_241, A_242, F_243, C_244), '#skF_3'(D_239, B_240, E_241, A_242, F_243, C_244), '#skF_4'(D_239, B_240, E_241, A_242, F_243, C_244))=F_243 | k10_mcart_1(A_242, B_240, C_244, D_239, F_243)=E_241 | k1_xboole_0=D_239 | k1_xboole_0=C_244 | k1_xboole_0=B_240 | k1_xboole_0=A_242 | ~m1_subset_1(F_243, k4_zfmisc_1(A_242, B_240, C_244, D_239)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.39/2.07  tff(c_46, plain, (![J_92, G_78, H_86, I_90]: (J_92='#skF_9' | k4_mcart_1(G_78, H_86, I_90, J_92)!='#skF_10' | ~m1_subset_1(J_92, '#skF_8') | ~m1_subset_1(I_90, '#skF_7') | ~m1_subset_1(H_86, '#skF_6') | ~m1_subset_1(G_78, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.39/2.07  tff(c_441, plain, (![B_278, E_274, C_275, A_277, F_279, D_276]: ('#skF_4'(D_276, B_278, E_274, A_277, F_279, C_275)='#skF_9' | F_279!='#skF_10' | ~m1_subset_1('#skF_4'(D_276, B_278, E_274, A_277, F_279, C_275), '#skF_8') | ~m1_subset_1('#skF_3'(D_276, B_278, E_274, A_277, F_279, C_275), '#skF_7') | ~m1_subset_1('#skF_2'(D_276, B_278, E_274, A_277, F_279, C_275), '#skF_6') | ~m1_subset_1('#skF_1'(D_276, B_278, E_274, A_277, F_279, C_275), '#skF_5') | k10_mcart_1(A_277, B_278, C_275, D_276, F_279)=E_274 | k1_xboole_0=D_276 | k1_xboole_0=C_275 | k1_xboole_0=B_278 | k1_xboole_0=A_277 | ~m1_subset_1(F_279, k4_zfmisc_1(A_277, B_278, C_275, D_276)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_46])).
% 5.39/2.07  tff(c_445, plain, (![A_31, C_33, F_36, E_35, D_34]: ('#skF_4'(D_34, '#skF_6', E_35, A_31, F_36, C_33)='#skF_9' | F_36!='#skF_10' | ~m1_subset_1('#skF_4'(D_34, '#skF_6', E_35, A_31, F_36, C_33), '#skF_8') | ~m1_subset_1('#skF_3'(D_34, '#skF_6', E_35, A_31, F_36, C_33), '#skF_7') | ~m1_subset_1('#skF_1'(D_34, '#skF_6', E_35, A_31, F_36, C_33), '#skF_5') | k10_mcart_1(A_31, '#skF_6', C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0='#skF_6' | k1_xboole_0=A_31 | ~m1_subset_1(F_36, k4_zfmisc_1(A_31, '#skF_6', C_33, D_34)))), inference(resolution, [status(thm)], [c_32, c_441])).
% 5.39/2.07  tff(c_503, plain, (![C_322, E_319, A_320, F_321, D_318]: ('#skF_4'(D_318, '#skF_6', E_319, A_320, F_321, C_322)='#skF_9' | F_321!='#skF_10' | ~m1_subset_1('#skF_4'(D_318, '#skF_6', E_319, A_320, F_321, C_322), '#skF_8') | ~m1_subset_1('#skF_3'(D_318, '#skF_6', E_319, A_320, F_321, C_322), '#skF_7') | ~m1_subset_1('#skF_1'(D_318, '#skF_6', E_319, A_320, F_321, C_322), '#skF_5') | k10_mcart_1(A_320, '#skF_6', C_322, D_318, F_321)=E_319 | k1_xboole_0=D_318 | k1_xboole_0=C_322 | k1_xboole_0=A_320 | ~m1_subset_1(F_321, k4_zfmisc_1(A_320, '#skF_6', C_322, D_318)))), inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_445])).
% 5.39/2.07  tff(c_507, plain, (![D_34, E_35, F_36, C_33]: ('#skF_4'(D_34, '#skF_6', E_35, '#skF_5', F_36, C_33)='#skF_9' | F_36!='#skF_10' | ~m1_subset_1('#skF_4'(D_34, '#skF_6', E_35, '#skF_5', F_36, C_33), '#skF_8') | ~m1_subset_1('#skF_3'(D_34, '#skF_6', E_35, '#skF_5', F_36, C_33), '#skF_7') | k10_mcart_1('#skF_5', '#skF_6', C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_36, k4_zfmisc_1('#skF_5', '#skF_6', C_33, D_34)))), inference(resolution, [status(thm)], [c_34, c_503])).
% 5.39/2.07  tff(c_512, plain, (![D_323, E_324, F_325, C_326]: ('#skF_4'(D_323, '#skF_6', E_324, '#skF_5', F_325, C_326)='#skF_9' | F_325!='#skF_10' | ~m1_subset_1('#skF_4'(D_323, '#skF_6', E_324, '#skF_5', F_325, C_326), '#skF_8') | ~m1_subset_1('#skF_3'(D_323, '#skF_6', E_324, '#skF_5', F_325, C_326), '#skF_7') | k10_mcart_1('#skF_5', '#skF_6', C_326, D_323, F_325)=E_324 | k1_xboole_0=D_323 | k1_xboole_0=C_326 | ~m1_subset_1(F_325, k4_zfmisc_1('#skF_5', '#skF_6', C_326, D_323)))), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_44, c_507])).
% 5.39/2.07  tff(c_516, plain, (![D_34, E_35, F_36]: ('#skF_4'(D_34, '#skF_6', E_35, '#skF_5', F_36, '#skF_7')='#skF_9' | F_36!='#skF_10' | ~m1_subset_1('#skF_4'(D_34, '#skF_6', E_35, '#skF_5', F_36, '#skF_7'), '#skF_8') | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_36, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_34)))), inference(resolution, [status(thm)], [c_30, c_512])).
% 5.39/2.07  tff(c_521, plain, (![D_327, E_328, F_329]: ('#skF_4'(D_327, '#skF_6', E_328, '#skF_5', F_329, '#skF_7')='#skF_9' | F_329!='#skF_10' | ~m1_subset_1('#skF_4'(D_327, '#skF_6', E_328, '#skF_5', F_329, '#skF_7'), '#skF_8') | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', D_327, F_329)=E_328 | k1_xboole_0=D_327 | ~m1_subset_1(F_329, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_327)))), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_40, c_516])).
% 5.39/2.07  tff(c_525, plain, (![E_35, F_36]: ('#skF_4'('#skF_8', '#skF_6', E_35, '#skF_5', F_36, '#skF_7')='#skF_9' | F_36!='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_36)=E_35 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_36, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_28, c_521])).
% 5.39/2.07  tff(c_530, plain, (![E_330, F_331]: ('#skF_4'('#skF_8', '#skF_6', E_330, '#skF_5', F_331, '#skF_7')='#skF_9' | F_331!='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_331)=E_330 | ~m1_subset_1(F_331, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_38, c_525])).
% 5.39/2.07  tff(c_552, plain, (![E_332]: ('#skF_4'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7')='#skF_9' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(resolution, [status(thm)], [c_48, c_530])).
% 5.39/2.07  tff(c_26, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (k4_mcart_1('#skF_1'(D_34, B_32, E_35, A_31, F_36, C_33), '#skF_2'(D_34, B_32, E_35, A_31, F_36, C_33), '#skF_3'(D_34, B_32, E_35, A_31, F_36, C_33), '#skF_4'(D_34, B_32, E_35, A_31, F_36, C_33))=F_36 | k10_mcart_1(A_31, B_32, C_33, D_34, F_36)=E_35 | k1_xboole_0=D_34 | k1_xboole_0=C_33 | k1_xboole_0=B_32 | k1_xboole_0=A_31 | ~m1_subset_1(F_36, k4_zfmisc_1(A_31, B_32, C_33, D_34)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.39/2.07  tff(c_561, plain, (![E_332]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_2'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_3'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_9')='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(superposition, [status(thm), theory('equality')], [c_552, c_26])).
% 5.39/2.07  tff(c_1061, plain, (![E_332]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_2'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_3'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_561])).
% 5.39/2.07  tff(c_1062, plain, (![E_332]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_2'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_3'('#skF_8', '#skF_6', E_332, '#skF_5', '#skF_10', '#skF_7'), '#skF_9')='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_1061])).
% 5.39/2.07  tff(c_1135, plain, (![E_3809]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', E_3809, '#skF_5', '#skF_10', '#skF_7'), '#skF_2'('#skF_8', '#skF_6', E_3809, '#skF_5', '#skF_10', '#skF_7'), '#skF_3'('#skF_8', '#skF_6', E_3809, '#skF_5', '#skF_10', '#skF_7'), '#skF_9')='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3809)), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_1061])).
% 5.39/2.07  tff(c_16, plain, (![G_28, F_27, D_21, A_18, H_29, C_20, B_19, I_30]: (k11_mcart_1(A_18, B_19, C_20, D_21, k4_mcart_1(F_27, G_28, H_29, I_30))=I_30 | k1_xboole_0=D_21 | k1_xboole_0=C_20 | k1_xboole_0=B_19 | k1_xboole_0=A_18 | ~m1_subset_1(k4_mcart_1(F_27, G_28, H_29, I_30), k4_zfmisc_1(A_18, B_19, C_20, D_21)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.39/2.07  tff(c_1525, plain, (![C_4607, A_4606, D_4608, B_4609, E_4605]: (k11_mcart_1(A_4606, B_4609, C_4607, D_4608, k4_mcart_1('#skF_1'('#skF_8', '#skF_6', E_4605, '#skF_5', '#skF_10', '#skF_7'), '#skF_2'('#skF_8', '#skF_6', E_4605, '#skF_5', '#skF_10', '#skF_7'), '#skF_3'('#skF_8', '#skF_6', E_4605, '#skF_5', '#skF_10', '#skF_7'), '#skF_9'))='#skF_9' | k1_xboole_0=D_4608 | k1_xboole_0=C_4607 | k1_xboole_0=B_4609 | k1_xboole_0=A_4606 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_4606, B_4609, C_4607, D_4608)) | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_4605)), inference(superposition, [status(thm), theory('equality')], [c_1135, c_16])).
% 5.39/2.07  tff(c_1534, plain, (![C_4607, A_4606, D_4608, B_4609, E_332]: (k11_mcart_1(A_4606, B_4609, C_4607, D_4608, '#skF_10')='#skF_9' | k1_xboole_0=D_4608 | k1_xboole_0=C_4607 | k1_xboole_0=B_4609 | k1_xboole_0=A_4606 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_4606, B_4609, C_4607, D_4608)) | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332 | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(superposition, [status(thm), theory('equality')], [c_1062, c_1525])).
% 5.39/2.07  tff(c_1562, plain, (![E_332]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332 | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(splitLeft, [status(thm)], [c_1534])).
% 5.39/2.07  tff(c_3208, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_6'), inference(factorization, [status(thm), theory('equality')], [c_1562])).
% 5.39/2.07  tff(c_1583, plain, (![E_332]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_332)), inference(factorization, [status(thm), theory('equality')], [c_1562])).
% 5.39/2.07  tff(c_4349, plain, (![E_21707]: (E_21707='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3208, c_1583])).
% 5.39/2.07  tff(c_4765, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4349, c_42])).
% 5.39/2.07  tff(c_4767, plain, (![A_25996, B_25997, C_25998, D_25999]: (k11_mcart_1(A_25996, B_25997, C_25998, D_25999, '#skF_10')='#skF_9' | k1_xboole_0=D_25999 | k1_xboole_0=C_25998 | k1_xboole_0=B_25997 | k1_xboole_0=A_25996 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_25996, B_25997, C_25998, D_25999)))), inference(splitRight, [status(thm)], [c_1534])).
% 5.39/2.07  tff(c_4771, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_4767])).
% 5.39/2.07  tff(c_4773, plain, (k2_mcart_1('#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_4771])).
% 5.39/2.07  tff(c_4775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_156, c_4773])).
% 5.39/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.39/2.07  
% 5.39/2.07  Inference rules
% 5.39/2.07  ----------------------
% 5.39/2.07  #Ref     : 0
% 5.39/2.07  #Sup     : 720
% 5.39/2.07  #Fact    : 4
% 5.39/2.07  #Define  : 0
% 5.39/2.07  #Split   : 11
% 5.39/2.07  #Chain   : 0
% 5.39/2.07  #Close   : 0
% 5.39/2.07  
% 5.39/2.07  Ordering : KBO
% 5.39/2.07  
% 5.39/2.07  Simplification rules
% 5.39/2.07  ----------------------
% 5.39/2.07  #Subsume      : 94
% 5.39/2.07  #Demod        : 174
% 5.39/2.07  #Tautology    : 106
% 5.39/2.07  #SimpNegUnit  : 33
% 5.39/2.07  #BackRed      : 1
% 5.39/2.07  
% 5.39/2.07  #Partial instantiations: 5790
% 5.39/2.07  #Strategies tried      : 1
% 5.39/2.07  
% 5.39/2.07  Timing (in seconds)
% 5.39/2.07  ----------------------
% 5.39/2.07  Preprocessing        : 0.35
% 5.39/2.07  Parsing              : 0.18
% 5.39/2.07  CNF conversion       : 0.03
% 5.39/2.07  Main loop            : 0.94
% 5.39/2.07  Inferencing          : 0.48
% 5.39/2.07  Reduction            : 0.21
% 5.39/2.07  Demodulation         : 0.15
% 5.39/2.07  BG Simplification    : 0.05
% 5.39/2.07  Subsumption          : 0.14
% 5.39/2.07  Abstraction          : 0.07
% 5.39/2.07  MUC search           : 0.00
% 5.39/2.07  Cooper               : 0.00
% 5.39/2.07  Total                : 1.32
% 5.73/2.07  Index Insertion      : 0.00
% 5.73/2.07  Index Deletion       : 0.00
% 5.73/2.07  Index Matching       : 0.00
% 5.73/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
