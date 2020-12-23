%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:19 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 209 expanded)
%              Number of leaves         :   31 ( 100 expanded)
%              Depth                    :   19
%              Number of atoms          :  213 (1202 expanded)
%              Number of equality atoms :  155 ( 756 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
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

tff(f_117,axiom,(
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

tff(f_64,axiom,(
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

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_267,plain,(
    ! [B_204,E_206,A_203,D_207,C_205] :
      ( k11_mcart_1(A_203,B_204,C_205,D_207,E_206) = k2_mcart_1(E_206)
      | ~ m1_subset_1(E_206,k4_zfmisc_1(A_203,B_204,C_205,D_207))
      | k1_xboole_0 = D_207
      | k1_xboole_0 = C_205
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_203 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_284,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_267])).

tff(c_289,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_284])).

tff(c_36,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_290,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_36])).

tff(c_18,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( m1_subset_1('#skF_1'(C_17,D_18,B_16,E_50,A_15),A_15)
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( m1_subset_1('#skF_3'(C_17,D_18,B_16,E_50,A_15),C_17)
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( m1_subset_1('#skF_4'(C_17,D_18,B_16,E_50,A_15),D_18)
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( m1_subset_1('#skF_2'(C_17,D_18,B_16,E_50,A_15),B_16)
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_618,plain,(
    ! [D_301,A_304,B_302,E_303,C_300] :
      ( k4_mcart_1('#skF_1'(C_300,D_301,B_302,E_303,A_304),'#skF_2'(C_300,D_301,B_302,E_303,A_304),'#skF_3'(C_300,D_301,B_302,E_303,A_304),'#skF_4'(C_300,D_301,B_302,E_303,A_304)) = E_303
      | ~ m1_subset_1(E_303,k4_zfmisc_1(A_304,B_302,C_300,D_301))
      | k1_xboole_0 = D_301
      | k1_xboole_0 = C_300
      | k1_xboole_0 = B_302
      | k1_xboole_0 = A_304 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [J_134,G_120,H_128,I_132] :
      ( J_134 = '#skF_9'
      | k4_mcart_1(G_120,H_128,I_132,J_134) != '#skF_10'
      | ~ m1_subset_1(J_134,'#skF_8')
      | ~ m1_subset_1(I_132,'#skF_7')
      | ~ m1_subset_1(H_128,'#skF_6')
      | ~ m1_subset_1(G_120,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_736,plain,(
    ! [D_328,A_330,E_329,C_327,B_326] :
      ( '#skF_4'(C_327,D_328,B_326,E_329,A_330) = '#skF_9'
      | E_329 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_327,D_328,B_326,E_329,A_330),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_327,D_328,B_326,E_329,A_330),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_327,D_328,B_326,E_329,A_330),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_327,D_328,B_326,E_329,A_330),'#skF_5')
      | ~ m1_subset_1(E_329,k4_zfmisc_1(A_330,B_326,C_327,D_328))
      | k1_xboole_0 = D_328
      | k1_xboole_0 = C_327
      | k1_xboole_0 = B_326
      | k1_xboole_0 = A_330 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_46])).

tff(c_740,plain,(
    ! [C_17,D_18,E_50,A_15] :
      ( '#skF_4'(C_17,D_18,'#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6',C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_16,c_736])).

tff(c_811,plain,(
    ! [C_356,D_357,E_358,A_359] :
      ( '#skF_4'(C_356,D_357,'#skF_6',E_358,A_359) = '#skF_9'
      | E_358 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_356,D_357,'#skF_6',E_358,A_359),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_356,D_357,'#skF_6',E_358,A_359),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_356,D_357,'#skF_6',E_358,A_359),'#skF_5')
      | ~ m1_subset_1(E_358,k4_zfmisc_1(A_359,'#skF_6',C_356,D_357))
      | k1_xboole_0 = D_357
      | k1_xboole_0 = C_356
      | k1_xboole_0 = A_359 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_740])).

tff(c_815,plain,(
    ! [C_17,E_50,A_15] :
      ( '#skF_4'(C_17,'#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_17,'#skF_8','#skF_6',E_50,A_15),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_17,'#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6',C_17,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_12,c_811])).

tff(c_838,plain,(
    ! [C_369,E_370,A_371] :
      ( '#skF_4'(C_369,'#skF_8','#skF_6',E_370,A_371) = '#skF_9'
      | E_370 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_369,'#skF_8','#skF_6',E_370,A_371),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_369,'#skF_8','#skF_6',E_370,A_371),'#skF_5')
      | ~ m1_subset_1(E_370,k4_zfmisc_1(A_371,'#skF_6',C_369,'#skF_8'))
      | k1_xboole_0 = C_369
      | k1_xboole_0 = A_371 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_38,c_815])).

tff(c_842,plain,(
    ! [E_50,A_15] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_14,c_838])).

tff(c_847,plain,(
    ! [E_372,A_373] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_372,A_373) = '#skF_9'
      | E_372 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_372,A_373),'#skF_5')
      | ~ m1_subset_1(E_372,k4_zfmisc_1(A_373,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_373 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_40,c_842])).

tff(c_851,plain,(
    ! [E_50] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_50,'#skF_5') = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_847])).

tff(c_885,plain,(
    ! [E_382] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_382,'#skF_5') = '#skF_9'
      | E_382 != '#skF_10'
      | ~ m1_subset_1(E_382,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_44,c_851])).

tff(c_909,plain,(
    '#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_48,c_885])).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( k4_mcart_1('#skF_1'(C_17,D_18,B_16,E_50,A_15),'#skF_2'(C_17,D_18,B_16,E_50,A_15),'#skF_3'(C_17,D_18,B_16,E_50,A_15),'#skF_4'(C_17,D_18,B_16,E_50,A_15)) = E_50
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_916,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_10])).

tff(c_927,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_916])).

tff(c_928,plain,(
    k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_927])).

tff(c_20,plain,(
    ! [H_97,I_98,B_78,G_96,D_80,A_77,C_79,F_95] :
      ( k11_mcart_1(A_77,B_78,C_79,D_80,k4_mcart_1(F_95,G_96,H_97,I_98)) = I_98
      | ~ m1_subset_1(k4_mcart_1(F_95,G_96,H_97,I_98),k4_zfmisc_1(A_77,B_78,C_79,D_80))
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_948,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k11_mcart_1(A_77,B_78,C_79,D_80,k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9')) = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_77,B_78,C_79,D_80))
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_20])).

tff(c_975,plain,(
    ! [A_383,B_384,C_385,D_386] :
      ( k11_mcart_1(A_383,B_384,C_385,D_386,'#skF_10') = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_383,B_384,C_385,D_386))
      | k1_xboole_0 = D_386
      | k1_xboole_0 = C_385
      | k1_xboole_0 = B_384
      | k1_xboole_0 = A_383 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_948])).

tff(c_984,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_975])).

tff(c_986,plain,
    ( k2_mcart_1('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_984])).

tff(c_988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_290,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.60  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.58/1.60  
% 3.58/1.60  %Foreground sorts:
% 3.58/1.60  
% 3.58/1.60  
% 3.58/1.60  %Background operators:
% 3.58/1.60  
% 3.58/1.60  
% 3.58/1.60  %Foreground operators:
% 3.58/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.58/1.60  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.58/1.60  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.58/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.58/1.60  tff('#skF_10', type, '#skF_10': $i).
% 3.58/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.60  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.58/1.60  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.58/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.58/1.60  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.60  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.58/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.60  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.58/1.60  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.60  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.58/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.60  
% 3.58/1.61  tff(f_146, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_mcart_1)).
% 3.58/1.61  tff(f_117, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.58/1.61  tff(f_64, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.58/1.61  tff(f_92, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 3.58/1.61  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_40, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_38, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_48, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_267, plain, (![B_204, E_206, A_203, D_207, C_205]: (k11_mcart_1(A_203, B_204, C_205, D_207, E_206)=k2_mcart_1(E_206) | ~m1_subset_1(E_206, k4_zfmisc_1(A_203, B_204, C_205, D_207)) | k1_xboole_0=D_207 | k1_xboole_0=C_205 | k1_xboole_0=B_204 | k1_xboole_0=A_203)), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.58/1.61  tff(c_284, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_267])).
% 3.58/1.61  tff(c_289, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_284])).
% 3.58/1.61  tff(c_36, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_290, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_36])).
% 3.58/1.61  tff(c_18, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), A_15) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.61  tff(c_14, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_3'(C_17, D_18, B_16, E_50, A_15), C_17) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.61  tff(c_12, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_4'(C_17, D_18, B_16, E_50, A_15), D_18) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.61  tff(c_16, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_2'(C_17, D_18, B_16, E_50, A_15), B_16) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.61  tff(c_618, plain, (![D_301, A_304, B_302, E_303, C_300]: (k4_mcart_1('#skF_1'(C_300, D_301, B_302, E_303, A_304), '#skF_2'(C_300, D_301, B_302, E_303, A_304), '#skF_3'(C_300, D_301, B_302, E_303, A_304), '#skF_4'(C_300, D_301, B_302, E_303, A_304))=E_303 | ~m1_subset_1(E_303, k4_zfmisc_1(A_304, B_302, C_300, D_301)) | k1_xboole_0=D_301 | k1_xboole_0=C_300 | k1_xboole_0=B_302 | k1_xboole_0=A_304)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.61  tff(c_46, plain, (![J_134, G_120, H_128, I_132]: (J_134='#skF_9' | k4_mcart_1(G_120, H_128, I_132, J_134)!='#skF_10' | ~m1_subset_1(J_134, '#skF_8') | ~m1_subset_1(I_132, '#skF_7') | ~m1_subset_1(H_128, '#skF_6') | ~m1_subset_1(G_120, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.58/1.61  tff(c_736, plain, (![D_328, A_330, E_329, C_327, B_326]: ('#skF_4'(C_327, D_328, B_326, E_329, A_330)='#skF_9' | E_329!='#skF_10' | ~m1_subset_1('#skF_4'(C_327, D_328, B_326, E_329, A_330), '#skF_8') | ~m1_subset_1('#skF_3'(C_327, D_328, B_326, E_329, A_330), '#skF_7') | ~m1_subset_1('#skF_2'(C_327, D_328, B_326, E_329, A_330), '#skF_6') | ~m1_subset_1('#skF_1'(C_327, D_328, B_326, E_329, A_330), '#skF_5') | ~m1_subset_1(E_329, k4_zfmisc_1(A_330, B_326, C_327, D_328)) | k1_xboole_0=D_328 | k1_xboole_0=C_327 | k1_xboole_0=B_326 | k1_xboole_0=A_330)), inference(superposition, [status(thm), theory('equality')], [c_618, c_46])).
% 3.58/1.61  tff(c_740, plain, (![C_17, D_18, E_50, A_15]: ('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_8') | ~m1_subset_1('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_16, c_736])).
% 3.58/1.61  tff(c_811, plain, (![C_356, D_357, E_358, A_359]: ('#skF_4'(C_356, D_357, '#skF_6', E_358, A_359)='#skF_9' | E_358!='#skF_10' | ~m1_subset_1('#skF_4'(C_356, D_357, '#skF_6', E_358, A_359), '#skF_8') | ~m1_subset_1('#skF_3'(C_356, D_357, '#skF_6', E_358, A_359), '#skF_7') | ~m1_subset_1('#skF_1'(C_356, D_357, '#skF_6', E_358, A_359), '#skF_5') | ~m1_subset_1(E_358, k4_zfmisc_1(A_359, '#skF_6', C_356, D_357)) | k1_xboole_0=D_357 | k1_xboole_0=C_356 | k1_xboole_0=A_359)), inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_740])).
% 3.58/1.61  tff(c_815, plain, (![C_17, E_50, A_15]: ('#skF_4'(C_17, '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_811])).
% 3.58/1.61  tff(c_838, plain, (![C_369, E_370, A_371]: ('#skF_4'(C_369, '#skF_8', '#skF_6', E_370, A_371)='#skF_9' | E_370!='#skF_10' | ~m1_subset_1('#skF_3'(C_369, '#skF_8', '#skF_6', E_370, A_371), '#skF_7') | ~m1_subset_1('#skF_1'(C_369, '#skF_8', '#skF_6', E_370, A_371), '#skF_5') | ~m1_subset_1(E_370, k4_zfmisc_1(A_371, '#skF_6', C_369, '#skF_8')) | k1_xboole_0=C_369 | k1_xboole_0=A_371)), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_38, c_815])).
% 3.58/1.61  tff(c_842, plain, (![E_50, A_15]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_838])).
% 3.58/1.61  tff(c_847, plain, (![E_372, A_373]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_372, A_373)='#skF_9' | E_372!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_372, A_373), '#skF_5') | ~m1_subset_1(E_372, k4_zfmisc_1(A_373, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_373)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_40, c_842])).
% 3.58/1.61  tff(c_851, plain, (![E_50]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_50, '#skF_5')='#skF_9' | E_50!='#skF_10' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_18, c_847])).
% 3.58/1.61  tff(c_885, plain, (![E_382]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_382, '#skF_5')='#skF_9' | E_382!='#skF_10' | ~m1_subset_1(E_382, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_44, c_851])).
% 3.58/1.61  tff(c_909, plain, ('#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_48, c_885])).
% 3.58/1.61  tff(c_10, plain, (![B_16, A_15, D_18, E_50, C_17]: (k4_mcart_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), '#skF_2'(C_17, D_18, B_16, E_50, A_15), '#skF_3'(C_17, D_18, B_16, E_50, A_15), '#skF_4'(C_17, D_18, B_16, E_50, A_15))=E_50 | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.61  tff(c_916, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_909, c_10])).
% 3.58/1.61  tff(c_927, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_916])).
% 3.58/1.61  tff(c_928, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_927])).
% 3.58/1.61  tff(c_20, plain, (![H_97, I_98, B_78, G_96, D_80, A_77, C_79, F_95]: (k11_mcart_1(A_77, B_78, C_79, D_80, k4_mcart_1(F_95, G_96, H_97, I_98))=I_98 | ~m1_subset_1(k4_mcart_1(F_95, G_96, H_97, I_98), k4_zfmisc_1(A_77, B_78, C_79, D_80)) | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.58/1.61  tff(c_948, plain, (![A_77, B_78, C_79, D_80]: (k11_mcart_1(A_77, B_78, C_79, D_80, k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_77, B_78, C_79, D_80)) | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77)), inference(superposition, [status(thm), theory('equality')], [c_928, c_20])).
% 3.58/1.61  tff(c_975, plain, (![A_383, B_384, C_385, D_386]: (k11_mcart_1(A_383, B_384, C_385, D_386, '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_383, B_384, C_385, D_386)) | k1_xboole_0=D_386 | k1_xboole_0=C_385 | k1_xboole_0=B_384 | k1_xboole_0=A_383)), inference(demodulation, [status(thm), theory('equality')], [c_928, c_948])).
% 3.58/1.61  tff(c_984, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_975])).
% 3.58/1.61  tff(c_986, plain, (k2_mcart_1('#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_984])).
% 3.58/1.61  tff(c_988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_38, c_290, c_986])).
% 3.58/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.61  
% 3.58/1.61  Inference rules
% 3.58/1.61  ----------------------
% 3.58/1.61  #Ref     : 0
% 3.58/1.61  #Sup     : 219
% 3.58/1.61  #Fact    : 0
% 3.58/1.61  #Define  : 0
% 3.58/1.61  #Split   : 0
% 3.58/1.61  #Chain   : 0
% 3.58/1.61  #Close   : 0
% 3.58/1.61  
% 3.58/1.61  Ordering : KBO
% 3.58/1.61  
% 3.58/1.61  Simplification rules
% 3.58/1.61  ----------------------
% 3.58/1.61  #Subsume      : 23
% 3.58/1.61  #Demod        : 160
% 3.58/1.61  #Tautology    : 60
% 3.58/1.61  #SimpNegUnit  : 12
% 3.58/1.61  #BackRed      : 1
% 3.58/1.61  
% 3.58/1.61  #Partial instantiations: 0
% 3.58/1.61  #Strategies tried      : 1
% 3.58/1.61  
% 3.58/1.61  Timing (in seconds)
% 3.58/1.61  ----------------------
% 3.86/1.61  Preprocessing        : 0.35
% 3.86/1.61  Parsing              : 0.18
% 3.86/1.61  CNF conversion       : 0.03
% 3.86/1.61  Main loop            : 0.49
% 3.86/1.61  Inferencing          : 0.19
% 3.86/1.61  Reduction            : 0.15
% 3.86/1.61  Demodulation         : 0.11
% 3.86/1.61  BG Simplification    : 0.04
% 3.86/1.62  Subsumption          : 0.08
% 3.86/1.62  Abstraction          : 0.06
% 3.86/1.62  MUC search           : 0.00
% 3.86/1.62  Cooper               : 0.00
% 3.86/1.62  Total                : 0.88
% 3.86/1.62  Index Insertion      : 0.00
% 3.86/1.62  Index Deletion       : 0.00
% 3.86/1.62  Index Matching       : 0.00
% 3.86/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
