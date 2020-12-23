%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:18 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 462 expanded)
%              Number of leaves         :   28 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :  225 (3132 expanded)
%              Number of equality atoms :  167 (2019 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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

tff(f_86,axiom,(
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
                         => E = G ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

tff(f_58,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1('#skF_4'(D_28,A_25,C_27,F_30,B_26,E_29),D_28)
      | k8_mcart_1(A_25,B_26,C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(F_30,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1('#skF_3'(D_28,A_25,C_27,F_30,B_26,E_29),C_27)
      | k8_mcart_1(A_25,B_26,C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(F_30,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1('#skF_1'(D_28,A_25,C_27,F_30,B_26,E_29),A_25)
      | k8_mcart_1(A_25,B_26,C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(F_30,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1('#skF_2'(D_28,A_25,C_27,F_30,B_26,E_29),B_26)
      | k8_mcart_1(A_25,B_26,C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(F_30,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_240,plain,(
    ! [C_222,D_220,A_221,F_223,B_224,E_225] :
      ( k4_mcart_1('#skF_1'(D_220,A_221,C_222,F_223,B_224,E_225),'#skF_2'(D_220,A_221,C_222,F_223,B_224,E_225),'#skF_3'(D_220,A_221,C_222,F_223,B_224,E_225),'#skF_4'(D_220,A_221,C_222,F_223,B_224,E_225)) = F_223
      | k8_mcart_1(A_221,B_224,C_222,D_220,F_223) = E_225
      | k1_xboole_0 = D_220
      | k1_xboole_0 = C_222
      | k1_xboole_0 = B_224
      | k1_xboole_0 = A_221
      | ~ m1_subset_1(F_223,k4_zfmisc_1(A_221,B_224,C_222,D_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [I_84,G_72,H_80,J_86] :
      ( I_84 = '#skF_9'
      | k4_mcart_1(G_72,H_80,I_84,J_86) != '#skF_10'
      | ~ m1_subset_1(J_86,'#skF_8')
      | ~ m1_subset_1(I_84,'#skF_7')
      | ~ m1_subset_1(H_80,'#skF_6')
      | ~ m1_subset_1(G_72,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_312,plain,(
    ! [E_256,D_260,C_259,F_257,A_261,B_258] :
      ( '#skF_3'(D_260,A_261,C_259,F_257,B_258,E_256) = '#skF_9'
      | F_257 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_260,A_261,C_259,F_257,B_258,E_256),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_260,A_261,C_259,F_257,B_258,E_256),'#skF_7')
      | ~ m1_subset_1('#skF_2'(D_260,A_261,C_259,F_257,B_258,E_256),'#skF_6')
      | ~ m1_subset_1('#skF_1'(D_260,A_261,C_259,F_257,B_258,E_256),'#skF_5')
      | k8_mcart_1(A_261,B_258,C_259,D_260,F_257) = E_256
      | k1_xboole_0 = D_260
      | k1_xboole_0 = C_259
      | k1_xboole_0 = B_258
      | k1_xboole_0 = A_261
      | ~ m1_subset_1(F_257,k4_zfmisc_1(A_261,B_258,C_259,D_260)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_38])).

tff(c_316,plain,(
    ! [A_25,F_30,E_29,C_27,D_28] :
      ( '#skF_3'(D_28,A_25,C_27,F_30,'#skF_6',E_29) = '#skF_9'
      | F_30 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_28,A_25,C_27,F_30,'#skF_6',E_29),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_28,A_25,C_27,F_30,'#skF_6',E_29),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_28,A_25,C_27,F_30,'#skF_6',E_29),'#skF_5')
      | k8_mcart_1(A_25,'#skF_6',C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(F_30,k4_zfmisc_1(A_25,'#skF_6',C_27,D_28)) ) ),
    inference(resolution,[status(thm)],[c_24,c_312])).

tff(c_349,plain,(
    ! [C_284,E_286,A_283,F_285,D_282] :
      ( '#skF_3'(D_282,A_283,C_284,F_285,'#skF_6',E_286) = '#skF_9'
      | F_285 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_282,A_283,C_284,F_285,'#skF_6',E_286),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_282,A_283,C_284,F_285,'#skF_6',E_286),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_282,A_283,C_284,F_285,'#skF_6',E_286),'#skF_5')
      | k8_mcart_1(A_283,'#skF_6',C_284,D_282,F_285) = E_286
      | k1_xboole_0 = D_282
      | k1_xboole_0 = C_284
      | k1_xboole_0 = A_283
      | ~ m1_subset_1(F_285,k4_zfmisc_1(A_283,'#skF_6',C_284,D_282)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_316])).

tff(c_353,plain,(
    ! [D_28,C_27,F_30,E_29] :
      ( '#skF_3'(D_28,'#skF_5',C_27,F_30,'#skF_6',E_29) = '#skF_9'
      | F_30 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_28,'#skF_5',C_27,F_30,'#skF_6',E_29),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_28,'#skF_5',C_27,F_30,'#skF_6',E_29),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_30,k4_zfmisc_1('#skF_5','#skF_6',C_27,D_28)) ) ),
    inference(resolution,[status(thm)],[c_26,c_349])).

tff(c_358,plain,(
    ! [D_287,C_288,F_289,E_290] :
      ( '#skF_3'(D_287,'#skF_5',C_288,F_289,'#skF_6',E_290) = '#skF_9'
      | F_289 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_287,'#skF_5',C_288,F_289,'#skF_6',E_290),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_287,'#skF_5',C_288,F_289,'#skF_6',E_290),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_288,D_287,F_289) = E_290
      | k1_xboole_0 = D_287
      | k1_xboole_0 = C_288
      | ~ m1_subset_1(F_289,k4_zfmisc_1('#skF_5','#skF_6',C_288,D_287)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_36,c_353])).

tff(c_362,plain,(
    ! [D_28,F_30,E_29] :
      ( '#skF_3'(D_28,'#skF_5','#skF_7',F_30,'#skF_6',E_29) = '#skF_9'
      | F_30 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_28,'#skF_5','#skF_7',F_30,'#skF_6',E_29),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_30,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_28)) ) ),
    inference(resolution,[status(thm)],[c_22,c_358])).

tff(c_367,plain,(
    ! [D_291,F_292,E_293] :
      ( '#skF_3'(D_291,'#skF_5','#skF_7',F_292,'#skF_6',E_293) = '#skF_9'
      | F_292 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_291,'#skF_5','#skF_7',F_292,'#skF_6',E_293),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_291,F_292) = E_293
      | k1_xboole_0 = D_291
      | ~ m1_subset_1(F_292,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_291)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_32,c_362])).

tff(c_371,plain,(
    ! [F_30,E_29] :
      ( '#skF_3'('#skF_8','#skF_5','#skF_7',F_30,'#skF_6',E_29) = '#skF_9'
      | F_30 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_30) = E_29
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_30,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_20,c_367])).

tff(c_376,plain,(
    ! [F_294,E_295] :
      ( '#skF_3'('#skF_8','#skF_5','#skF_7',F_294,'#skF_6',E_295) = '#skF_9'
      | F_294 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_294) = E_295
      | ~ m1_subset_1(F_294,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_30,c_371])).

tff(c_398,plain,(
    ! [E_296] :
      ( '#skF_3'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296) = '#skF_9'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ) ),
    inference(resolution,[status(thm)],[c_40,c_376])).

tff(c_18,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( k4_mcart_1('#skF_1'(D_28,A_25,C_27,F_30,B_26,E_29),'#skF_2'(D_28,A_25,C_27,F_30,B_26,E_29),'#skF_3'(D_28,A_25,C_27,F_30,B_26,E_29),'#skF_4'(D_28,A_25,C_27,F_30,B_26,E_29)) = F_30
      | k8_mcart_1(A_25,B_26,C_27,D_28,F_30) = E_29
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(F_30,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_410,plain,(
    ! [E_296] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296),'#skF_2'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296),'#skF_9','#skF_4'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296)) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_18])).

tff(c_863,plain,(
    ! [E_296] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296),'#skF_2'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296),'#skF_9','#skF_4'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296)) = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_410])).

tff(c_864,plain,(
    ! [E_296] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296),'#skF_2'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296),'#skF_9','#skF_4'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_296)) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_863])).

tff(c_996,plain,(
    ! [E_3108] :
      ( k4_mcart_1('#skF_1'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_3108),'#skF_2'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_3108),'#skF_9','#skF_4'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_3108)) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3108 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_863])).

tff(c_10,plain,(
    ! [I_24,D_15,C_14,A_12,G_22,B_13,H_23,F_21] :
      ( k10_mcart_1(A_12,B_13,C_14,D_15,k4_mcart_1(F_21,G_22,H_23,I_24)) = H_23
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k4_mcart_1(F_21,G_22,H_23,I_24),k4_zfmisc_1(A_12,B_13,C_14,D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1472,plain,(
    ! [D_3628,E_3627,B_3625,A_3626,C_3629] :
      ( k10_mcart_1(A_3626,B_3625,C_3629,D_3628,k4_mcart_1('#skF_1'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_3627),'#skF_2'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_3627),'#skF_9','#skF_4'('#skF_8','#skF_5','#skF_7','#skF_10','#skF_6',E_3627))) = '#skF_9'
      | k1_xboole_0 = D_3628
      | k1_xboole_0 = C_3629
      | k1_xboole_0 = B_3625
      | k1_xboole_0 = A_3626
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_3626,B_3625,C_3629,D_3628))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3627 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_10])).

tff(c_1481,plain,(
    ! [E_296,D_3628,B_3625,A_3626,C_3629] :
      ( k10_mcart_1(A_3626,B_3625,C_3629,D_3628,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_3628
      | k1_xboole_0 = C_3629
      | k1_xboole_0 = B_3625
      | k1_xboole_0 = A_3626
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_3626,B_3625,C_3629,D_3628))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_1472])).

tff(c_1509,plain,(
    ! [E_296] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ) ),
    inference(splitLeft,[status(thm)],[c_1481])).

tff(c_2857,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_8' ),
    inference(factorization,[status(thm),theory(equality)],[c_1509])).

tff(c_1530,plain,(
    ! [E_296] : k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_296 ),
    inference(factorization,[status(thm),theory(equality)],[c_1509])).

tff(c_3973,plain,(
    ! [E_17035] : E_17035 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2857,c_1530])).

tff(c_4308,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3973,c_30])).

tff(c_4310,plain,(
    ! [A_20508,B_20509,C_20510,D_20511] :
      ( k10_mcart_1(A_20508,B_20509,C_20510,D_20511,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_20511
      | k1_xboole_0 = C_20510
      | k1_xboole_0 = B_20509
      | k1_xboole_0 = A_20508
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_20508,B_20509,C_20510,D_20511)) ) ),
    inference(splitRight,[status(thm)],[c_1481])).

tff(c_4320,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_4310])).

tff(c_4324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_28,c_4320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.23/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/1.98  
% 5.23/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/1.98  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 5.23/1.98  
% 5.23/1.98  %Foreground sorts:
% 5.23/1.98  
% 5.23/1.98  
% 5.23/1.98  %Background operators:
% 5.23/1.98  
% 5.23/1.98  
% 5.23/1.98  %Foreground operators:
% 5.23/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.23/1.98  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/1.98  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.23/1.98  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.23/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.23/1.98  tff('#skF_10', type, '#skF_10': $i).
% 5.23/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.23/1.98  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.23/1.98  tff('#skF_9', type, '#skF_9': $i).
% 5.23/1.98  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.23/1.98  tff('#skF_8', type, '#skF_8': $i).
% 5.23/1.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/1.98  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.23/1.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 5.23/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/1.98  
% 5.23/2.00  tff(f_115, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_mcart_1)).
% 5.23/2.00  tff(f_86, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 5.23/2.00  tff(f_58, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 5.23/2.00  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_34, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_32, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_30, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_28, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_40, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_20, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1('#skF_4'(D_28, A_25, C_27, F_30, B_26, E_29), D_28) | k8_mcart_1(A_25, B_26, C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | ~m1_subset_1(F_30, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.00  tff(c_22, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1('#skF_3'(D_28, A_25, C_27, F_30, B_26, E_29), C_27) | k8_mcart_1(A_25, B_26, C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | ~m1_subset_1(F_30, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.00  tff(c_26, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1('#skF_1'(D_28, A_25, C_27, F_30, B_26, E_29), A_25) | k8_mcart_1(A_25, B_26, C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | ~m1_subset_1(F_30, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.00  tff(c_24, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1('#skF_2'(D_28, A_25, C_27, F_30, B_26, E_29), B_26) | k8_mcart_1(A_25, B_26, C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | ~m1_subset_1(F_30, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.00  tff(c_240, plain, (![C_222, D_220, A_221, F_223, B_224, E_225]: (k4_mcart_1('#skF_1'(D_220, A_221, C_222, F_223, B_224, E_225), '#skF_2'(D_220, A_221, C_222, F_223, B_224, E_225), '#skF_3'(D_220, A_221, C_222, F_223, B_224, E_225), '#skF_4'(D_220, A_221, C_222, F_223, B_224, E_225))=F_223 | k8_mcart_1(A_221, B_224, C_222, D_220, F_223)=E_225 | k1_xboole_0=D_220 | k1_xboole_0=C_222 | k1_xboole_0=B_224 | k1_xboole_0=A_221 | ~m1_subset_1(F_223, k4_zfmisc_1(A_221, B_224, C_222, D_220)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.00  tff(c_38, plain, (![I_84, G_72, H_80, J_86]: (I_84='#skF_9' | k4_mcart_1(G_72, H_80, I_84, J_86)!='#skF_10' | ~m1_subset_1(J_86, '#skF_8') | ~m1_subset_1(I_84, '#skF_7') | ~m1_subset_1(H_80, '#skF_6') | ~m1_subset_1(G_72, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.23/2.00  tff(c_312, plain, (![E_256, D_260, C_259, F_257, A_261, B_258]: ('#skF_3'(D_260, A_261, C_259, F_257, B_258, E_256)='#skF_9' | F_257!='#skF_10' | ~m1_subset_1('#skF_4'(D_260, A_261, C_259, F_257, B_258, E_256), '#skF_8') | ~m1_subset_1('#skF_3'(D_260, A_261, C_259, F_257, B_258, E_256), '#skF_7') | ~m1_subset_1('#skF_2'(D_260, A_261, C_259, F_257, B_258, E_256), '#skF_6') | ~m1_subset_1('#skF_1'(D_260, A_261, C_259, F_257, B_258, E_256), '#skF_5') | k8_mcart_1(A_261, B_258, C_259, D_260, F_257)=E_256 | k1_xboole_0=D_260 | k1_xboole_0=C_259 | k1_xboole_0=B_258 | k1_xboole_0=A_261 | ~m1_subset_1(F_257, k4_zfmisc_1(A_261, B_258, C_259, D_260)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_38])).
% 5.23/2.00  tff(c_316, plain, (![A_25, F_30, E_29, C_27, D_28]: ('#skF_3'(D_28, A_25, C_27, F_30, '#skF_6', E_29)='#skF_9' | F_30!='#skF_10' | ~m1_subset_1('#skF_4'(D_28, A_25, C_27, F_30, '#skF_6', E_29), '#skF_8') | ~m1_subset_1('#skF_3'(D_28, A_25, C_27, F_30, '#skF_6', E_29), '#skF_7') | ~m1_subset_1('#skF_1'(D_28, A_25, C_27, F_30, '#skF_6', E_29), '#skF_5') | k8_mcart_1(A_25, '#skF_6', C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0='#skF_6' | k1_xboole_0=A_25 | ~m1_subset_1(F_30, k4_zfmisc_1(A_25, '#skF_6', C_27, D_28)))), inference(resolution, [status(thm)], [c_24, c_312])).
% 5.23/2.00  tff(c_349, plain, (![C_284, E_286, A_283, F_285, D_282]: ('#skF_3'(D_282, A_283, C_284, F_285, '#skF_6', E_286)='#skF_9' | F_285!='#skF_10' | ~m1_subset_1('#skF_4'(D_282, A_283, C_284, F_285, '#skF_6', E_286), '#skF_8') | ~m1_subset_1('#skF_3'(D_282, A_283, C_284, F_285, '#skF_6', E_286), '#skF_7') | ~m1_subset_1('#skF_1'(D_282, A_283, C_284, F_285, '#skF_6', E_286), '#skF_5') | k8_mcart_1(A_283, '#skF_6', C_284, D_282, F_285)=E_286 | k1_xboole_0=D_282 | k1_xboole_0=C_284 | k1_xboole_0=A_283 | ~m1_subset_1(F_285, k4_zfmisc_1(A_283, '#skF_6', C_284, D_282)))), inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_316])).
% 5.23/2.00  tff(c_353, plain, (![D_28, C_27, F_30, E_29]: ('#skF_3'(D_28, '#skF_5', C_27, F_30, '#skF_6', E_29)='#skF_9' | F_30!='#skF_10' | ~m1_subset_1('#skF_4'(D_28, '#skF_5', C_27, F_30, '#skF_6', E_29), '#skF_8') | ~m1_subset_1('#skF_3'(D_28, '#skF_5', C_27, F_30, '#skF_6', E_29), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_30, k4_zfmisc_1('#skF_5', '#skF_6', C_27, D_28)))), inference(resolution, [status(thm)], [c_26, c_349])).
% 5.23/2.00  tff(c_358, plain, (![D_287, C_288, F_289, E_290]: ('#skF_3'(D_287, '#skF_5', C_288, F_289, '#skF_6', E_290)='#skF_9' | F_289!='#skF_10' | ~m1_subset_1('#skF_4'(D_287, '#skF_5', C_288, F_289, '#skF_6', E_290), '#skF_8') | ~m1_subset_1('#skF_3'(D_287, '#skF_5', C_288, F_289, '#skF_6', E_290), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_288, D_287, F_289)=E_290 | k1_xboole_0=D_287 | k1_xboole_0=C_288 | ~m1_subset_1(F_289, k4_zfmisc_1('#skF_5', '#skF_6', C_288, D_287)))), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_36, c_353])).
% 5.23/2.00  tff(c_362, plain, (![D_28, F_30, E_29]: ('#skF_3'(D_28, '#skF_5', '#skF_7', F_30, '#skF_6', E_29)='#skF_9' | F_30!='#skF_10' | ~m1_subset_1('#skF_4'(D_28, '#skF_5', '#skF_7', F_30, '#skF_6', E_29), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_30, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_28)))), inference(resolution, [status(thm)], [c_22, c_358])).
% 5.23/2.00  tff(c_367, plain, (![D_291, F_292, E_293]: ('#skF_3'(D_291, '#skF_5', '#skF_7', F_292, '#skF_6', E_293)='#skF_9' | F_292!='#skF_10' | ~m1_subset_1('#skF_4'(D_291, '#skF_5', '#skF_7', F_292, '#skF_6', E_293), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_291, F_292)=E_293 | k1_xboole_0=D_291 | ~m1_subset_1(F_292, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_291)))), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_32, c_362])).
% 5.23/2.00  tff(c_371, plain, (![F_30, E_29]: ('#skF_3'('#skF_8', '#skF_5', '#skF_7', F_30, '#skF_6', E_29)='#skF_9' | F_30!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_30)=E_29 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_30, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_20, c_367])).
% 5.23/2.00  tff(c_376, plain, (![F_294, E_295]: ('#skF_3'('#skF_8', '#skF_5', '#skF_7', F_294, '#skF_6', E_295)='#skF_9' | F_294!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_294)=E_295 | ~m1_subset_1(F_294, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_30, c_371])).
% 5.23/2.00  tff(c_398, plain, (![E_296]: ('#skF_3'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296)='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(resolution, [status(thm)], [c_40, c_376])).
% 5.23/2.00  tff(c_18, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (k4_mcart_1('#skF_1'(D_28, A_25, C_27, F_30, B_26, E_29), '#skF_2'(D_28, A_25, C_27, F_30, B_26, E_29), '#skF_3'(D_28, A_25, C_27, F_30, B_26, E_29), '#skF_4'(D_28, A_25, C_27, F_30, B_26, E_29))=F_30 | k8_mcart_1(A_25, B_26, C_27, D_28, F_30)=E_29 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25 | ~m1_subset_1(F_30, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.23/2.00  tff(c_410, plain, (![E_296]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296), '#skF_2'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296), '#skF_9', '#skF_4'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(superposition, [status(thm), theory('equality')], [c_398, c_18])).
% 5.23/2.00  tff(c_863, plain, (![E_296]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296), '#skF_2'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296), '#skF_9', '#skF_4'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_410])).
% 5.23/2.00  tff(c_864, plain, (![E_296]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296), '#skF_2'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296), '#skF_9', '#skF_4'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_296))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_863])).
% 5.23/2.00  tff(c_996, plain, (![E_3108]: (k4_mcart_1('#skF_1'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_3108), '#skF_2'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_3108), '#skF_9', '#skF_4'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_3108))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3108)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_863])).
% 5.23/2.00  tff(c_10, plain, (![I_24, D_15, C_14, A_12, G_22, B_13, H_23, F_21]: (k10_mcart_1(A_12, B_13, C_14, D_15, k4_mcart_1(F_21, G_22, H_23, I_24))=H_23 | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12 | ~m1_subset_1(k4_mcart_1(F_21, G_22, H_23, I_24), k4_zfmisc_1(A_12, B_13, C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.23/2.00  tff(c_1472, plain, (![D_3628, E_3627, B_3625, A_3626, C_3629]: (k10_mcart_1(A_3626, B_3625, C_3629, D_3628, k4_mcart_1('#skF_1'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_3627), '#skF_2'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_3627), '#skF_9', '#skF_4'('#skF_8', '#skF_5', '#skF_7', '#skF_10', '#skF_6', E_3627)))='#skF_9' | k1_xboole_0=D_3628 | k1_xboole_0=C_3629 | k1_xboole_0=B_3625 | k1_xboole_0=A_3626 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_3626, B_3625, C_3629, D_3628)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3627)), inference(superposition, [status(thm), theory('equality')], [c_996, c_10])).
% 5.23/2.00  tff(c_1481, plain, (![E_296, D_3628, B_3625, A_3626, C_3629]: (k10_mcart_1(A_3626, B_3625, C_3629, D_3628, '#skF_10')='#skF_9' | k1_xboole_0=D_3628 | k1_xboole_0=C_3629 | k1_xboole_0=B_3625 | k1_xboole_0=A_3626 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_3626, B_3625, C_3629, D_3628)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(superposition, [status(thm), theory('equality')], [c_864, c_1472])).
% 5.23/2.00  tff(c_1509, plain, (![E_296]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(splitLeft, [status(thm)], [c_1481])).
% 5.23/2.00  tff(c_2857, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_8'), inference(factorization, [status(thm), theory('equality')], [c_1509])).
% 5.23/2.00  tff(c_1530, plain, (![E_296]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_296)), inference(factorization, [status(thm), theory('equality')], [c_1509])).
% 5.23/2.00  tff(c_3973, plain, (![E_17035]: (E_17035='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2857, c_1530])).
% 5.23/2.00  tff(c_4308, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3973, c_30])).
% 5.23/2.00  tff(c_4310, plain, (![A_20508, B_20509, C_20510, D_20511]: (k10_mcart_1(A_20508, B_20509, C_20510, D_20511, '#skF_10')='#skF_9' | k1_xboole_0=D_20511 | k1_xboole_0=C_20510 | k1_xboole_0=B_20509 | k1_xboole_0=A_20508 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_20508, B_20509, C_20510, D_20511)))), inference(splitRight, [status(thm)], [c_1481])).
% 5.23/2.00  tff(c_4320, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_4310])).
% 5.23/2.00  tff(c_4324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_28, c_4320])).
% 5.23/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.00  
% 5.23/2.00  Inference rules
% 5.23/2.00  ----------------------
% 5.23/2.00  #Ref     : 0
% 5.23/2.00  #Sup     : 673
% 5.23/2.00  #Fact    : 4
% 5.23/2.00  #Define  : 0
% 5.23/2.00  #Split   : 9
% 5.23/2.00  #Chain   : 0
% 5.23/2.00  #Close   : 0
% 5.23/2.00  
% 5.23/2.00  Ordering : KBO
% 5.23/2.00  
% 5.23/2.00  Simplification rules
% 5.23/2.00  ----------------------
% 5.23/2.00  #Subsume      : 81
% 5.23/2.00  #Demod        : 191
% 5.23/2.00  #Tautology    : 102
% 5.23/2.00  #SimpNegUnit  : 62
% 5.23/2.00  #BackRed      : 0
% 5.23/2.00  
% 5.23/2.00  #Partial instantiations: 4556
% 5.23/2.00  #Strategies tried      : 1
% 5.23/2.00  
% 5.23/2.00  Timing (in seconds)
% 5.23/2.00  ----------------------
% 5.23/2.00  Preprocessing        : 0.30
% 5.23/2.00  Parsing              : 0.15
% 5.23/2.00  CNF conversion       : 0.03
% 5.23/2.00  Main loop            : 0.86
% 5.23/2.00  Inferencing          : 0.43
% 5.23/2.00  Reduction            : 0.21
% 5.23/2.00  Demodulation         : 0.15
% 5.23/2.00  BG Simplification    : 0.04
% 5.23/2.00  Subsumption          : 0.14
% 5.23/2.01  Abstraction          : 0.05
% 5.23/2.01  MUC search           : 0.00
% 5.23/2.01  Cooper               : 0.00
% 5.23/2.01  Total                : 1.19
% 5.23/2.01  Index Insertion      : 0.00
% 5.23/2.01  Index Deletion       : 0.00
% 5.23/2.01  Index Matching       : 0.00
% 5.23/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
