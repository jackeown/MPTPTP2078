%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:18 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 460 expanded)
%              Number of leaves         :   26 ( 195 expanded)
%              Depth                    :   20
%              Number of atoms          :  225 (3132 expanded)
%              Number of equality atoms :  167 (2019 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_113,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

tff(f_84,axiom,(
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
                         => E = H ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k9_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_56,axiom,(
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

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( m1_subset_1('#skF_4'(A_21,D_24,C_23,F_26,B_22,E_25),D_24)
      | k9_mcart_1(A_21,B_22,C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(F_26,k4_zfmisc_1(A_21,B_22,C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( m1_subset_1('#skF_3'(A_21,D_24,C_23,F_26,B_22,E_25),C_23)
      | k9_mcart_1(A_21,B_22,C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(F_26,k4_zfmisc_1(A_21,B_22,C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( m1_subset_1('#skF_1'(A_21,D_24,C_23,F_26,B_22,E_25),A_21)
      | k9_mcart_1(A_21,B_22,C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(F_26,k4_zfmisc_1(A_21,B_22,C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( m1_subset_1('#skF_2'(A_21,D_24,C_23,F_26,B_22,E_25),B_22)
      | k9_mcart_1(A_21,B_22,C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(F_26,k4_zfmisc_1(A_21,B_22,C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_239,plain,(
    ! [E_227,F_225,B_226,D_223,C_224,A_222] :
      ( k4_mcart_1('#skF_1'(A_222,D_223,C_224,F_225,B_226,E_227),'#skF_2'(A_222,D_223,C_224,F_225,B_226,E_227),'#skF_3'(A_222,D_223,C_224,F_225,B_226,E_227),'#skF_4'(A_222,D_223,C_224,F_225,B_226,E_227)) = F_225
      | k9_mcart_1(A_222,B_226,C_224,D_223,F_225) = E_227
      | k1_xboole_0 = D_223
      | k1_xboole_0 = C_224
      | k1_xboole_0 = B_226
      | k1_xboole_0 = A_222
      | ~ m1_subset_1(F_225,k4_zfmisc_1(A_222,B_226,C_224,D_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [I_80,G_68,H_76,J_82] :
      ( I_80 = '#skF_9'
      | k4_mcart_1(G_68,H_76,I_80,J_82) != '#skF_10'
      | ~ m1_subset_1(J_82,'#skF_8')
      | ~ m1_subset_1(I_80,'#skF_7')
      | ~ m1_subset_1(H_76,'#skF_6')
      | ~ m1_subset_1(G_68,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_314,plain,(
    ! [A_263,D_260,E_262,C_261,B_258,F_259] :
      ( '#skF_3'(A_263,D_260,C_261,F_259,B_258,E_262) = '#skF_9'
      | F_259 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_263,D_260,C_261,F_259,B_258,E_262),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_263,D_260,C_261,F_259,B_258,E_262),'#skF_7')
      | ~ m1_subset_1('#skF_2'(A_263,D_260,C_261,F_259,B_258,E_262),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_263,D_260,C_261,F_259,B_258,E_262),'#skF_5')
      | k9_mcart_1(A_263,B_258,C_261,D_260,F_259) = E_262
      | k1_xboole_0 = D_260
      | k1_xboole_0 = C_261
      | k1_xboole_0 = B_258
      | k1_xboole_0 = A_263
      | ~ m1_subset_1(F_259,k4_zfmisc_1(A_263,B_258,C_261,D_260)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_36])).

tff(c_318,plain,(
    ! [A_21,D_24,C_23,F_26,E_25] :
      ( '#skF_3'(A_21,D_24,C_23,F_26,'#skF_6',E_25) = '#skF_9'
      | F_26 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_21,D_24,C_23,F_26,'#skF_6',E_25),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_21,D_24,C_23,F_26,'#skF_6',E_25),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_21,D_24,C_23,F_26,'#skF_6',E_25),'#skF_5')
      | k9_mcart_1(A_21,'#skF_6',C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(F_26,k4_zfmisc_1(A_21,'#skF_6',C_23,D_24)) ) ),
    inference(resolution,[status(thm)],[c_22,c_314])).

tff(c_323,plain,(
    ! [C_266,D_265,F_267,A_264,E_268] :
      ( '#skF_3'(A_264,D_265,C_266,F_267,'#skF_6',E_268) = '#skF_9'
      | F_267 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_264,D_265,C_266,F_267,'#skF_6',E_268),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_264,D_265,C_266,F_267,'#skF_6',E_268),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_264,D_265,C_266,F_267,'#skF_6',E_268),'#skF_5')
      | k9_mcart_1(A_264,'#skF_6',C_266,D_265,F_267) = E_268
      | k1_xboole_0 = D_265
      | k1_xboole_0 = C_266
      | k1_xboole_0 = A_264
      | ~ m1_subset_1(F_267,k4_zfmisc_1(A_264,'#skF_6',C_266,D_265)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_318])).

tff(c_327,plain,(
    ! [D_24,C_23,F_26,E_25] :
      ( '#skF_3'('#skF_5',D_24,C_23,F_26,'#skF_6',E_25) = '#skF_9'
      | F_26 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5',D_24,C_23,F_26,'#skF_6',E_25),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_5',D_24,C_23,F_26,'#skF_6',E_25),'#skF_7')
      | k9_mcart_1('#skF_5','#skF_6',C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_26,k4_zfmisc_1('#skF_5','#skF_6',C_23,D_24)) ) ),
    inference(resolution,[status(thm)],[c_24,c_323])).

tff(c_348,plain,(
    ! [D_279,C_280,F_281,E_282] :
      ( '#skF_3'('#skF_5',D_279,C_280,F_281,'#skF_6',E_282) = '#skF_9'
      | F_281 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5',D_279,C_280,F_281,'#skF_6',E_282),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_5',D_279,C_280,F_281,'#skF_6',E_282),'#skF_7')
      | k9_mcart_1('#skF_5','#skF_6',C_280,D_279,F_281) = E_282
      | k1_xboole_0 = D_279
      | k1_xboole_0 = C_280
      | ~ m1_subset_1(F_281,k4_zfmisc_1('#skF_5','#skF_6',C_280,D_279)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_34,c_327])).

tff(c_352,plain,(
    ! [D_24,F_26,E_25] :
      ( '#skF_3'('#skF_5',D_24,'#skF_7',F_26,'#skF_6',E_25) = '#skF_9'
      | F_26 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5',D_24,'#skF_7',F_26,'#skF_6',E_25),'#skF_8')
      | k9_mcart_1('#skF_5','#skF_6','#skF_7',D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_26,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_24)) ) ),
    inference(resolution,[status(thm)],[c_20,c_348])).

tff(c_357,plain,(
    ! [D_283,F_284,E_285] :
      ( '#skF_3'('#skF_5',D_283,'#skF_7',F_284,'#skF_6',E_285) = '#skF_9'
      | F_284 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5',D_283,'#skF_7',F_284,'#skF_6',E_285),'#skF_8')
      | k9_mcart_1('#skF_5','#skF_6','#skF_7',D_283,F_284) = E_285
      | k1_xboole_0 = D_283
      | ~ m1_subset_1(F_284,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_283)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_30,c_352])).

tff(c_361,plain,(
    ! [F_26,E_25] :
      ( '#skF_3'('#skF_5','#skF_8','#skF_7',F_26,'#skF_6',E_25) = '#skF_9'
      | F_26 != '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_26) = E_25
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_26,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_18,c_357])).

tff(c_366,plain,(
    ! [F_286,E_287] :
      ( '#skF_3'('#skF_5','#skF_8','#skF_7',F_286,'#skF_6',E_287) = '#skF_9'
      | F_286 != '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_286) = E_287
      | ~ m1_subset_1(F_286,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_28,c_361])).

tff(c_388,plain,(
    ! [E_288] :
      ( '#skF_3'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288) = '#skF_9'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ) ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_16,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( k4_mcart_1('#skF_1'(A_21,D_24,C_23,F_26,B_22,E_25),'#skF_2'(A_21,D_24,C_23,F_26,B_22,E_25),'#skF_3'(A_21,D_24,C_23,F_26,B_22,E_25),'#skF_4'(A_21,D_24,C_23,F_26,B_22,E_25)) = F_26
      | k9_mcart_1(A_21,B_22,C_23,D_24,F_26) = E_25
      | k1_xboole_0 = D_24
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(F_26,k4_zfmisc_1(A_21,B_22,C_23,D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_400,plain,(
    ! [E_288] :
      ( k4_mcart_1('#skF_1'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288),'#skF_2'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288),'#skF_9','#skF_4'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288)) = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_16])).

tff(c_834,plain,(
    ! [E_288] :
      ( k4_mcart_1('#skF_1'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288),'#skF_2'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288),'#skF_9','#skF_4'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288)) = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_400])).

tff(c_835,plain,(
    ! [E_288] :
      ( k4_mcart_1('#skF_1'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288),'#skF_2'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288),'#skF_9','#skF_4'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_288)) = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_834])).

tff(c_1022,plain,(
    ! [E_2875] :
      ( k4_mcart_1('#skF_1'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_2875),'#skF_2'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_2875),'#skF_9','#skF_4'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_2875)) = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_2875 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_834])).

tff(c_8,plain,(
    ! [D_11,A_8,I_20,H_19,F_17,C_10,B_9,G_18] :
      ( k10_mcart_1(A_8,B_9,C_10,D_11,k4_mcart_1(F_17,G_18,H_19,I_20)) = H_19
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k4_mcart_1(F_17,G_18,H_19,I_20),k4_zfmisc_1(A_8,B_9,C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1438,plain,(
    ! [A_3295,C_3298,E_3296,B_3297,D_3299] :
      ( k10_mcart_1(A_3295,B_3297,C_3298,D_3299,k4_mcart_1('#skF_1'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_3296),'#skF_2'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_3296),'#skF_9','#skF_4'('#skF_5','#skF_8','#skF_7','#skF_10','#skF_6',E_3296))) = '#skF_9'
      | k1_xboole_0 = D_3299
      | k1_xboole_0 = C_3298
      | k1_xboole_0 = B_3297
      | k1_xboole_0 = A_3295
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_3295,B_3297,C_3298,D_3299))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_8])).

tff(c_1447,plain,(
    ! [A_3295,C_3298,B_3297,D_3299,E_288] :
      ( k10_mcart_1(A_3295,B_3297,C_3298,D_3299,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_3299
      | k1_xboole_0 = C_3298
      | k1_xboole_0 = B_3297
      | k1_xboole_0 = A_3295
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_3295,B_3297,C_3298,D_3299))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_1438])).

tff(c_1474,plain,(
    ! [E_288] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ) ),
    inference(splitLeft,[status(thm)],[c_1447])).

tff(c_2755,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_6' ),
    inference(factorization,[status(thm),theory(equality)],[c_1474])).

tff(c_1495,plain,(
    ! [E_288] : k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_288 ),
    inference(factorization,[status(thm),theory(equality)],[c_1474])).

tff(c_3396,plain,(
    ! [E_12308] : E_12308 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2755,c_1495])).

tff(c_3778,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3396,c_32])).

tff(c_3864,plain,(
    ! [A_15340,B_15341,C_15342,D_15343] :
      ( k10_mcart_1(A_15340,B_15341,C_15342,D_15343,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_15343
      | k1_xboole_0 = C_15342
      | k1_xboole_0 = B_15341
      | k1_xboole_0 = A_15340
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_15340,B_15341,C_15342,D_15343)) ) ),
    inference(splitRight,[status(thm)],[c_1447])).

tff(c_3874,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_3864])).

tff(c_3878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_26,c_3874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:30:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.89  
% 4.82/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.89  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 4.82/1.89  
% 4.82/1.89  %Foreground sorts:
% 4.82/1.89  
% 4.82/1.89  
% 4.82/1.89  %Background operators:
% 4.82/1.89  
% 4.82/1.89  
% 4.82/1.89  %Foreground operators:
% 4.82/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.89  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.82/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.82/1.89  tff('#skF_10', type, '#skF_10': $i).
% 4.82/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.89  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.82/1.89  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.82/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.82/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.82/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.89  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.82/1.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 4.82/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.89  
% 4.82/1.91  tff(f_113, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 4.82/1.91  tff(f_84, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_mcart_1)).
% 4.82/1.91  tff(f_56, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 4.82/1.91  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_30, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_28, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_26, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_38, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_18, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (m1_subset_1('#skF_4'(A_21, D_24, C_23, F_26, B_22, E_25), D_24) | k9_mcart_1(A_21, B_22, C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | ~m1_subset_1(F_26, k4_zfmisc_1(A_21, B_22, C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.91  tff(c_20, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (m1_subset_1('#skF_3'(A_21, D_24, C_23, F_26, B_22, E_25), C_23) | k9_mcart_1(A_21, B_22, C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | ~m1_subset_1(F_26, k4_zfmisc_1(A_21, B_22, C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.91  tff(c_24, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (m1_subset_1('#skF_1'(A_21, D_24, C_23, F_26, B_22, E_25), A_21) | k9_mcart_1(A_21, B_22, C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | ~m1_subset_1(F_26, k4_zfmisc_1(A_21, B_22, C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.91  tff(c_22, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (m1_subset_1('#skF_2'(A_21, D_24, C_23, F_26, B_22, E_25), B_22) | k9_mcart_1(A_21, B_22, C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | ~m1_subset_1(F_26, k4_zfmisc_1(A_21, B_22, C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.91  tff(c_239, plain, (![E_227, F_225, B_226, D_223, C_224, A_222]: (k4_mcart_1('#skF_1'(A_222, D_223, C_224, F_225, B_226, E_227), '#skF_2'(A_222, D_223, C_224, F_225, B_226, E_227), '#skF_3'(A_222, D_223, C_224, F_225, B_226, E_227), '#skF_4'(A_222, D_223, C_224, F_225, B_226, E_227))=F_225 | k9_mcart_1(A_222, B_226, C_224, D_223, F_225)=E_227 | k1_xboole_0=D_223 | k1_xboole_0=C_224 | k1_xboole_0=B_226 | k1_xboole_0=A_222 | ~m1_subset_1(F_225, k4_zfmisc_1(A_222, B_226, C_224, D_223)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.91  tff(c_36, plain, (![I_80, G_68, H_76, J_82]: (I_80='#skF_9' | k4_mcart_1(G_68, H_76, I_80, J_82)!='#skF_10' | ~m1_subset_1(J_82, '#skF_8') | ~m1_subset_1(I_80, '#skF_7') | ~m1_subset_1(H_76, '#skF_6') | ~m1_subset_1(G_68, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.82/1.91  tff(c_314, plain, (![A_263, D_260, E_262, C_261, B_258, F_259]: ('#skF_3'(A_263, D_260, C_261, F_259, B_258, E_262)='#skF_9' | F_259!='#skF_10' | ~m1_subset_1('#skF_4'(A_263, D_260, C_261, F_259, B_258, E_262), '#skF_8') | ~m1_subset_1('#skF_3'(A_263, D_260, C_261, F_259, B_258, E_262), '#skF_7') | ~m1_subset_1('#skF_2'(A_263, D_260, C_261, F_259, B_258, E_262), '#skF_6') | ~m1_subset_1('#skF_1'(A_263, D_260, C_261, F_259, B_258, E_262), '#skF_5') | k9_mcart_1(A_263, B_258, C_261, D_260, F_259)=E_262 | k1_xboole_0=D_260 | k1_xboole_0=C_261 | k1_xboole_0=B_258 | k1_xboole_0=A_263 | ~m1_subset_1(F_259, k4_zfmisc_1(A_263, B_258, C_261, D_260)))), inference(superposition, [status(thm), theory('equality')], [c_239, c_36])).
% 4.82/1.91  tff(c_318, plain, (![A_21, D_24, C_23, F_26, E_25]: ('#skF_3'(A_21, D_24, C_23, F_26, '#skF_6', E_25)='#skF_9' | F_26!='#skF_10' | ~m1_subset_1('#skF_4'(A_21, D_24, C_23, F_26, '#skF_6', E_25), '#skF_8') | ~m1_subset_1('#skF_3'(A_21, D_24, C_23, F_26, '#skF_6', E_25), '#skF_7') | ~m1_subset_1('#skF_1'(A_21, D_24, C_23, F_26, '#skF_6', E_25), '#skF_5') | k9_mcart_1(A_21, '#skF_6', C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0='#skF_6' | k1_xboole_0=A_21 | ~m1_subset_1(F_26, k4_zfmisc_1(A_21, '#skF_6', C_23, D_24)))), inference(resolution, [status(thm)], [c_22, c_314])).
% 4.82/1.91  tff(c_323, plain, (![C_266, D_265, F_267, A_264, E_268]: ('#skF_3'(A_264, D_265, C_266, F_267, '#skF_6', E_268)='#skF_9' | F_267!='#skF_10' | ~m1_subset_1('#skF_4'(A_264, D_265, C_266, F_267, '#skF_6', E_268), '#skF_8') | ~m1_subset_1('#skF_3'(A_264, D_265, C_266, F_267, '#skF_6', E_268), '#skF_7') | ~m1_subset_1('#skF_1'(A_264, D_265, C_266, F_267, '#skF_6', E_268), '#skF_5') | k9_mcart_1(A_264, '#skF_6', C_266, D_265, F_267)=E_268 | k1_xboole_0=D_265 | k1_xboole_0=C_266 | k1_xboole_0=A_264 | ~m1_subset_1(F_267, k4_zfmisc_1(A_264, '#skF_6', C_266, D_265)))), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_318])).
% 4.82/1.91  tff(c_327, plain, (![D_24, C_23, F_26, E_25]: ('#skF_3'('#skF_5', D_24, C_23, F_26, '#skF_6', E_25)='#skF_9' | F_26!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', D_24, C_23, F_26, '#skF_6', E_25), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_5', D_24, C_23, F_26, '#skF_6', E_25), '#skF_7') | k9_mcart_1('#skF_5', '#skF_6', C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_26, k4_zfmisc_1('#skF_5', '#skF_6', C_23, D_24)))), inference(resolution, [status(thm)], [c_24, c_323])).
% 4.82/1.91  tff(c_348, plain, (![D_279, C_280, F_281, E_282]: ('#skF_3'('#skF_5', D_279, C_280, F_281, '#skF_6', E_282)='#skF_9' | F_281!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', D_279, C_280, F_281, '#skF_6', E_282), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_5', D_279, C_280, F_281, '#skF_6', E_282), '#skF_7') | k9_mcart_1('#skF_5', '#skF_6', C_280, D_279, F_281)=E_282 | k1_xboole_0=D_279 | k1_xboole_0=C_280 | ~m1_subset_1(F_281, k4_zfmisc_1('#skF_5', '#skF_6', C_280, D_279)))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_34, c_327])).
% 4.82/1.91  tff(c_352, plain, (![D_24, F_26, E_25]: ('#skF_3'('#skF_5', D_24, '#skF_7', F_26, '#skF_6', E_25)='#skF_9' | F_26!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', D_24, '#skF_7', F_26, '#skF_6', E_25), '#skF_8') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_26, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_24)))), inference(resolution, [status(thm)], [c_20, c_348])).
% 4.82/1.91  tff(c_357, plain, (![D_283, F_284, E_285]: ('#skF_3'('#skF_5', D_283, '#skF_7', F_284, '#skF_6', E_285)='#skF_9' | F_284!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', D_283, '#skF_7', F_284, '#skF_6', E_285), '#skF_8') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', D_283, F_284)=E_285 | k1_xboole_0=D_283 | ~m1_subset_1(F_284, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_283)))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_30, c_352])).
% 4.82/1.91  tff(c_361, plain, (![F_26, E_25]: ('#skF_3'('#skF_5', '#skF_8', '#skF_7', F_26, '#skF_6', E_25)='#skF_9' | F_26!='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_26)=E_25 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_26, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_18, c_357])).
% 4.82/1.91  tff(c_366, plain, (![F_286, E_287]: ('#skF_3'('#skF_5', '#skF_8', '#skF_7', F_286, '#skF_6', E_287)='#skF_9' | F_286!='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_286)=E_287 | ~m1_subset_1(F_286, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_28, c_361])).
% 4.82/1.91  tff(c_388, plain, (![E_288]: ('#skF_3'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288)='#skF_9' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(resolution, [status(thm)], [c_38, c_366])).
% 4.82/1.91  tff(c_16, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (k4_mcart_1('#skF_1'(A_21, D_24, C_23, F_26, B_22, E_25), '#skF_2'(A_21, D_24, C_23, F_26, B_22, E_25), '#skF_3'(A_21, D_24, C_23, F_26, B_22, E_25), '#skF_4'(A_21, D_24, C_23, F_26, B_22, E_25))=F_26 | k9_mcart_1(A_21, B_22, C_23, D_24, F_26)=E_25 | k1_xboole_0=D_24 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_21 | ~m1_subset_1(F_26, k4_zfmisc_1(A_21, B_22, C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.91  tff(c_400, plain, (![E_288]: (k4_mcart_1('#skF_1'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288), '#skF_2'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288), '#skF_9', '#skF_4'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288))='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(superposition, [status(thm), theory('equality')], [c_388, c_16])).
% 4.82/1.91  tff(c_834, plain, (![E_288]: (k4_mcart_1('#skF_1'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288), '#skF_2'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288), '#skF_9', '#skF_4'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_400])).
% 4.82/1.91  tff(c_835, plain, (![E_288]: (k4_mcart_1('#skF_1'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288), '#skF_2'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288), '#skF_9', '#skF_4'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_288))='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_834])).
% 4.82/1.91  tff(c_1022, plain, (![E_2875]: (k4_mcart_1('#skF_1'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_2875), '#skF_2'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_2875), '#skF_9', '#skF_4'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_2875))='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_2875)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_834])).
% 4.82/1.91  tff(c_8, plain, (![D_11, A_8, I_20, H_19, F_17, C_10, B_9, G_18]: (k10_mcart_1(A_8, B_9, C_10, D_11, k4_mcart_1(F_17, G_18, H_19, I_20))=H_19 | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8 | ~m1_subset_1(k4_mcart_1(F_17, G_18, H_19, I_20), k4_zfmisc_1(A_8, B_9, C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.91  tff(c_1438, plain, (![A_3295, C_3298, E_3296, B_3297, D_3299]: (k10_mcart_1(A_3295, B_3297, C_3298, D_3299, k4_mcart_1('#skF_1'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_3296), '#skF_2'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_3296), '#skF_9', '#skF_4'('#skF_5', '#skF_8', '#skF_7', '#skF_10', '#skF_6', E_3296)))='#skF_9' | k1_xboole_0=D_3299 | k1_xboole_0=C_3298 | k1_xboole_0=B_3297 | k1_xboole_0=A_3295 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_3295, B_3297, C_3298, D_3299)) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3296)), inference(superposition, [status(thm), theory('equality')], [c_1022, c_8])).
% 4.82/1.91  tff(c_1447, plain, (![A_3295, C_3298, B_3297, D_3299, E_288]: (k10_mcart_1(A_3295, B_3297, C_3298, D_3299, '#skF_10')='#skF_9' | k1_xboole_0=D_3299 | k1_xboole_0=C_3298 | k1_xboole_0=B_3297 | k1_xboole_0=A_3295 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_3295, B_3297, C_3298, D_3299)) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(superposition, [status(thm), theory('equality')], [c_835, c_1438])).
% 4.82/1.91  tff(c_1474, plain, (![E_288]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(splitLeft, [status(thm)], [c_1447])).
% 4.82/1.91  tff(c_2755, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_6'), inference(factorization, [status(thm), theory('equality')], [c_1474])).
% 4.82/1.91  tff(c_1495, plain, (![E_288]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_288)), inference(factorization, [status(thm), theory('equality')], [c_1474])).
% 4.82/1.91  tff(c_3396, plain, (![E_12308]: (E_12308='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2755, c_1495])).
% 4.82/1.91  tff(c_3778, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3396, c_32])).
% 4.82/1.91  tff(c_3864, plain, (![A_15340, B_15341, C_15342, D_15343]: (k10_mcart_1(A_15340, B_15341, C_15342, D_15343, '#skF_10')='#skF_9' | k1_xboole_0=D_15343 | k1_xboole_0=C_15342 | k1_xboole_0=B_15341 | k1_xboole_0=A_15340 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_15340, B_15341, C_15342, D_15343)))), inference(splitRight, [status(thm)], [c_1447])).
% 4.82/1.91  tff(c_3874, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_3864])).
% 4.82/1.91  tff(c_3878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_3874])).
% 4.82/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.91  
% 4.82/1.91  Inference rules
% 4.82/1.91  ----------------------
% 4.82/1.91  #Ref     : 0
% 4.82/1.91  #Sup     : 505
% 4.82/1.91  #Fact    : 4
% 4.82/1.91  #Define  : 0
% 4.82/1.91  #Split   : 9
% 4.82/1.91  #Chain   : 0
% 4.82/1.91  #Close   : 0
% 4.82/1.91  
% 4.82/1.91  Ordering : KBO
% 4.82/1.91  
% 4.82/1.91  Simplification rules
% 4.82/1.91  ----------------------
% 4.82/1.91  #Subsume      : 58
% 4.82/1.91  #Demod        : 185
% 4.82/1.91  #Tautology    : 94
% 4.82/1.91  #SimpNegUnit  : 62
% 4.82/1.91  #BackRed      : 0
% 4.82/1.91  
% 4.82/1.91  #Partial instantiations: 4130
% 4.82/1.91  #Strategies tried      : 1
% 4.82/1.91  
% 4.82/1.91  Timing (in seconds)
% 4.82/1.91  ----------------------
% 4.82/1.91  Preprocessing        : 0.32
% 4.82/1.91  Parsing              : 0.16
% 4.82/1.91  CNF conversion       : 0.03
% 4.82/1.91  Main loop            : 0.80
% 4.82/1.91  Inferencing          : 0.40
% 4.82/1.91  Reduction            : 0.19
% 4.82/1.91  Demodulation         : 0.13
% 4.82/1.91  BG Simplification    : 0.04
% 4.82/1.91  Subsumption          : 0.14
% 4.82/1.91  Abstraction          : 0.05
% 4.82/1.91  MUC search           : 0.00
% 4.82/1.91  Cooper               : 0.00
% 4.82/1.91  Total                : 1.15
% 5.11/1.91  Index Insertion      : 0.00
% 5.11/1.91  Index Deletion       : 0.00
% 5.11/1.91  Index Matching       : 0.00
% 5.11/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
