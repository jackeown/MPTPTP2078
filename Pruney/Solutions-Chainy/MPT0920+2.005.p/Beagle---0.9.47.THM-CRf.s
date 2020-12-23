%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:17 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 228 expanded)
%              Number of leaves         :   28 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          :  212 (1401 expanded)
%              Number of equality atoms :  152 ( 864 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_62,axiom,(
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

tff(f_89,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( m1_subset_1('#skF_1'(B_13,A_12,D_15,C_14,E_47),A_12)
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( m1_subset_1('#skF_3'(B_13,A_12,D_15,C_14,E_47),C_14)
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( m1_subset_1('#skF_4'(B_13,A_12,D_15,C_14,E_47),D_15)
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( m1_subset_1('#skF_2'(B_13,A_12,D_15,C_14,E_47),B_13)
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_244,plain,(
    ! [A_234,B_233,C_236,E_237,D_235] :
      ( k4_mcart_1('#skF_1'(B_233,A_234,D_235,C_236,E_237),'#skF_2'(B_233,A_234,D_235,C_236,E_237),'#skF_3'(B_233,A_234,D_235,C_236,E_237),'#skF_4'(B_233,A_234,D_235,C_236,E_237)) = E_237
      | ~ m1_subset_1(E_237,k4_zfmisc_1(A_234,B_233,C_236,D_235))
      | k1_xboole_0 = D_235
      | k1_xboole_0 = C_236
      | k1_xboole_0 = B_233
      | k1_xboole_0 = A_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [H_110,G_102,I_114,J_116] :
      ( H_110 = '#skF_9'
      | k4_mcart_1(G_102,H_110,I_114,J_116) != '#skF_10'
      | ~ m1_subset_1(J_116,'#skF_8')
      | ~ m1_subset_1(I_114,'#skF_7')
      | ~ m1_subset_1(H_110,'#skF_6')
      | ~ m1_subset_1(G_102,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_314,plain,(
    ! [A_271,B_267,C_270,D_269,E_268] :
      ( '#skF_2'(B_267,A_271,D_269,C_270,E_268) = '#skF_9'
      | E_268 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(B_267,A_271,D_269,C_270,E_268),'#skF_8')
      | ~ m1_subset_1('#skF_3'(B_267,A_271,D_269,C_270,E_268),'#skF_7')
      | ~ m1_subset_1('#skF_2'(B_267,A_271,D_269,C_270,E_268),'#skF_6')
      | ~ m1_subset_1('#skF_1'(B_267,A_271,D_269,C_270,E_268),'#skF_5')
      | ~ m1_subset_1(E_268,k4_zfmisc_1(A_271,B_267,C_270,D_269))
      | k1_xboole_0 = D_269
      | k1_xboole_0 = C_270
      | k1_xboole_0 = B_267
      | k1_xboole_0 = A_271 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_36])).

tff(c_318,plain,(
    ! [A_12,D_15,C_14,E_47] :
      ( '#skF_2'('#skF_6',A_12,D_15,C_14,E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_6',A_12,D_15,C_14,E_47),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',A_12,D_15,C_14,E_47),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,D_15,C_14,E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6',C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_14,c_314])).

tff(c_375,plain,(
    ! [A_310,D_311,C_312,E_313] :
      ( '#skF_2'('#skF_6',A_310,D_311,C_312,E_313) = '#skF_9'
      | E_313 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_6',A_310,D_311,C_312,E_313),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',A_310,D_311,C_312,E_313),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_310,D_311,C_312,E_313),'#skF_5')
      | ~ m1_subset_1(E_313,k4_zfmisc_1(A_310,'#skF_6',C_312,D_311))
      | k1_xboole_0 = D_311
      | k1_xboole_0 = C_312
      | k1_xboole_0 = A_310 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_318])).

tff(c_379,plain,(
    ! [A_12,C_14,E_47] :
      ( '#skF_2'('#skF_6',A_12,'#skF_8',C_14,E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_6',A_12,'#skF_8',C_14,E_47),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,'#skF_8',C_14,E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6',C_14,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_14
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_10,c_375])).

tff(c_384,plain,(
    ! [A_314,C_315,E_316] :
      ( '#skF_2'('#skF_6',A_314,'#skF_8',C_315,E_316) = '#skF_9'
      | E_316 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_6',A_314,'#skF_8',C_315,E_316),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_314,'#skF_8',C_315,E_316),'#skF_5')
      | ~ m1_subset_1(E_316,k4_zfmisc_1(A_314,'#skF_6',C_315,'#skF_8'))
      | k1_xboole_0 = C_315
      | k1_xboole_0 = A_314 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_28,c_379])).

tff(c_388,plain,(
    ! [A_12,E_47] :
      ( '#skF_2'('#skF_6',A_12,'#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,'#skF_8','#skF_7',E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_12,c_384])).

tff(c_393,plain,(
    ! [A_317,E_318] :
      ( '#skF_2'('#skF_6',A_317,'#skF_8','#skF_7',E_318) = '#skF_9'
      | E_318 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_317,'#skF_8','#skF_7',E_318),'#skF_5')
      | ~ m1_subset_1(E_318,k4_zfmisc_1(A_317,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_317 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_30,c_388])).

tff(c_397,plain,(
    ! [E_47] :
      ( '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1(E_47,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_16,c_393])).

tff(c_402,plain,(
    ! [E_319] :
      ( '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7',E_319) = '#skF_9'
      | E_319 != '#skF_10'
      | ~ m1_subset_1(E_319,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_34,c_397])).

tff(c_426,plain,(
    '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_402])).

tff(c_8,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( k4_mcart_1('#skF_1'(B_13,A_12,D_15,C_14,E_47),'#skF_2'(B_13,A_12,D_15,C_14,E_47),'#skF_3'(B_13,A_12,D_15,C_14,E_47),'#skF_4'(B_13,A_12,D_15,C_14,E_47)) = E_47
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_436,plain,
    ( k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_8])).

tff(c_450,plain,
    ( k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_436])).

tff(c_451,plain,(
    k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_450])).

tff(c_22,plain,(
    ! [A_74,D_77,B_75,I_86,H_85,C_76,G_84,F_83] :
      ( k9_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_83,G_84,H_85,I_86)) = G_84
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74
      | ~ m1_subset_1(k4_mcart_1(F_83,G_84,H_85,I_86),k4_zfmisc_1(A_74,B_75,C_76,D_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_522,plain,(
    ! [A_325,D_322,C_327,A_328,C_324,B_320,D_323,E_321,B_326] :
      ( k9_mcart_1(A_325,B_326,C_324,D_323,k4_mcart_1('#skF_1'(B_320,A_328,D_322,C_327,E_321),'#skF_2'(B_320,A_328,D_322,C_327,E_321),'#skF_3'(B_320,A_328,D_322,C_327,E_321),'#skF_4'(B_320,A_328,D_322,C_327,E_321))) = '#skF_2'(B_320,A_328,D_322,C_327,E_321)
      | k1_xboole_0 = D_323
      | k1_xboole_0 = C_324
      | k1_xboole_0 = B_326
      | k1_xboole_0 = A_325
      | ~ m1_subset_1(E_321,k4_zfmisc_1(A_325,B_326,C_324,D_323))
      | ~ m1_subset_1(E_321,k4_zfmisc_1(A_328,B_320,C_327,D_322))
      | k1_xboole_0 = D_322
      | k1_xboole_0 = C_327
      | k1_xboole_0 = B_320
      | k1_xboole_0 = A_328 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_22])).

tff(c_531,plain,(
    ! [A_325,B_326,C_324,D_323] :
      ( k9_mcart_1(A_325,B_326,C_324,D_323,k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'))) = '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')
      | k1_xboole_0 = D_323
      | k1_xboole_0 = C_324
      | k1_xboole_0 = B_326
      | k1_xboole_0 = A_325
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_325,B_326,C_324,D_323))
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_522])).

tff(c_538,plain,(
    ! [A_325,B_326,C_324,D_323] :
      ( k9_mcart_1(A_325,B_326,C_324,D_323,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_323
      | k1_xboole_0 = C_324
      | k1_xboole_0 = B_326
      | k1_xboole_0 = A_325
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_325,B_326,C_324,D_323))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_451,c_426,c_531])).

tff(c_540,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( k9_mcart_1(A_329,B_330,C_331,D_332,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_332
      | k1_xboole_0 = C_331
      | k1_xboole_0 = B_330
      | k1_xboole_0 = A_329
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_329,B_330,C_331,D_332)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_538])).

tff(c_543,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_540])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_26,c_543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.80/1.44  
% 2.80/1.44  %Foreground sorts:
% 2.80/1.44  
% 2.80/1.44  
% 2.80/1.44  %Background operators:
% 2.80/1.44  
% 2.80/1.44  
% 2.80/1.44  %Foreground operators:
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.80/1.44  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.80/1.44  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.80/1.44  tff('#skF_10', type, '#skF_10': $i).
% 2.80/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.44  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.80/1.44  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.80/1.44  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.44  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.44  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.80/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.44  
% 3.15/1.45  tff(f_118, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_mcart_1)).
% 3.15/1.45  tff(f_62, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.15/1.45  tff(f_89, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 3.15/1.45  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_30, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_28, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_26, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_38, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_16, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), A_12) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_12, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_3'(B_13, A_12, D_15, C_14, E_47), C_14) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_10, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_4'(B_13, A_12, D_15, C_14, E_47), D_15) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_14, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_2'(B_13, A_12, D_15, C_14, E_47), B_13) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_244, plain, (![A_234, B_233, C_236, E_237, D_235]: (k4_mcart_1('#skF_1'(B_233, A_234, D_235, C_236, E_237), '#skF_2'(B_233, A_234, D_235, C_236, E_237), '#skF_3'(B_233, A_234, D_235, C_236, E_237), '#skF_4'(B_233, A_234, D_235, C_236, E_237))=E_237 | ~m1_subset_1(E_237, k4_zfmisc_1(A_234, B_233, C_236, D_235)) | k1_xboole_0=D_235 | k1_xboole_0=C_236 | k1_xboole_0=B_233 | k1_xboole_0=A_234)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_36, plain, (![H_110, G_102, I_114, J_116]: (H_110='#skF_9' | k4_mcart_1(G_102, H_110, I_114, J_116)!='#skF_10' | ~m1_subset_1(J_116, '#skF_8') | ~m1_subset_1(I_114, '#skF_7') | ~m1_subset_1(H_110, '#skF_6') | ~m1_subset_1(G_102, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.15/1.45  tff(c_314, plain, (![A_271, B_267, C_270, D_269, E_268]: ('#skF_2'(B_267, A_271, D_269, C_270, E_268)='#skF_9' | E_268!='#skF_10' | ~m1_subset_1('#skF_4'(B_267, A_271, D_269, C_270, E_268), '#skF_8') | ~m1_subset_1('#skF_3'(B_267, A_271, D_269, C_270, E_268), '#skF_7') | ~m1_subset_1('#skF_2'(B_267, A_271, D_269, C_270, E_268), '#skF_6') | ~m1_subset_1('#skF_1'(B_267, A_271, D_269, C_270, E_268), '#skF_5') | ~m1_subset_1(E_268, k4_zfmisc_1(A_271, B_267, C_270, D_269)) | k1_xboole_0=D_269 | k1_xboole_0=C_270 | k1_xboole_0=B_267 | k1_xboole_0=A_271)), inference(superposition, [status(thm), theory('equality')], [c_244, c_36])).
% 3.15/1.45  tff(c_318, plain, (![A_12, D_15, C_14, E_47]: ('#skF_2'('#skF_6', A_12, D_15, C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_12, D_15, C_14, E_47), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_12, D_15, C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, D_15, C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_14, c_314])).
% 3.15/1.45  tff(c_375, plain, (![A_310, D_311, C_312, E_313]: ('#skF_2'('#skF_6', A_310, D_311, C_312, E_313)='#skF_9' | E_313!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_310, D_311, C_312, E_313), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_310, D_311, C_312, E_313), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_310, D_311, C_312, E_313), '#skF_5') | ~m1_subset_1(E_313, k4_zfmisc_1(A_310, '#skF_6', C_312, D_311)) | k1_xboole_0=D_311 | k1_xboole_0=C_312 | k1_xboole_0=A_310)), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_318])).
% 3.15/1.45  tff(c_379, plain, (![A_12, C_14, E_47]: ('#skF_2'('#skF_6', A_12, '#skF_8', C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_10, c_375])).
% 3.15/1.45  tff(c_384, plain, (![A_314, C_315, E_316]: ('#skF_2'('#skF_6', A_314, '#skF_8', C_315, E_316)='#skF_9' | E_316!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_314, '#skF_8', C_315, E_316), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_314, '#skF_8', C_315, E_316), '#skF_5') | ~m1_subset_1(E_316, k4_zfmisc_1(A_314, '#skF_6', C_315, '#skF_8')) | k1_xboole_0=C_315 | k1_xboole_0=A_314)), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_28, c_379])).
% 3.15/1.45  tff(c_388, plain, (![A_12, E_47]: ('#skF_2'('#skF_6', A_12, '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', '#skF_7', E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_12, c_384])).
% 3.15/1.45  tff(c_393, plain, (![A_317, E_318]: ('#skF_2'('#skF_6', A_317, '#skF_8', '#skF_7', E_318)='#skF_9' | E_318!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_317, '#skF_8', '#skF_7', E_318), '#skF_5') | ~m1_subset_1(E_318, k4_zfmisc_1(A_317, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_317)), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_30, c_388])).
% 3.15/1.45  tff(c_397, plain, (![E_47]: ('#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1(E_47, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_16, c_393])).
% 3.15/1.45  tff(c_402, plain, (![E_319]: ('#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_319)='#skF_9' | E_319!='#skF_10' | ~m1_subset_1(E_319, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_34, c_397])).
% 3.15/1.45  tff(c_426, plain, ('#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_38, c_402])).
% 3.15/1.45  tff(c_8, plain, (![D_15, E_47, C_14, A_12, B_13]: (k4_mcart_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), '#skF_2'(B_13, A_12, D_15, C_14, E_47), '#skF_3'(B_13, A_12, D_15, C_14, E_47), '#skF_4'(B_13, A_12, D_15, C_14, E_47))=E_47 | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_436, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_426, c_8])).
% 3.15/1.45  tff(c_450, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_436])).
% 3.15/1.45  tff(c_451, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_450])).
% 3.15/1.45  tff(c_22, plain, (![A_74, D_77, B_75, I_86, H_85, C_76, G_84, F_83]: (k9_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_83, G_84, H_85, I_86))=G_84 | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74 | ~m1_subset_1(k4_mcart_1(F_83, G_84, H_85, I_86), k4_zfmisc_1(A_74, B_75, C_76, D_77)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.45  tff(c_522, plain, (![A_325, D_322, C_327, A_328, C_324, B_320, D_323, E_321, B_326]: (k9_mcart_1(A_325, B_326, C_324, D_323, k4_mcart_1('#skF_1'(B_320, A_328, D_322, C_327, E_321), '#skF_2'(B_320, A_328, D_322, C_327, E_321), '#skF_3'(B_320, A_328, D_322, C_327, E_321), '#skF_4'(B_320, A_328, D_322, C_327, E_321)))='#skF_2'(B_320, A_328, D_322, C_327, E_321) | k1_xboole_0=D_323 | k1_xboole_0=C_324 | k1_xboole_0=B_326 | k1_xboole_0=A_325 | ~m1_subset_1(E_321, k4_zfmisc_1(A_325, B_326, C_324, D_323)) | ~m1_subset_1(E_321, k4_zfmisc_1(A_328, B_320, C_327, D_322)) | k1_xboole_0=D_322 | k1_xboole_0=C_327 | k1_xboole_0=B_320 | k1_xboole_0=A_328)), inference(superposition, [status(thm), theory('equality')], [c_244, c_22])).
% 3.15/1.45  tff(c_531, plain, (![A_325, B_326, C_324, D_323]: (k9_mcart_1(A_325, B_326, C_324, D_323, k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')))='#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10') | k1_xboole_0=D_323 | k1_xboole_0=C_324 | k1_xboole_0=B_326 | k1_xboole_0=A_325 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_325, B_326, C_324, D_323)) | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_426, c_522])).
% 3.15/1.45  tff(c_538, plain, (![A_325, B_326, C_324, D_323]: (k9_mcart_1(A_325, B_326, C_324, D_323, '#skF_10')='#skF_9' | k1_xboole_0=D_323 | k1_xboole_0=C_324 | k1_xboole_0=B_326 | k1_xboole_0=A_325 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_325, B_326, C_324, D_323)) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_451, c_426, c_531])).
% 3.15/1.45  tff(c_540, plain, (![A_329, B_330, C_331, D_332]: (k9_mcart_1(A_329, B_330, C_331, D_332, '#skF_10')='#skF_9' | k1_xboole_0=D_332 | k1_xboole_0=C_331 | k1_xboole_0=B_330 | k1_xboole_0=A_329 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_329, B_330, C_331, D_332)))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_538])).
% 3.15/1.45  tff(c_543, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_540])).
% 3.15/1.45  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_543])).
% 3.15/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.45  
% 3.15/1.45  Inference rules
% 3.15/1.45  ----------------------
% 3.15/1.45  #Ref     : 0
% 3.15/1.45  #Sup     : 115
% 3.15/1.45  #Fact    : 0
% 3.15/1.45  #Define  : 0
% 3.15/1.45  #Split   : 0
% 3.15/1.45  #Chain   : 0
% 3.15/1.45  #Close   : 0
% 3.15/1.45  
% 3.15/1.45  Ordering : KBO
% 3.15/1.45  
% 3.15/1.45  Simplification rules
% 3.15/1.45  ----------------------
% 3.15/1.45  #Subsume      : 20
% 3.15/1.45  #Demod        : 114
% 3.15/1.45  #Tautology    : 36
% 3.15/1.45  #SimpNegUnit  : 10
% 3.15/1.45  #BackRed      : 0
% 3.15/1.45  
% 3.15/1.45  #Partial instantiations: 0
% 3.15/1.45  #Strategies tried      : 1
% 3.15/1.45  
% 3.15/1.45  Timing (in seconds)
% 3.15/1.45  ----------------------
% 3.15/1.46  Preprocessing        : 0.33
% 3.15/1.46  Parsing              : 0.17
% 3.15/1.46  CNF conversion       : 0.03
% 3.15/1.46  Main loop            : 0.35
% 3.15/1.46  Inferencing          : 0.15
% 3.15/1.46  Reduction            : 0.11
% 3.15/1.46  Demodulation         : 0.08
% 3.15/1.46  BG Simplification    : 0.03
% 3.15/1.46  Subsumption          : 0.06
% 3.15/1.46  Abstraction          : 0.03
% 3.15/1.46  MUC search           : 0.00
% 3.15/1.46  Cooper               : 0.00
% 3.15/1.46  Total                : 0.71
% 3.15/1.46  Index Insertion      : 0.00
% 3.15/1.46  Index Deletion       : 0.00
% 3.15/1.46  Index Matching       : 0.00
% 3.15/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
