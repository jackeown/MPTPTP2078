%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:18 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 177 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  186 (1024 expanded)
%              Number of equality atoms :  130 ( 634 expanded)
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

tff(f_121,negated_conjecture,(
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

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

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

tff(c_400,plain,(
    ! [D_278,C_277,B_279,A_281,E_280] :
      ( k4_mcart_1('#skF_1'(C_277,D_278,B_279,E_280,A_281),'#skF_2'(C_277,D_278,B_279,E_280,A_281),'#skF_3'(C_277,D_278,B_279,E_280,A_281),'#skF_4'(C_277,D_278,B_279,E_280,A_281)) = E_280
      | ~ m1_subset_1(E_280,k4_zfmisc_1(A_281,B_279,C_277,D_278))
      | k1_xboole_0 = D_278
      | k1_xboole_0 = C_277
      | k1_xboole_0 = B_279
      | k1_xboole_0 = A_281 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [I_126,G_114,H_122,J_128] :
      ( I_126 = '#skF_9'
      | k4_mcart_1(G_114,H_122,I_126,J_128) != '#skF_10'
      | ~ m1_subset_1(J_128,'#skF_8')
      | ~ m1_subset_1(I_126,'#skF_7')
      | ~ m1_subset_1(H_122,'#skF_6')
      | ~ m1_subset_1(G_114,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_535,plain,(
    ! [C_330,A_328,B_329,D_331,E_332] :
      ( '#skF_3'(C_330,D_331,B_329,E_332,A_328) = '#skF_9'
      | E_332 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_330,D_331,B_329,E_332,A_328),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_330,D_331,B_329,E_332,A_328),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_330,D_331,B_329,E_332,A_328),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_330,D_331,B_329,E_332,A_328),'#skF_5')
      | ~ m1_subset_1(E_332,k4_zfmisc_1(A_328,B_329,C_330,D_331))
      | k1_xboole_0 = D_331
      | k1_xboole_0 = C_330
      | k1_xboole_0 = B_329
      | k1_xboole_0 = A_328 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_38])).

tff(c_539,plain,(
    ! [C_17,D_18,E_50,A_15] :
      ( '#skF_3'(C_17,D_18,'#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6',C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_16,c_535])).

tff(c_598,plain,(
    ! [C_362,D_363,E_364,A_365] :
      ( '#skF_3'(C_362,D_363,'#skF_6',E_364,A_365) = '#skF_9'
      | E_364 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_362,D_363,'#skF_6',E_364,A_365),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_362,D_363,'#skF_6',E_364,A_365),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_362,D_363,'#skF_6',E_364,A_365),'#skF_5')
      | ~ m1_subset_1(E_364,k4_zfmisc_1(A_365,'#skF_6',C_362,D_363))
      | k1_xboole_0 = D_363
      | k1_xboole_0 = C_362
      | k1_xboole_0 = A_365 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_539])).

tff(c_602,plain,(
    ! [C_17,E_50,A_15] :
      ( '#skF_3'(C_17,'#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_17,'#skF_8','#skF_6',E_50,A_15),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_17,'#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6',C_17,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_12,c_598])).

tff(c_607,plain,(
    ! [C_366,E_367,A_368] :
      ( '#skF_3'(C_366,'#skF_8','#skF_6',E_367,A_368) = '#skF_9'
      | E_367 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_366,'#skF_8','#skF_6',E_367,A_368),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_366,'#skF_8','#skF_6',E_367,A_368),'#skF_5')
      | ~ m1_subset_1(E_367,k4_zfmisc_1(A_368,'#skF_6',C_366,'#skF_8'))
      | k1_xboole_0 = C_366
      | k1_xboole_0 = A_368 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_30,c_30,c_602])).

tff(c_611,plain,(
    ! [E_50,A_15] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_14,c_607])).

tff(c_616,plain,(
    ! [E_369,A_370] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_369,A_370) = '#skF_9'
      | E_369 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_369,A_370),'#skF_5')
      | ~ m1_subset_1(E_369,k4_zfmisc_1(A_370,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_370 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_32,c_611])).

tff(c_620,plain,(
    ! [E_50] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_50,'#skF_5') = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_616])).

tff(c_625,plain,(
    ! [E_371] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_371,'#skF_5') = '#skF_9'
      | E_371 != '#skF_10'
      | ~ m1_subset_1(E_371,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_36,c_620])).

tff(c_649,plain,(
    '#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_625])).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( k4_mcart_1('#skF_1'(C_17,D_18,B_16,E_50,A_15),'#skF_2'(C_17,D_18,B_16,E_50,A_15),'#skF_3'(C_17,D_18,B_16,E_50,A_15),'#skF_4'(C_17,D_18,B_16,E_50,A_15)) = E_50
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_656,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_10])).

tff(c_667,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_656])).

tff(c_668,plain,(
    k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_667])).

tff(c_22,plain,(
    ! [H_97,I_98,B_78,G_96,D_80,A_77,C_79,F_95] :
      ( k10_mcart_1(A_77,B_78,C_79,D_80,k4_mcart_1(F_95,G_96,H_97,I_98)) = H_97
      | ~ m1_subset_1(k4_mcart_1(F_95,G_96,H_97,I_98),k4_zfmisc_1(A_77,B_78,C_79,D_80))
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_734,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k10_mcart_1(A_77,B_78,C_79,D_80,k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'))) = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_77,B_78,C_79,D_80))
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_22])).

tff(c_769,plain,(
    ! [A_381,B_382,C_383,D_384] :
      ( k10_mcart_1(A_381,B_382,C_383,D_384,'#skF_10') = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_381,B_382,C_383,D_384))
      | k1_xboole_0 = D_384
      | k1_xboole_0 = C_383
      | k1_xboole_0 = B_382
      | k1_xboole_0 = A_381 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_734])).

tff(c_778,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_769])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_28,c_778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.61  
% 3.54/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.61  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.54/1.61  
% 3.54/1.61  %Foreground sorts:
% 3.54/1.61  
% 3.54/1.61  
% 3.54/1.61  %Background operators:
% 3.54/1.61  
% 3.54/1.61  
% 3.54/1.61  %Foreground operators:
% 3.54/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.54/1.61  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.54/1.61  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.54/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.61  tff('#skF_10', type, '#skF_10': $i).
% 3.54/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.61  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.54/1.61  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.54/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.54/1.61  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.61  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.61  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.54/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.61  
% 3.92/1.63  tff(f_121, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 3.92/1.63  tff(f_64, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.92/1.63  tff(f_92, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 3.92/1.63  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_34, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_32, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_30, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_28, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_40, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_18, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), A_15) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.63  tff(c_14, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_3'(C_17, D_18, B_16, E_50, A_15), C_17) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.63  tff(c_12, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_4'(C_17, D_18, B_16, E_50, A_15), D_18) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.63  tff(c_16, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_2'(C_17, D_18, B_16, E_50, A_15), B_16) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.63  tff(c_400, plain, (![D_278, C_277, B_279, A_281, E_280]: (k4_mcart_1('#skF_1'(C_277, D_278, B_279, E_280, A_281), '#skF_2'(C_277, D_278, B_279, E_280, A_281), '#skF_3'(C_277, D_278, B_279, E_280, A_281), '#skF_4'(C_277, D_278, B_279, E_280, A_281))=E_280 | ~m1_subset_1(E_280, k4_zfmisc_1(A_281, B_279, C_277, D_278)) | k1_xboole_0=D_278 | k1_xboole_0=C_277 | k1_xboole_0=B_279 | k1_xboole_0=A_281)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.63  tff(c_38, plain, (![I_126, G_114, H_122, J_128]: (I_126='#skF_9' | k4_mcart_1(G_114, H_122, I_126, J_128)!='#skF_10' | ~m1_subset_1(J_128, '#skF_8') | ~m1_subset_1(I_126, '#skF_7') | ~m1_subset_1(H_122, '#skF_6') | ~m1_subset_1(G_114, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.92/1.63  tff(c_535, plain, (![C_330, A_328, B_329, D_331, E_332]: ('#skF_3'(C_330, D_331, B_329, E_332, A_328)='#skF_9' | E_332!='#skF_10' | ~m1_subset_1('#skF_4'(C_330, D_331, B_329, E_332, A_328), '#skF_8') | ~m1_subset_1('#skF_3'(C_330, D_331, B_329, E_332, A_328), '#skF_7') | ~m1_subset_1('#skF_2'(C_330, D_331, B_329, E_332, A_328), '#skF_6') | ~m1_subset_1('#skF_1'(C_330, D_331, B_329, E_332, A_328), '#skF_5') | ~m1_subset_1(E_332, k4_zfmisc_1(A_328, B_329, C_330, D_331)) | k1_xboole_0=D_331 | k1_xboole_0=C_330 | k1_xboole_0=B_329 | k1_xboole_0=A_328)), inference(superposition, [status(thm), theory('equality')], [c_400, c_38])).
% 3.92/1.63  tff(c_539, plain, (![C_17, D_18, E_50, A_15]: ('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_8') | ~m1_subset_1('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_16, c_535])).
% 3.92/1.63  tff(c_598, plain, (![C_362, D_363, E_364, A_365]: ('#skF_3'(C_362, D_363, '#skF_6', E_364, A_365)='#skF_9' | E_364!='#skF_10' | ~m1_subset_1('#skF_4'(C_362, D_363, '#skF_6', E_364, A_365), '#skF_8') | ~m1_subset_1('#skF_3'(C_362, D_363, '#skF_6', E_364, A_365), '#skF_7') | ~m1_subset_1('#skF_1'(C_362, D_363, '#skF_6', E_364, A_365), '#skF_5') | ~m1_subset_1(E_364, k4_zfmisc_1(A_365, '#skF_6', C_362, D_363)) | k1_xboole_0=D_363 | k1_xboole_0=C_362 | k1_xboole_0=A_365)), inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_539])).
% 3.92/1.63  tff(c_602, plain, (![C_17, E_50, A_15]: ('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_598])).
% 3.92/1.63  tff(c_607, plain, (![C_366, E_367, A_368]: ('#skF_3'(C_366, '#skF_8', '#skF_6', E_367, A_368)='#skF_9' | E_367!='#skF_10' | ~m1_subset_1('#skF_3'(C_366, '#skF_8', '#skF_6', E_367, A_368), '#skF_7') | ~m1_subset_1('#skF_1'(C_366, '#skF_8', '#skF_6', E_367, A_368), '#skF_5') | ~m1_subset_1(E_367, k4_zfmisc_1(A_368, '#skF_6', C_366, '#skF_8')) | k1_xboole_0=C_366 | k1_xboole_0=A_368)), inference(negUnitSimplification, [status(thm)], [c_34, c_30, c_30, c_602])).
% 3.92/1.63  tff(c_611, plain, (![E_50, A_15]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_607])).
% 3.92/1.63  tff(c_616, plain, (![E_369, A_370]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_369, A_370)='#skF_9' | E_369!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_369, A_370), '#skF_5') | ~m1_subset_1(E_369, k4_zfmisc_1(A_370, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_370)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_32, c_611])).
% 3.92/1.63  tff(c_620, plain, (![E_50]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_50, '#skF_5')='#skF_9' | E_50!='#skF_10' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_18, c_616])).
% 3.92/1.63  tff(c_625, plain, (![E_371]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_371, '#skF_5')='#skF_9' | E_371!='#skF_10' | ~m1_subset_1(E_371, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_36, c_620])).
% 3.92/1.63  tff(c_649, plain, ('#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_40, c_625])).
% 3.92/1.63  tff(c_10, plain, (![B_16, A_15, D_18, E_50, C_17]: (k4_mcart_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), '#skF_2'(C_17, D_18, B_16, E_50, A_15), '#skF_3'(C_17, D_18, B_16, E_50, A_15), '#skF_4'(C_17, D_18, B_16, E_50, A_15))=E_50 | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.63  tff(c_656, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_649, c_10])).
% 3.92/1.63  tff(c_667, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_656])).
% 3.92/1.63  tff(c_668, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_667])).
% 3.92/1.63  tff(c_22, plain, (![H_97, I_98, B_78, G_96, D_80, A_77, C_79, F_95]: (k10_mcart_1(A_77, B_78, C_79, D_80, k4_mcart_1(F_95, G_96, H_97, I_98))=H_97 | ~m1_subset_1(k4_mcart_1(F_95, G_96, H_97, I_98), k4_zfmisc_1(A_77, B_78, C_79, D_80)) | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.92/1.63  tff(c_734, plain, (![A_77, B_78, C_79, D_80]: (k10_mcart_1(A_77, B_78, C_79, D_80, k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')))='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_77, B_78, C_79, D_80)) | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77)), inference(superposition, [status(thm), theory('equality')], [c_668, c_22])).
% 3.92/1.63  tff(c_769, plain, (![A_381, B_382, C_383, D_384]: (k10_mcart_1(A_381, B_382, C_383, D_384, '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_381, B_382, C_383, D_384)) | k1_xboole_0=D_384 | k1_xboole_0=C_383 | k1_xboole_0=B_382 | k1_xboole_0=A_381)), inference(demodulation, [status(thm), theory('equality')], [c_668, c_734])).
% 3.92/1.63  tff(c_778, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_769])).
% 3.92/1.63  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_28, c_778])).
% 3.92/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.63  
% 3.92/1.63  Inference rules
% 3.92/1.63  ----------------------
% 3.92/1.63  #Ref     : 0
% 3.92/1.63  #Sup     : 179
% 3.92/1.63  #Fact    : 0
% 3.92/1.63  #Define  : 0
% 3.92/1.63  #Split   : 0
% 3.92/1.63  #Chain   : 0
% 3.92/1.63  #Close   : 0
% 3.92/1.63  
% 3.92/1.63  Ordering : KBO
% 3.92/1.63  
% 3.92/1.63  Simplification rules
% 3.92/1.63  ----------------------
% 3.92/1.63  #Subsume      : 18
% 3.92/1.63  #Demod        : 163
% 3.92/1.63  #Tautology    : 54
% 3.92/1.63  #SimpNegUnit  : 9
% 3.92/1.63  #BackRed      : 0
% 3.92/1.63  
% 3.92/1.63  #Partial instantiations: 0
% 3.92/1.63  #Strategies tried      : 1
% 3.92/1.63  
% 3.92/1.63  Timing (in seconds)
% 3.92/1.63  ----------------------
% 3.92/1.64  Preprocessing        : 0.35
% 3.92/1.64  Parsing              : 0.18
% 3.92/1.64  CNF conversion       : 0.04
% 3.92/1.64  Main loop            : 0.50
% 3.92/1.64  Inferencing          : 0.20
% 3.92/1.64  Reduction            : 0.16
% 3.92/1.64  Demodulation         : 0.12
% 3.92/1.64  BG Simplification    : 0.04
% 3.92/1.64  Subsumption          : 0.08
% 3.92/1.64  Abstraction          : 0.04
% 3.92/1.64  MUC search           : 0.00
% 3.92/1.64  Cooper               : 0.00
% 3.92/1.64  Total                : 0.90
% 3.92/1.64  Index Insertion      : 0.00
% 3.92/1.64  Index Deletion       : 0.00
% 3.92/1.64  Index Matching       : 0.00
% 3.92/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
