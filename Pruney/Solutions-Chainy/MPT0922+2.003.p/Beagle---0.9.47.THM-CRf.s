%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.49s
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

tff(f_120,negated_conjecture,(
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

tff(f_91,axiom,(
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

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

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
    ! [B_270,A_272,E_271,C_268,D_269] :
      ( k4_mcart_1('#skF_1'(C_268,D_269,B_270,E_271,A_272),'#skF_2'(C_268,D_269,B_270,E_271,A_272),'#skF_3'(C_268,D_269,B_270,E_271,A_272),'#skF_4'(C_268,D_269,B_270,E_271,A_272)) = E_271
      | ~ m1_subset_1(E_271,k4_zfmisc_1(A_272,B_270,C_268,D_269))
      | k1_xboole_0 = D_269
      | k1_xboole_0 = C_268
      | k1_xboole_0 = B_270
      | k1_xboole_0 = A_272 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [J_119,G_105,H_113,I_117] :
      ( J_119 = '#skF_9'
      | k4_mcart_1(G_105,H_113,I_117,J_119) != '#skF_10'
      | ~ m1_subset_1(J_119,'#skF_8')
      | ~ m1_subset_1(I_117,'#skF_7')
      | ~ m1_subset_1(H_113,'#skF_6')
      | ~ m1_subset_1(G_105,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_535,plain,(
    ! [C_323,A_319,D_322,B_320,E_321] :
      ( '#skF_4'(C_323,D_322,B_320,E_321,A_319) = '#skF_9'
      | E_321 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_323,D_322,B_320,E_321,A_319),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_323,D_322,B_320,E_321,A_319),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_323,D_322,B_320,E_321,A_319),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_323,D_322,B_320,E_321,A_319),'#skF_5')
      | ~ m1_subset_1(E_321,k4_zfmisc_1(A_319,B_320,C_323,D_322))
      | k1_xboole_0 = D_322
      | k1_xboole_0 = C_323
      | k1_xboole_0 = B_320
      | k1_xboole_0 = A_319 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_38])).

tff(c_539,plain,(
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
    inference(resolution,[status(thm)],[c_16,c_535])).

tff(c_598,plain,(
    ! [C_353,D_354,E_355,A_356] :
      ( '#skF_4'(C_353,D_354,'#skF_6',E_355,A_356) = '#skF_9'
      | E_355 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_353,D_354,'#skF_6',E_355,A_356),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_353,D_354,'#skF_6',E_355,A_356),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_353,D_354,'#skF_6',E_355,A_356),'#skF_5')
      | ~ m1_subset_1(E_355,k4_zfmisc_1(A_356,'#skF_6',C_353,D_354))
      | k1_xboole_0 = D_354
      | k1_xboole_0 = C_353
      | k1_xboole_0 = A_356 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_539])).

tff(c_602,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_598])).

tff(c_607,plain,(
    ! [C_357,E_358,A_359] :
      ( '#skF_4'(C_357,'#skF_8','#skF_6',E_358,A_359) = '#skF_9'
      | E_358 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_357,'#skF_8','#skF_6',E_358,A_359),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_357,'#skF_8','#skF_6',E_358,A_359),'#skF_5')
      | ~ m1_subset_1(E_358,k4_zfmisc_1(A_359,'#skF_6',C_357,'#skF_8'))
      | k1_xboole_0 = C_357
      | k1_xboole_0 = A_359 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_30,c_30,c_602])).

tff(c_611,plain,(
    ! [E_50,A_15] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_14,c_607])).

tff(c_616,plain,(
    ! [E_360,A_361] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_360,A_361) = '#skF_9'
      | E_360 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_360,A_361),'#skF_5')
      | ~ m1_subset_1(E_360,k4_zfmisc_1(A_361,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_361 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_32,c_611])).

tff(c_620,plain,(
    ! [E_50] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_50,'#skF_5') = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_616])).

tff(c_625,plain,(
    ! [E_362] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_362,'#skF_5') = '#skF_9'
      | E_362 != '#skF_10'
      | ~ m1_subset_1(E_362,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_36,c_620])).

tff(c_649,plain,(
    '#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') = '#skF_9' ),
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
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_10])).

tff(c_667,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_656])).

tff(c_668,plain,(
    k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_667])).

tff(c_20,plain,(
    ! [G_87,B_78,D_80,A_77,C_79,F_86,I_89,H_88] :
      ( k11_mcart_1(A_77,B_78,C_79,D_80,k4_mcart_1(F_86,G_87,H_88,I_89)) = I_89
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77
      | ~ m1_subset_1(k4_mcart_1(F_86,G_87,H_88,I_89),k4_zfmisc_1(A_77,B_78,C_79,D_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_731,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k11_mcart_1(A_77,B_78,C_79,D_80,k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9')) = '#skF_9'
      | k1_xboole_0 = D_80
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_77,B_78,C_79,D_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_20])).

tff(c_769,plain,(
    ! [A_372,B_373,C_374,D_375] :
      ( k11_mcart_1(A_372,B_373,C_374,D_375,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_375
      | k1_xboole_0 = C_374
      | k1_xboole_0 = B_373
      | k1_xboole_0 = A_372
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_372,B_373,C_374,D_375)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_731])).

tff(c_778,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.53  
% 3.15/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.53  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.15/1.53  
% 3.15/1.53  %Foreground sorts:
% 3.15/1.53  
% 3.15/1.53  
% 3.15/1.53  %Background operators:
% 3.15/1.53  
% 3.15/1.53  
% 3.15/1.53  %Foreground operators:
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.53  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.15/1.53  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.53  tff('#skF_10', type, '#skF_10': $i).
% 3.15/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.53  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.15/1.53  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.15/1.53  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.53  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.15/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.53  
% 3.49/1.54  tff(f_120, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_mcart_1)).
% 3.49/1.54  tff(f_64, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.49/1.54  tff(f_91, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 3.49/1.54  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_34, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_32, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_30, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_28, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_40, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_18, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), A_15) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.54  tff(c_14, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_3'(C_17, D_18, B_16, E_50, A_15), C_17) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.54  tff(c_12, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_4'(C_17, D_18, B_16, E_50, A_15), D_18) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.54  tff(c_16, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_2'(C_17, D_18, B_16, E_50, A_15), B_16) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.54  tff(c_400, plain, (![B_270, A_272, E_271, C_268, D_269]: (k4_mcart_1('#skF_1'(C_268, D_269, B_270, E_271, A_272), '#skF_2'(C_268, D_269, B_270, E_271, A_272), '#skF_3'(C_268, D_269, B_270, E_271, A_272), '#skF_4'(C_268, D_269, B_270, E_271, A_272))=E_271 | ~m1_subset_1(E_271, k4_zfmisc_1(A_272, B_270, C_268, D_269)) | k1_xboole_0=D_269 | k1_xboole_0=C_268 | k1_xboole_0=B_270 | k1_xboole_0=A_272)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.54  tff(c_38, plain, (![J_119, G_105, H_113, I_117]: (J_119='#skF_9' | k4_mcart_1(G_105, H_113, I_117, J_119)!='#skF_10' | ~m1_subset_1(J_119, '#skF_8') | ~m1_subset_1(I_117, '#skF_7') | ~m1_subset_1(H_113, '#skF_6') | ~m1_subset_1(G_105, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.49/1.54  tff(c_535, plain, (![C_323, A_319, D_322, B_320, E_321]: ('#skF_4'(C_323, D_322, B_320, E_321, A_319)='#skF_9' | E_321!='#skF_10' | ~m1_subset_1('#skF_4'(C_323, D_322, B_320, E_321, A_319), '#skF_8') | ~m1_subset_1('#skF_3'(C_323, D_322, B_320, E_321, A_319), '#skF_7') | ~m1_subset_1('#skF_2'(C_323, D_322, B_320, E_321, A_319), '#skF_6') | ~m1_subset_1('#skF_1'(C_323, D_322, B_320, E_321, A_319), '#skF_5') | ~m1_subset_1(E_321, k4_zfmisc_1(A_319, B_320, C_323, D_322)) | k1_xboole_0=D_322 | k1_xboole_0=C_323 | k1_xboole_0=B_320 | k1_xboole_0=A_319)), inference(superposition, [status(thm), theory('equality')], [c_400, c_38])).
% 3.49/1.54  tff(c_539, plain, (![C_17, D_18, E_50, A_15]: ('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_8') | ~m1_subset_1('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_16, c_535])).
% 3.49/1.54  tff(c_598, plain, (![C_353, D_354, E_355, A_356]: ('#skF_4'(C_353, D_354, '#skF_6', E_355, A_356)='#skF_9' | E_355!='#skF_10' | ~m1_subset_1('#skF_4'(C_353, D_354, '#skF_6', E_355, A_356), '#skF_8') | ~m1_subset_1('#skF_3'(C_353, D_354, '#skF_6', E_355, A_356), '#skF_7') | ~m1_subset_1('#skF_1'(C_353, D_354, '#skF_6', E_355, A_356), '#skF_5') | ~m1_subset_1(E_355, k4_zfmisc_1(A_356, '#skF_6', C_353, D_354)) | k1_xboole_0=D_354 | k1_xboole_0=C_353 | k1_xboole_0=A_356)), inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_539])).
% 3.49/1.54  tff(c_602, plain, (![C_17, E_50, A_15]: ('#skF_4'(C_17, '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_598])).
% 3.49/1.54  tff(c_607, plain, (![C_357, E_358, A_359]: ('#skF_4'(C_357, '#skF_8', '#skF_6', E_358, A_359)='#skF_9' | E_358!='#skF_10' | ~m1_subset_1('#skF_3'(C_357, '#skF_8', '#skF_6', E_358, A_359), '#skF_7') | ~m1_subset_1('#skF_1'(C_357, '#skF_8', '#skF_6', E_358, A_359), '#skF_5') | ~m1_subset_1(E_358, k4_zfmisc_1(A_359, '#skF_6', C_357, '#skF_8')) | k1_xboole_0=C_357 | k1_xboole_0=A_359)), inference(negUnitSimplification, [status(thm)], [c_34, c_30, c_30, c_602])).
% 3.49/1.54  tff(c_611, plain, (![E_50, A_15]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_607])).
% 3.49/1.54  tff(c_616, plain, (![E_360, A_361]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_360, A_361)='#skF_9' | E_360!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_360, A_361), '#skF_5') | ~m1_subset_1(E_360, k4_zfmisc_1(A_361, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_361)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_32, c_611])).
% 3.49/1.54  tff(c_620, plain, (![E_50]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_50, '#skF_5')='#skF_9' | E_50!='#skF_10' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_18, c_616])).
% 3.49/1.54  tff(c_625, plain, (![E_362]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_362, '#skF_5')='#skF_9' | E_362!='#skF_10' | ~m1_subset_1(E_362, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_36, c_620])).
% 3.49/1.54  tff(c_649, plain, ('#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_40, c_625])).
% 3.49/1.54  tff(c_10, plain, (![B_16, A_15, D_18, E_50, C_17]: (k4_mcart_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), '#skF_2'(C_17, D_18, B_16, E_50, A_15), '#skF_3'(C_17, D_18, B_16, E_50, A_15), '#skF_4'(C_17, D_18, B_16, E_50, A_15))=E_50 | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.54  tff(c_656, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_649, c_10])).
% 3.49/1.54  tff(c_667, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_656])).
% 3.49/1.54  tff(c_668, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_667])).
% 3.49/1.54  tff(c_20, plain, (![G_87, B_78, D_80, A_77, C_79, F_86, I_89, H_88]: (k11_mcart_1(A_77, B_78, C_79, D_80, k4_mcart_1(F_86, G_87, H_88, I_89))=I_89 | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77 | ~m1_subset_1(k4_mcart_1(F_86, G_87, H_88, I_89), k4_zfmisc_1(A_77, B_78, C_79, D_80)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.49/1.54  tff(c_731, plain, (![A_77, B_78, C_79, D_80]: (k11_mcart_1(A_77, B_78, C_79, D_80, k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9'))='#skF_9' | k1_xboole_0=D_80 | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_77, B_78, C_79, D_80)))), inference(superposition, [status(thm), theory('equality')], [c_668, c_20])).
% 3.49/1.54  tff(c_769, plain, (![A_372, B_373, C_374, D_375]: (k11_mcart_1(A_372, B_373, C_374, D_375, '#skF_10')='#skF_9' | k1_xboole_0=D_375 | k1_xboole_0=C_374 | k1_xboole_0=B_373 | k1_xboole_0=A_372 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_372, B_373, C_374, D_375)))), inference(demodulation, [status(thm), theory('equality')], [c_668, c_731])).
% 3.49/1.54  tff(c_778, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_769])).
% 3.49/1.54  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_28, c_778])).
% 3.49/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.54  
% 3.49/1.54  Inference rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Ref     : 0
% 3.49/1.54  #Sup     : 179
% 3.49/1.54  #Fact    : 0
% 3.49/1.54  #Define  : 0
% 3.49/1.54  #Split   : 0
% 3.49/1.54  #Chain   : 0
% 3.49/1.54  #Close   : 0
% 3.49/1.54  
% 3.49/1.54  Ordering : KBO
% 3.49/1.54  
% 3.49/1.54  Simplification rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Subsume      : 18
% 3.49/1.54  #Demod        : 163
% 3.49/1.54  #Tautology    : 54
% 3.49/1.54  #SimpNegUnit  : 9
% 3.49/1.54  #BackRed      : 0
% 3.49/1.54  
% 3.49/1.54  #Partial instantiations: 0
% 3.49/1.54  #Strategies tried      : 1
% 3.49/1.54  
% 3.49/1.54  Timing (in seconds)
% 3.49/1.54  ----------------------
% 3.49/1.55  Preprocessing        : 0.33
% 3.49/1.55  Parsing              : 0.17
% 3.49/1.55  CNF conversion       : 0.03
% 3.49/1.55  Main loop            : 0.45
% 3.49/1.55  Inferencing          : 0.18
% 3.49/1.55  Reduction            : 0.14
% 3.49/1.55  Demodulation         : 0.10
% 3.49/1.55  BG Simplification    : 0.03
% 3.49/1.55  Subsumption          : 0.07
% 3.49/1.55  Abstraction          : 0.04
% 3.49/1.55  MUC search           : 0.00
% 3.49/1.55  Cooper               : 0.00
% 3.49/1.55  Total                : 0.81
% 3.49/1.55  Index Insertion      : 0.00
% 3.49/1.55  Index Deletion       : 0.00
% 3.49/1.55  Index Matching       : 0.00
% 3.49/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
