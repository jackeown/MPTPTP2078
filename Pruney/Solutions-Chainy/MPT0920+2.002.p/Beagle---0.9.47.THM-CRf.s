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
% DateTime   : Thu Dec  3 10:10:16 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 181 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 (1034 expanded)
%              Number of equality atoms :  133 ( 637 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_6 > #skF_5 > #skF_10 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_9 > #skF_3 > #skF_12 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_95,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    k9_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_22,plain,(
    ! [C_92,E_125,B_91,D_93,A_90] :
      ( m1_subset_1('#skF_7'(B_91,D_93,E_125,C_92,A_90),C_92)
      | ~ m1_subset_1(E_125,k4_zfmisc_1(A_90,B_91,C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [C_92,E_125,B_91,D_93,A_90] :
      ( m1_subset_1('#skF_8'(B_91,D_93,E_125,C_92,A_90),D_93)
      | ~ m1_subset_1(E_125,k4_zfmisc_1(A_90,B_91,C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [C_92,E_125,B_91,D_93,A_90] :
      ( m1_subset_1('#skF_5'(B_91,D_93,E_125,C_92,A_90),A_90)
      | ~ m1_subset_1(E_125,k4_zfmisc_1(A_90,B_91,C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    ! [C_92,E_125,B_91,D_93,A_90] :
      ( m1_subset_1('#skF_6'(B_91,D_93,E_125,C_92,A_90),B_91)
      | ~ m1_subset_1(E_125,k4_zfmisc_1(A_90,B_91,C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_297,plain,(
    ! [C_285,D_283,A_286,E_284,B_282] :
      ( k4_mcart_1('#skF_5'(B_282,D_283,E_284,C_285,A_286),'#skF_6'(B_282,D_283,E_284,C_285,A_286),'#skF_7'(B_282,D_283,E_284,C_285,A_286),'#skF_8'(B_282,D_283,E_284,C_285,A_286)) = E_284
      | ~ m1_subset_1(E_284,k4_zfmisc_1(A_286,B_282,C_285,D_283))
      | k1_xboole_0 = D_283
      | k1_xboole_0 = C_285
      | k1_xboole_0 = B_282
      | k1_xboole_0 = A_286 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    ! [H_175,G_167,I_179,J_181] :
      ( H_175 = '#skF_13'
      | k4_mcart_1(G_167,H_175,I_179,J_181) != '#skF_14'
      | ~ m1_subset_1(J_181,'#skF_12')
      | ~ m1_subset_1(I_179,'#skF_11')
      | ~ m1_subset_1(H_175,'#skF_10')
      | ~ m1_subset_1(G_167,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_384,plain,(
    ! [A_326,E_323,B_322,C_324,D_325] :
      ( '#skF_6'(B_322,D_325,E_323,C_324,A_326) = '#skF_13'
      | E_323 != '#skF_14'
      | ~ m1_subset_1('#skF_8'(B_322,D_325,E_323,C_324,A_326),'#skF_12')
      | ~ m1_subset_1('#skF_7'(B_322,D_325,E_323,C_324,A_326),'#skF_11')
      | ~ m1_subset_1('#skF_6'(B_322,D_325,E_323,C_324,A_326),'#skF_10')
      | ~ m1_subset_1('#skF_5'(B_322,D_325,E_323,C_324,A_326),'#skF_9')
      | ~ m1_subset_1(E_323,k4_zfmisc_1(A_326,B_322,C_324,D_325))
      | k1_xboole_0 = D_325
      | k1_xboole_0 = C_324
      | k1_xboole_0 = B_322
      | k1_xboole_0 = A_326 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_38])).

tff(c_388,plain,(
    ! [D_93,E_125,C_92,A_90] :
      ( '#skF_6'('#skF_10',D_93,E_125,C_92,A_90) = '#skF_13'
      | E_125 != '#skF_14'
      | ~ m1_subset_1('#skF_8'('#skF_10',D_93,E_125,C_92,A_90),'#skF_12')
      | ~ m1_subset_1('#skF_7'('#skF_10',D_93,E_125,C_92,A_90),'#skF_11')
      | ~ m1_subset_1('#skF_5'('#skF_10',D_93,E_125,C_92,A_90),'#skF_9')
      | ~ m1_subset_1(E_125,k4_zfmisc_1(A_90,'#skF_10',C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = A_90 ) ),
    inference(resolution,[status(thm)],[c_24,c_384])).

tff(c_518,plain,(
    ! [D_373,E_374,C_375,A_376] :
      ( '#skF_6'('#skF_10',D_373,E_374,C_375,A_376) = '#skF_13'
      | E_374 != '#skF_14'
      | ~ m1_subset_1('#skF_8'('#skF_10',D_373,E_374,C_375,A_376),'#skF_12')
      | ~ m1_subset_1('#skF_7'('#skF_10',D_373,E_374,C_375,A_376),'#skF_11')
      | ~ m1_subset_1('#skF_5'('#skF_10',D_373,E_374,C_375,A_376),'#skF_9')
      | ~ m1_subset_1(E_374,k4_zfmisc_1(A_376,'#skF_10',C_375,D_373))
      | k1_xboole_0 = D_373
      | k1_xboole_0 = C_375
      | k1_xboole_0 = A_376 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_388])).

tff(c_522,plain,(
    ! [D_93,E_125,C_92] :
      ( '#skF_6'('#skF_10',D_93,E_125,C_92,'#skF_9') = '#skF_13'
      | E_125 != '#skF_14'
      | ~ m1_subset_1('#skF_8'('#skF_10',D_93,E_125,C_92,'#skF_9'),'#skF_12')
      | ~ m1_subset_1('#skF_7'('#skF_10',D_93,E_125,C_92,'#skF_9'),'#skF_11')
      | ~ m1_subset_1(E_125,k4_zfmisc_1('#skF_9','#skF_10',C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_26,c_518])).

tff(c_527,plain,(
    ! [D_377,E_378,C_379] :
      ( '#skF_6'('#skF_10',D_377,E_378,C_379,'#skF_9') = '#skF_13'
      | E_378 != '#skF_14'
      | ~ m1_subset_1('#skF_8'('#skF_10',D_377,E_378,C_379,'#skF_9'),'#skF_12')
      | ~ m1_subset_1('#skF_7'('#skF_10',D_377,E_378,C_379,'#skF_9'),'#skF_11')
      | ~ m1_subset_1(E_378,k4_zfmisc_1('#skF_9','#skF_10',C_379,D_377))
      | k1_xboole_0 = D_377
      | k1_xboole_0 = C_379 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_36,c_522])).

tff(c_531,plain,(
    ! [E_125,C_92] :
      ( '#skF_6'('#skF_10','#skF_12',E_125,C_92,'#skF_9') = '#skF_13'
      | E_125 != '#skF_14'
      | ~ m1_subset_1('#skF_7'('#skF_10','#skF_12',E_125,C_92,'#skF_9'),'#skF_11')
      | ~ m1_subset_1(E_125,k4_zfmisc_1('#skF_9','#skF_10',C_92,'#skF_12'))
      | k1_xboole_0 = '#skF_12'
      | k1_xboole_0 = C_92
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_20,c_527])).

tff(c_536,plain,(
    ! [E_380,C_381] :
      ( '#skF_6'('#skF_10','#skF_12',E_380,C_381,'#skF_9') = '#skF_13'
      | E_380 != '#skF_14'
      | ~ m1_subset_1('#skF_7'('#skF_10','#skF_12',E_380,C_381,'#skF_9'),'#skF_11')
      | ~ m1_subset_1(E_380,k4_zfmisc_1('#skF_9','#skF_10',C_381,'#skF_12'))
      | k1_xboole_0 = C_381 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_30,c_30,c_531])).

tff(c_540,plain,(
    ! [E_125] :
      ( '#skF_6'('#skF_10','#skF_12',E_125,'#skF_11','#skF_9') = '#skF_13'
      | E_125 != '#skF_14'
      | ~ m1_subset_1(E_125,k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
      | k1_xboole_0 = '#skF_12'
      | k1_xboole_0 = '#skF_11'
      | k1_xboole_0 = '#skF_10'
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_22,c_536])).

tff(c_545,plain,(
    ! [E_382] :
      ( '#skF_6'('#skF_10','#skF_12',E_382,'#skF_11','#skF_9') = '#skF_13'
      | E_382 != '#skF_14'
      | ~ m1_subset_1(E_382,k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_32,c_540])).

tff(c_574,plain,(
    '#skF_6'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_40,c_545])).

tff(c_18,plain,(
    ! [C_92,E_125,B_91,D_93,A_90] :
      ( k4_mcart_1('#skF_5'(B_91,D_93,E_125,C_92,A_90),'#skF_6'(B_91,D_93,E_125,C_92,A_90),'#skF_7'(B_91,D_93,E_125,C_92,A_90),'#skF_8'(B_91,D_93,E_125,C_92,A_90)) = E_125
      | ~ m1_subset_1(E_125,k4_zfmisc_1(A_90,B_91,C_92,D_93))
      | k1_xboole_0 = D_93
      | k1_xboole_0 = C_92
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_581,plain,
    ( k4_mcart_1('#skF_5'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_13','#skF_7'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_8'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9')) = '#skF_14'
    | ~ m1_subset_1('#skF_14',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_18])).

tff(c_592,plain,
    ( k4_mcart_1('#skF_5'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_13','#skF_7'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_8'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9')) = '#skF_14'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_581])).

tff(c_593,plain,(
    k4_mcart_1('#skF_5'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_13','#skF_7'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_8'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9')) = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_592])).

tff(c_16,plain,(
    ! [A_85,D_88,C_87,E_89,B_86] :
      ( m1_subset_1(k9_mcart_1(A_85,B_86,C_87,D_88,E_89),B_86)
      | ~ m1_subset_1(E_89,k4_zfmisc_1(A_85,B_86,C_87,D_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_312,plain,(
    ! [I_294,A_293,G_289,B_291,D_288,H_290,C_287,J_292] :
      ( k9_mcart_1(A_293,B_291,C_287,D_288,k4_mcart_1(G_289,H_290,I_294,J_292)) = H_290
      | ~ m1_subset_1(k9_mcart_1(A_293,B_291,C_287,D_288,k4_mcart_1(G_289,H_290,I_294,J_292)),B_291)
      | ~ m1_subset_1(k4_mcart_1(G_289,H_290,I_294,J_292),k4_zfmisc_1(A_293,B_291,C_287,D_288))
      | k1_xboole_0 = D_288
      | k1_xboole_0 = C_287
      | k1_xboole_0 = B_291
      | k1_xboole_0 = A_293 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_328,plain,(
    ! [A_85,D_88,I_294,G_289,C_87,H_290,B_86,J_292] :
      ( k9_mcart_1(A_85,B_86,C_87,D_88,k4_mcart_1(G_289,H_290,I_294,J_292)) = H_290
      | k1_xboole_0 = D_88
      | k1_xboole_0 = C_87
      | k1_xboole_0 = B_86
      | k1_xboole_0 = A_85
      | ~ m1_subset_1(k4_mcart_1(G_289,H_290,I_294,J_292),k4_zfmisc_1(A_85,B_86,C_87,D_88)) ) ),
    inference(resolution,[status(thm)],[c_16,c_312])).

tff(c_621,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k9_mcart_1(A_85,B_86,C_87,D_88,k4_mcart_1('#skF_5'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_13','#skF_7'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'),'#skF_8'('#skF_10','#skF_12','#skF_14','#skF_11','#skF_9'))) = '#skF_13'
      | k1_xboole_0 = D_88
      | k1_xboole_0 = C_87
      | k1_xboole_0 = B_86
      | k1_xboole_0 = A_85
      | ~ m1_subset_1('#skF_14',k4_zfmisc_1(A_85,B_86,C_87,D_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_328])).

tff(c_642,plain,(
    ! [A_389,B_390,C_391,D_392] :
      ( k9_mcart_1(A_389,B_390,C_391,D_392,'#skF_14') = '#skF_13'
      | k1_xboole_0 = D_392
      | k1_xboole_0 = C_391
      | k1_xboole_0 = B_390
      | k1_xboole_0 = A_389
      | ~ m1_subset_1('#skF_14',k4_zfmisc_1(A_389,B_390,C_391,D_392)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_621])).

tff(c_651,plain,
    ( k9_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12','#skF_14') = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_642])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_30,c_28,c_651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:33:46 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.56  
% 3.37/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.56  %$ m1_subset_1 > k9_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_6 > #skF_5 > #skF_10 > #skF_8 > #skF_14 > #skF_7 > #skF_13 > #skF_9 > #skF_3 > #skF_12 > #skF_4
% 3.37/1.56  
% 3.37/1.56  %Foreground sorts:
% 3.37/1.56  
% 3.37/1.56  
% 3.37/1.56  %Background operators:
% 3.37/1.56  
% 3.37/1.56  
% 3.37/1.56  %Foreground operators:
% 3.37/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.37/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.37/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.37/1.56  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.37/1.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_14', type, '#skF_14': $i).
% 3.37/1.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_13', type, '#skF_13': $i).
% 3.37/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.37/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.56  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.37/1.56  tff('#skF_12', type, '#skF_12': $i).
% 3.37/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.56  
% 3.37/1.57  tff(f_124, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 3.37/1.57  tff(f_95, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.37/1.57  tff(f_64, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 3.37/1.57  tff(f_60, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, B) => ((F = k9_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = H)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_mcart_1)).
% 3.37/1.57  tff(c_36, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_34, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_32, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_30, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_28, plain, (k9_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_40, plain, (m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_22, plain, (![C_92, E_125, B_91, D_93, A_90]: (m1_subset_1('#skF_7'(B_91, D_93, E_125, C_92, A_90), C_92) | ~m1_subset_1(E_125, k4_zfmisc_1(A_90, B_91, C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0=B_91 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.57  tff(c_20, plain, (![C_92, E_125, B_91, D_93, A_90]: (m1_subset_1('#skF_8'(B_91, D_93, E_125, C_92, A_90), D_93) | ~m1_subset_1(E_125, k4_zfmisc_1(A_90, B_91, C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0=B_91 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.57  tff(c_26, plain, (![C_92, E_125, B_91, D_93, A_90]: (m1_subset_1('#skF_5'(B_91, D_93, E_125, C_92, A_90), A_90) | ~m1_subset_1(E_125, k4_zfmisc_1(A_90, B_91, C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0=B_91 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.57  tff(c_24, plain, (![C_92, E_125, B_91, D_93, A_90]: (m1_subset_1('#skF_6'(B_91, D_93, E_125, C_92, A_90), B_91) | ~m1_subset_1(E_125, k4_zfmisc_1(A_90, B_91, C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0=B_91 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.57  tff(c_297, plain, (![C_285, D_283, A_286, E_284, B_282]: (k4_mcart_1('#skF_5'(B_282, D_283, E_284, C_285, A_286), '#skF_6'(B_282, D_283, E_284, C_285, A_286), '#skF_7'(B_282, D_283, E_284, C_285, A_286), '#skF_8'(B_282, D_283, E_284, C_285, A_286))=E_284 | ~m1_subset_1(E_284, k4_zfmisc_1(A_286, B_282, C_285, D_283)) | k1_xboole_0=D_283 | k1_xboole_0=C_285 | k1_xboole_0=B_282 | k1_xboole_0=A_286)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.57  tff(c_38, plain, (![H_175, G_167, I_179, J_181]: (H_175='#skF_13' | k4_mcart_1(G_167, H_175, I_179, J_181)!='#skF_14' | ~m1_subset_1(J_181, '#skF_12') | ~m1_subset_1(I_179, '#skF_11') | ~m1_subset_1(H_175, '#skF_10') | ~m1_subset_1(G_167, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.37/1.57  tff(c_384, plain, (![A_326, E_323, B_322, C_324, D_325]: ('#skF_6'(B_322, D_325, E_323, C_324, A_326)='#skF_13' | E_323!='#skF_14' | ~m1_subset_1('#skF_8'(B_322, D_325, E_323, C_324, A_326), '#skF_12') | ~m1_subset_1('#skF_7'(B_322, D_325, E_323, C_324, A_326), '#skF_11') | ~m1_subset_1('#skF_6'(B_322, D_325, E_323, C_324, A_326), '#skF_10') | ~m1_subset_1('#skF_5'(B_322, D_325, E_323, C_324, A_326), '#skF_9') | ~m1_subset_1(E_323, k4_zfmisc_1(A_326, B_322, C_324, D_325)) | k1_xboole_0=D_325 | k1_xboole_0=C_324 | k1_xboole_0=B_322 | k1_xboole_0=A_326)), inference(superposition, [status(thm), theory('equality')], [c_297, c_38])).
% 3.37/1.57  tff(c_388, plain, (![D_93, E_125, C_92, A_90]: ('#skF_6'('#skF_10', D_93, E_125, C_92, A_90)='#skF_13' | E_125!='#skF_14' | ~m1_subset_1('#skF_8'('#skF_10', D_93, E_125, C_92, A_90), '#skF_12') | ~m1_subset_1('#skF_7'('#skF_10', D_93, E_125, C_92, A_90), '#skF_11') | ~m1_subset_1('#skF_5'('#skF_10', D_93, E_125, C_92, A_90), '#skF_9') | ~m1_subset_1(E_125, k4_zfmisc_1(A_90, '#skF_10', C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0='#skF_10' | k1_xboole_0=A_90)), inference(resolution, [status(thm)], [c_24, c_384])).
% 3.37/1.57  tff(c_518, plain, (![D_373, E_374, C_375, A_376]: ('#skF_6'('#skF_10', D_373, E_374, C_375, A_376)='#skF_13' | E_374!='#skF_14' | ~m1_subset_1('#skF_8'('#skF_10', D_373, E_374, C_375, A_376), '#skF_12') | ~m1_subset_1('#skF_7'('#skF_10', D_373, E_374, C_375, A_376), '#skF_11') | ~m1_subset_1('#skF_5'('#skF_10', D_373, E_374, C_375, A_376), '#skF_9') | ~m1_subset_1(E_374, k4_zfmisc_1(A_376, '#skF_10', C_375, D_373)) | k1_xboole_0=D_373 | k1_xboole_0=C_375 | k1_xboole_0=A_376)), inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_388])).
% 3.37/1.57  tff(c_522, plain, (![D_93, E_125, C_92]: ('#skF_6'('#skF_10', D_93, E_125, C_92, '#skF_9')='#skF_13' | E_125!='#skF_14' | ~m1_subset_1('#skF_8'('#skF_10', D_93, E_125, C_92, '#skF_9'), '#skF_12') | ~m1_subset_1('#skF_7'('#skF_10', D_93, E_125, C_92, '#skF_9'), '#skF_11') | ~m1_subset_1(E_125, k4_zfmisc_1('#skF_9', '#skF_10', C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_26, c_518])).
% 3.37/1.57  tff(c_527, plain, (![D_377, E_378, C_379]: ('#skF_6'('#skF_10', D_377, E_378, C_379, '#skF_9')='#skF_13' | E_378!='#skF_14' | ~m1_subset_1('#skF_8'('#skF_10', D_377, E_378, C_379, '#skF_9'), '#skF_12') | ~m1_subset_1('#skF_7'('#skF_10', D_377, E_378, C_379, '#skF_9'), '#skF_11') | ~m1_subset_1(E_378, k4_zfmisc_1('#skF_9', '#skF_10', C_379, D_377)) | k1_xboole_0=D_377 | k1_xboole_0=C_379)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_36, c_522])).
% 3.37/1.57  tff(c_531, plain, (![E_125, C_92]: ('#skF_6'('#skF_10', '#skF_12', E_125, C_92, '#skF_9')='#skF_13' | E_125!='#skF_14' | ~m1_subset_1('#skF_7'('#skF_10', '#skF_12', E_125, C_92, '#skF_9'), '#skF_11') | ~m1_subset_1(E_125, k4_zfmisc_1('#skF_9', '#skF_10', C_92, '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0=C_92 | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_20, c_527])).
% 3.37/1.57  tff(c_536, plain, (![E_380, C_381]: ('#skF_6'('#skF_10', '#skF_12', E_380, C_381, '#skF_9')='#skF_13' | E_380!='#skF_14' | ~m1_subset_1('#skF_7'('#skF_10', '#skF_12', E_380, C_381, '#skF_9'), '#skF_11') | ~m1_subset_1(E_380, k4_zfmisc_1('#skF_9', '#skF_10', C_381, '#skF_12')) | k1_xboole_0=C_381)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_30, c_30, c_531])).
% 3.37/1.57  tff(c_540, plain, (![E_125]: ('#skF_6'('#skF_10', '#skF_12', E_125, '#skF_11', '#skF_9')='#skF_13' | E_125!='#skF_14' | ~m1_subset_1(E_125, k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_22, c_536])).
% 3.37/1.57  tff(c_545, plain, (![E_382]: ('#skF_6'('#skF_10', '#skF_12', E_382, '#skF_11', '#skF_9')='#skF_13' | E_382!='#skF_14' | ~m1_subset_1(E_382, k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_32, c_540])).
% 3.37/1.57  tff(c_574, plain, ('#skF_6'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9')='#skF_13'), inference(resolution, [status(thm)], [c_40, c_545])).
% 3.37/1.57  tff(c_18, plain, (![C_92, E_125, B_91, D_93, A_90]: (k4_mcart_1('#skF_5'(B_91, D_93, E_125, C_92, A_90), '#skF_6'(B_91, D_93, E_125, C_92, A_90), '#skF_7'(B_91, D_93, E_125, C_92, A_90), '#skF_8'(B_91, D_93, E_125, C_92, A_90))=E_125 | ~m1_subset_1(E_125, k4_zfmisc_1(A_90, B_91, C_92, D_93)) | k1_xboole_0=D_93 | k1_xboole_0=C_92 | k1_xboole_0=B_91 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.57  tff(c_581, plain, (k4_mcart_1('#skF_5'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_13', '#skF_7'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_8'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'))='#skF_14' | ~m1_subset_1('#skF_14', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_574, c_18])).
% 3.37/1.57  tff(c_592, plain, (k4_mcart_1('#skF_5'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_13', '#skF_7'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_8'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'))='#skF_14' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_581])).
% 3.37/1.57  tff(c_593, plain, (k4_mcart_1('#skF_5'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_13', '#skF_7'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_8'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'))='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_592])).
% 3.37/1.57  tff(c_16, plain, (![A_85, D_88, C_87, E_89, B_86]: (m1_subset_1(k9_mcart_1(A_85, B_86, C_87, D_88, E_89), B_86) | ~m1_subset_1(E_89, k4_zfmisc_1(A_85, B_86, C_87, D_88)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.57  tff(c_312, plain, (![I_294, A_293, G_289, B_291, D_288, H_290, C_287, J_292]: (k9_mcart_1(A_293, B_291, C_287, D_288, k4_mcart_1(G_289, H_290, I_294, J_292))=H_290 | ~m1_subset_1(k9_mcart_1(A_293, B_291, C_287, D_288, k4_mcart_1(G_289, H_290, I_294, J_292)), B_291) | ~m1_subset_1(k4_mcart_1(G_289, H_290, I_294, J_292), k4_zfmisc_1(A_293, B_291, C_287, D_288)) | k1_xboole_0=D_288 | k1_xboole_0=C_287 | k1_xboole_0=B_291 | k1_xboole_0=A_293)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.57  tff(c_328, plain, (![A_85, D_88, I_294, G_289, C_87, H_290, B_86, J_292]: (k9_mcart_1(A_85, B_86, C_87, D_88, k4_mcart_1(G_289, H_290, I_294, J_292))=H_290 | k1_xboole_0=D_88 | k1_xboole_0=C_87 | k1_xboole_0=B_86 | k1_xboole_0=A_85 | ~m1_subset_1(k4_mcart_1(G_289, H_290, I_294, J_292), k4_zfmisc_1(A_85, B_86, C_87, D_88)))), inference(resolution, [status(thm)], [c_16, c_312])).
% 3.37/1.57  tff(c_621, plain, (![A_85, B_86, C_87, D_88]: (k9_mcart_1(A_85, B_86, C_87, D_88, k4_mcart_1('#skF_5'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_13', '#skF_7'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9'), '#skF_8'('#skF_10', '#skF_12', '#skF_14', '#skF_11', '#skF_9')))='#skF_13' | k1_xboole_0=D_88 | k1_xboole_0=C_87 | k1_xboole_0=B_86 | k1_xboole_0=A_85 | ~m1_subset_1('#skF_14', k4_zfmisc_1(A_85, B_86, C_87, D_88)))), inference(superposition, [status(thm), theory('equality')], [c_593, c_328])).
% 3.37/1.57  tff(c_642, plain, (![A_389, B_390, C_391, D_392]: (k9_mcart_1(A_389, B_390, C_391, D_392, '#skF_14')='#skF_13' | k1_xboole_0=D_392 | k1_xboole_0=C_391 | k1_xboole_0=B_390 | k1_xboole_0=A_389 | ~m1_subset_1('#skF_14', k4_zfmisc_1(A_389, B_390, C_391, D_392)))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_621])).
% 3.37/1.57  tff(c_651, plain, (k9_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_14')='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_642])).
% 3.37/1.57  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_30, c_28, c_651])).
% 3.37/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.57  
% 3.37/1.57  Inference rules
% 3.37/1.57  ----------------------
% 3.37/1.57  #Ref     : 0
% 3.37/1.57  #Sup     : 144
% 3.37/1.57  #Fact    : 0
% 3.37/1.57  #Define  : 0
% 3.37/1.57  #Split   : 0
% 3.37/1.57  #Chain   : 0
% 3.37/1.57  #Close   : 0
% 3.37/1.57  
% 3.37/1.57  Ordering : KBO
% 3.37/1.57  
% 3.37/1.57  Simplification rules
% 3.37/1.57  ----------------------
% 3.37/1.57  #Subsume      : 20
% 3.37/1.57  #Demod        : 128
% 3.37/1.57  #Tautology    : 54
% 3.37/1.57  #SimpNegUnit  : 8
% 3.37/1.57  #BackRed      : 0
% 3.37/1.57  
% 3.37/1.57  #Partial instantiations: 0
% 3.37/1.57  #Strategies tried      : 1
% 3.37/1.57  
% 3.37/1.57  Timing (in seconds)
% 3.37/1.57  ----------------------
% 3.37/1.58  Preprocessing        : 0.34
% 3.37/1.58  Parsing              : 0.17
% 3.37/1.58  CNF conversion       : 0.04
% 3.37/1.58  Main loop            : 0.41
% 3.37/1.58  Inferencing          : 0.16
% 3.37/1.58  Reduction            : 0.13
% 3.37/1.58  Demodulation         : 0.09
% 3.37/1.58  BG Simplification    : 0.03
% 3.37/1.58  Subsumption          : 0.07
% 3.37/1.58  Abstraction          : 0.03
% 3.37/1.58  MUC search           : 0.00
% 3.37/1.58  Cooper               : 0.00
% 3.37/1.58  Total                : 0.78
% 3.37/1.58  Index Insertion      : 0.00
% 3.37/1.58  Index Deletion       : 0.00
% 3.37/1.58  Index Matching       : 0.00
% 3.37/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
