%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 492 expanded)
%              Number of leaves         :   29 ( 209 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (3310 expanded)
%              Number of equality atoms :  192 (2141 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

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

tff(f_138,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_81,axiom,(
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

tff(c_42,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_154,plain,(
    ! [B_121,E_122,A_120,D_124,C_123] :
      ( k11_mcart_1(A_120,B_121,C_123,D_124,E_122) = k2_mcart_1(E_122)
      | ~ m1_subset_1(E_122,k4_zfmisc_1(A_120,B_121,C_123,D_124))
      | k1_xboole_0 = D_124
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_121
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_163,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_154])).

tff(c_166,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_163])).

tff(c_34,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_167,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_34])).

tff(c_26,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_4'(F_32,C_29,D_30,E_31,B_28,A_27),D_30)
      | k9_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_3'(F_32,C_29,D_30,E_31,B_28,A_27),C_29)
      | k9_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_1'(F_32,C_29,D_30,E_31,B_28,A_27),A_27)
      | k9_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_2'(F_32,C_29,D_30,E_31,B_28,A_27),B_28)
      | k9_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_487,plain,(
    ! [B_237,C_234,E_236,D_235,A_238,F_233] :
      ( k4_mcart_1('#skF_1'(F_233,C_234,D_235,E_236,B_237,A_238),'#skF_2'(F_233,C_234,D_235,E_236,B_237,A_238),'#skF_3'(F_233,C_234,D_235,E_236,B_237,A_238),'#skF_4'(F_233,C_234,D_235,E_236,B_237,A_238)) = F_233
      | k9_mcart_1(A_238,B_237,C_234,D_235,F_233) = E_236
      | k1_xboole_0 = D_235
      | k1_xboole_0 = C_234
      | k1_xboole_0 = B_237
      | k1_xboole_0 = A_238
      | ~ m1_subset_1(F_233,k4_zfmisc_1(A_238,B_237,C_234,D_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ! [J_88,G_74,H_82,I_86] :
      ( J_88 = '#skF_9'
      | k4_mcart_1(G_74,H_82,I_86,J_88) != '#skF_10'
      | ~ m1_subset_1(J_88,'#skF_8')
      | ~ m1_subset_1(I_86,'#skF_7')
      | ~ m1_subset_1(H_82,'#skF_6')
      | ~ m1_subset_1(G_74,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_571,plain,(
    ! [F_254,C_256,D_255,B_258,A_253,E_257] :
      ( '#skF_4'(F_254,C_256,D_255,E_257,B_258,A_253) = '#skF_9'
      | F_254 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_254,C_256,D_255,E_257,B_258,A_253),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_254,C_256,D_255,E_257,B_258,A_253),'#skF_7')
      | ~ m1_subset_1('#skF_2'(F_254,C_256,D_255,E_257,B_258,A_253),'#skF_6')
      | ~ m1_subset_1('#skF_1'(F_254,C_256,D_255,E_257,B_258,A_253),'#skF_5')
      | k9_mcart_1(A_253,B_258,C_256,D_255,F_254) = E_257
      | k1_xboole_0 = D_255
      | k1_xboole_0 = C_256
      | k1_xboole_0 = B_258
      | k1_xboole_0 = A_253
      | ~ m1_subset_1(F_254,k4_zfmisc_1(A_253,B_258,C_256,D_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_44])).

tff(c_575,plain,(
    ! [C_29,D_30,F_32,A_27,E_31] :
      ( '#skF_4'(F_32,C_29,D_30,E_31,'#skF_6',A_27) = '#skF_9'
      | F_32 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_32,C_29,D_30,E_31,'#skF_6',A_27),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_32,C_29,D_30,E_31,'#skF_6',A_27),'#skF_7')
      | ~ m1_subset_1('#skF_1'(F_32,C_29,D_30,E_31,'#skF_6',A_27),'#skF_5')
      | k9_mcart_1(A_27,'#skF_6',C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,'#skF_6',C_29,D_30)) ) ),
    inference(resolution,[status(thm)],[c_30,c_571])).

tff(c_693,plain,(
    ! [A_325,C_322,E_324,F_321,D_323] :
      ( '#skF_4'(F_321,C_322,D_323,E_324,'#skF_6',A_325) = '#skF_9'
      | F_321 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_321,C_322,D_323,E_324,'#skF_6',A_325),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_321,C_322,D_323,E_324,'#skF_6',A_325),'#skF_7')
      | ~ m1_subset_1('#skF_1'(F_321,C_322,D_323,E_324,'#skF_6',A_325),'#skF_5')
      | k9_mcart_1(A_325,'#skF_6',C_322,D_323,F_321) = E_324
      | k1_xboole_0 = D_323
      | k1_xboole_0 = C_322
      | k1_xboole_0 = A_325
      | ~ m1_subset_1(F_321,k4_zfmisc_1(A_325,'#skF_6',C_322,D_323)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_575])).

tff(c_697,plain,(
    ! [F_32,C_29,D_30,E_31] :
      ( '#skF_4'(F_32,C_29,D_30,E_31,'#skF_6','#skF_5') = '#skF_9'
      | F_32 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_32,C_29,D_30,E_31,'#skF_6','#skF_5'),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_32,C_29,D_30,E_31,'#skF_6','#skF_5'),'#skF_7')
      | k9_mcart_1('#skF_5','#skF_6',C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_32,k4_zfmisc_1('#skF_5','#skF_6',C_29,D_30)) ) ),
    inference(resolution,[status(thm)],[c_32,c_693])).

tff(c_767,plain,(
    ! [F_365,C_366,D_367,E_368] :
      ( '#skF_4'(F_365,C_366,D_367,E_368,'#skF_6','#skF_5') = '#skF_9'
      | F_365 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_365,C_366,D_367,E_368,'#skF_6','#skF_5'),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_365,C_366,D_367,E_368,'#skF_6','#skF_5'),'#skF_7')
      | k9_mcart_1('#skF_5','#skF_6',C_366,D_367,F_365) = E_368
      | k1_xboole_0 = D_367
      | k1_xboole_0 = C_366
      | ~ m1_subset_1(F_365,k4_zfmisc_1('#skF_5','#skF_6',C_366,D_367)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_42,c_697])).

tff(c_771,plain,(
    ! [F_32,D_30,E_31] :
      ( '#skF_4'(F_32,'#skF_7',D_30,E_31,'#skF_6','#skF_5') = '#skF_9'
      | F_32 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_32,'#skF_7',D_30,E_31,'#skF_6','#skF_5'),'#skF_8')
      | k9_mcart_1('#skF_5','#skF_6','#skF_7',D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_32,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_30)) ) ),
    inference(resolution,[status(thm)],[c_28,c_767])).

tff(c_776,plain,(
    ! [F_369,D_370,E_371] :
      ( '#skF_4'(F_369,'#skF_7',D_370,E_371,'#skF_6','#skF_5') = '#skF_9'
      | F_369 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_369,'#skF_7',D_370,E_371,'#skF_6','#skF_5'),'#skF_8')
      | k9_mcart_1('#skF_5','#skF_6','#skF_7',D_370,F_369) = E_371
      | k1_xboole_0 = D_370
      | ~ m1_subset_1(F_369,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_370)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_38,c_771])).

tff(c_780,plain,(
    ! [F_32,E_31] :
      ( '#skF_4'(F_32,'#skF_7','#skF_8',E_31,'#skF_6','#skF_5') = '#skF_9'
      | F_32 != '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_32) = E_31
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_32,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_26,c_776])).

tff(c_785,plain,(
    ! [F_372,E_373] :
      ( '#skF_4'(F_372,'#skF_7','#skF_8',E_373,'#skF_6','#skF_5') = '#skF_9'
      | F_372 != '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_372) = E_373
      | ~ m1_subset_1(F_372,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_36,c_780])).

tff(c_807,plain,(
    ! [E_374] :
      ( '#skF_4'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5') = '#skF_9'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(resolution,[status(thm)],[c_46,c_785])).

tff(c_24,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( k4_mcart_1('#skF_1'(F_32,C_29,D_30,E_31,B_28,A_27),'#skF_2'(F_32,C_29,D_30,E_31,B_28,A_27),'#skF_3'(F_32,C_29,D_30,E_31,B_28,A_27),'#skF_4'(F_32,C_29,D_30,E_31,B_28,A_27)) = F_32
      | k9_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_816,plain,(
    ! [E_374] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_24])).

tff(c_1409,plain,(
    ! [E_374] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_816])).

tff(c_1410,plain,(
    ! [E_374] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_1409])).

tff(c_1521,plain,(
    ! [E_3994] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_3994,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_3994,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_3994,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3994 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_1409])).

tff(c_14,plain,(
    ! [H_25,G_24,F_23,C_16,D_17,A_14,B_15,I_26] :
      ( k11_mcart_1(A_14,B_15,C_16,D_17,k4_mcart_1(F_23,G_24,H_25,I_26)) = I_26
      | k1_xboole_0 = D_17
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k4_mcart_1(F_23,G_24,H_25,I_26),k4_zfmisc_1(A_14,B_15,C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1844,plain,(
    ! [A_4489,E_4488,C_4486,B_4487,D_4485] :
      ( k11_mcart_1(A_4489,B_4487,C_4486,D_4485,k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_4488,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_4488,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_4488,'#skF_6','#skF_5'),'#skF_9')) = '#skF_9'
      | k1_xboole_0 = D_4485
      | k1_xboole_0 = C_4486
      | k1_xboole_0 = B_4487
      | k1_xboole_0 = A_4489
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_4489,B_4487,C_4486,D_4485))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_4488 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1521,c_14])).

tff(c_1853,plain,(
    ! [E_374,A_4489,C_4486,B_4487,D_4485] :
      ( k11_mcart_1(A_4489,B_4487,C_4486,D_4485,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_4485
      | k1_xboole_0 = C_4486
      | k1_xboole_0 = B_4487
      | k1_xboole_0 = A_4489
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_4489,B_4487,C_4486,D_4485))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_1844])).

tff(c_1882,plain,(
    ! [E_374] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(splitLeft,[status(thm)],[c_1853])).

tff(c_3477,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_6' ),
    inference(factorization,[status(thm),theory(equality)],[c_1882])).

tff(c_1903,plain,(
    ! [E_374] : k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ),
    inference(factorization,[status(thm),theory(equality)],[c_1882])).

tff(c_4313,plain,(
    ! [E_16832] : E_16832 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3477,c_1903])).

tff(c_4756,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4313,c_40])).

tff(c_4758,plain,(
    ! [A_20904,B_20905,C_20906,D_20907] :
      ( k11_mcart_1(A_20904,B_20905,C_20906,D_20907,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_20907
      | k1_xboole_0 = C_20906
      | k1_xboole_0 = B_20905
      | k1_xboole_0 = A_20904
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_20904,B_20905,C_20906,D_20907)) ) ),
    inference(splitRight,[status(thm)],[c_1853])).

tff(c_4768,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_4758])).

tff(c_4770,plain,
    ( k2_mcart_1('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_4768])).

tff(c_4772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_167,c_4770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.10  
% 5.74/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.10  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 5.74/2.10  
% 5.74/2.10  %Foreground sorts:
% 5.74/2.10  
% 5.74/2.10  
% 5.74/2.10  %Background operators:
% 5.74/2.10  
% 5.74/2.10  
% 5.74/2.10  %Foreground operators:
% 5.74/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.10  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.74/2.10  tff('#skF_7', type, '#skF_7': $i).
% 5.74/2.10  tff('#skF_10', type, '#skF_10': $i).
% 5.74/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.74/2.10  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff('#skF_6', type, '#skF_6': $i).
% 5.74/2.10  tff('#skF_9', type, '#skF_9': $i).
% 5.74/2.10  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.74/2.10  tff('#skF_8', type, '#skF_8': $i).
% 5.74/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.10  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.74/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.74/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.10  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.74/2.10  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.74/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.10  
% 5.74/2.12  tff(f_138, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_mcart_1)).
% 5.74/2.12  tff(f_54, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 5.74/2.12  tff(f_109, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 5.74/2.12  tff(f_81, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 5.74/2.12  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_40, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_36, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_46, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_154, plain, (![B_121, E_122, A_120, D_124, C_123]: (k11_mcart_1(A_120, B_121, C_123, D_124, E_122)=k2_mcart_1(E_122) | ~m1_subset_1(E_122, k4_zfmisc_1(A_120, B_121, C_123, D_124)) | k1_xboole_0=D_124 | k1_xboole_0=C_123 | k1_xboole_0=B_121 | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.12  tff(c_163, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_154])).
% 5.74/2.12  tff(c_166, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_163])).
% 5.74/2.12  tff(c_34, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_167, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_34])).
% 5.74/2.12  tff(c_26, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_4'(F_32, C_29, D_30, E_31, B_28, A_27), D_30) | k9_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.74/2.12  tff(c_28, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_3'(F_32, C_29, D_30, E_31, B_28, A_27), C_29) | k9_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.74/2.12  tff(c_32, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_1'(F_32, C_29, D_30, E_31, B_28, A_27), A_27) | k9_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.74/2.12  tff(c_30, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_2'(F_32, C_29, D_30, E_31, B_28, A_27), B_28) | k9_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.74/2.12  tff(c_487, plain, (![B_237, C_234, E_236, D_235, A_238, F_233]: (k4_mcart_1('#skF_1'(F_233, C_234, D_235, E_236, B_237, A_238), '#skF_2'(F_233, C_234, D_235, E_236, B_237, A_238), '#skF_3'(F_233, C_234, D_235, E_236, B_237, A_238), '#skF_4'(F_233, C_234, D_235, E_236, B_237, A_238))=F_233 | k9_mcart_1(A_238, B_237, C_234, D_235, F_233)=E_236 | k1_xboole_0=D_235 | k1_xboole_0=C_234 | k1_xboole_0=B_237 | k1_xboole_0=A_238 | ~m1_subset_1(F_233, k4_zfmisc_1(A_238, B_237, C_234, D_235)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.74/2.12  tff(c_44, plain, (![J_88, G_74, H_82, I_86]: (J_88='#skF_9' | k4_mcart_1(G_74, H_82, I_86, J_88)!='#skF_10' | ~m1_subset_1(J_88, '#skF_8') | ~m1_subset_1(I_86, '#skF_7') | ~m1_subset_1(H_82, '#skF_6') | ~m1_subset_1(G_74, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.74/2.12  tff(c_571, plain, (![F_254, C_256, D_255, B_258, A_253, E_257]: ('#skF_4'(F_254, C_256, D_255, E_257, B_258, A_253)='#skF_9' | F_254!='#skF_10' | ~m1_subset_1('#skF_4'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_8') | ~m1_subset_1('#skF_3'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_7') | ~m1_subset_1('#skF_2'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_6') | ~m1_subset_1('#skF_1'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_5') | k9_mcart_1(A_253, B_258, C_256, D_255, F_254)=E_257 | k1_xboole_0=D_255 | k1_xboole_0=C_256 | k1_xboole_0=B_258 | k1_xboole_0=A_253 | ~m1_subset_1(F_254, k4_zfmisc_1(A_253, B_258, C_256, D_255)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_44])).
% 5.74/2.12  tff(c_575, plain, (![C_29, D_30, F_32, A_27, E_31]: ('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', A_27)='#skF_9' | F_32!='#skF_10' | ~m1_subset_1('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', A_27), '#skF_8') | ~m1_subset_1('#skF_3'(F_32, C_29, D_30, E_31, '#skF_6', A_27), '#skF_7') | ~m1_subset_1('#skF_1'(F_32, C_29, D_30, E_31, '#skF_6', A_27), '#skF_5') | k9_mcart_1(A_27, '#skF_6', C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0='#skF_6' | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, '#skF_6', C_29, D_30)))), inference(resolution, [status(thm)], [c_30, c_571])).
% 5.74/2.12  tff(c_693, plain, (![A_325, C_322, E_324, F_321, D_323]: ('#skF_4'(F_321, C_322, D_323, E_324, '#skF_6', A_325)='#skF_9' | F_321!='#skF_10' | ~m1_subset_1('#skF_4'(F_321, C_322, D_323, E_324, '#skF_6', A_325), '#skF_8') | ~m1_subset_1('#skF_3'(F_321, C_322, D_323, E_324, '#skF_6', A_325), '#skF_7') | ~m1_subset_1('#skF_1'(F_321, C_322, D_323, E_324, '#skF_6', A_325), '#skF_5') | k9_mcart_1(A_325, '#skF_6', C_322, D_323, F_321)=E_324 | k1_xboole_0=D_323 | k1_xboole_0=C_322 | k1_xboole_0=A_325 | ~m1_subset_1(F_321, k4_zfmisc_1(A_325, '#skF_6', C_322, D_323)))), inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_575])).
% 5.74/2.12  tff(c_697, plain, (![F_32, C_29, D_30, E_31]: ('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', '#skF_5')='#skF_9' | F_32!='#skF_10' | ~m1_subset_1('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', '#skF_5'), '#skF_8') | ~m1_subset_1('#skF_3'(F_32, C_29, D_30, E_31, '#skF_6', '#skF_5'), '#skF_7') | k9_mcart_1('#skF_5', '#skF_6', C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_32, k4_zfmisc_1('#skF_5', '#skF_6', C_29, D_30)))), inference(resolution, [status(thm)], [c_32, c_693])).
% 5.74/2.12  tff(c_767, plain, (![F_365, C_366, D_367, E_368]: ('#skF_4'(F_365, C_366, D_367, E_368, '#skF_6', '#skF_5')='#skF_9' | F_365!='#skF_10' | ~m1_subset_1('#skF_4'(F_365, C_366, D_367, E_368, '#skF_6', '#skF_5'), '#skF_8') | ~m1_subset_1('#skF_3'(F_365, C_366, D_367, E_368, '#skF_6', '#skF_5'), '#skF_7') | k9_mcart_1('#skF_5', '#skF_6', C_366, D_367, F_365)=E_368 | k1_xboole_0=D_367 | k1_xboole_0=C_366 | ~m1_subset_1(F_365, k4_zfmisc_1('#skF_5', '#skF_6', C_366, D_367)))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_42, c_697])).
% 5.74/2.12  tff(c_771, plain, (![F_32, D_30, E_31]: ('#skF_4'(F_32, '#skF_7', D_30, E_31, '#skF_6', '#skF_5')='#skF_9' | F_32!='#skF_10' | ~m1_subset_1('#skF_4'(F_32, '#skF_7', D_30, E_31, '#skF_6', '#skF_5'), '#skF_8') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_32, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_30)))), inference(resolution, [status(thm)], [c_28, c_767])).
% 5.74/2.12  tff(c_776, plain, (![F_369, D_370, E_371]: ('#skF_4'(F_369, '#skF_7', D_370, E_371, '#skF_6', '#skF_5')='#skF_9' | F_369!='#skF_10' | ~m1_subset_1('#skF_4'(F_369, '#skF_7', D_370, E_371, '#skF_6', '#skF_5'), '#skF_8') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', D_370, F_369)=E_371 | k1_xboole_0=D_370 | ~m1_subset_1(F_369, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_370)))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_38, c_771])).
% 5.74/2.12  tff(c_780, plain, (![F_32, E_31]: ('#skF_4'(F_32, '#skF_7', '#skF_8', E_31, '#skF_6', '#skF_5')='#skF_9' | F_32!='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_32)=E_31 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_32, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_26, c_776])).
% 5.74/2.12  tff(c_785, plain, (![F_372, E_373]: ('#skF_4'(F_372, '#skF_7', '#skF_8', E_373, '#skF_6', '#skF_5')='#skF_9' | F_372!='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_372)=E_373 | ~m1_subset_1(F_372, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_36, c_780])).
% 5.74/2.12  tff(c_807, plain, (![E_374]: ('#skF_4'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5')='#skF_9' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(resolution, [status(thm)], [c_46, c_785])).
% 5.74/2.12  tff(c_24, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k4_mcart_1('#skF_1'(F_32, C_29, D_30, E_31, B_28, A_27), '#skF_2'(F_32, C_29, D_30, E_31, B_28, A_27), '#skF_3'(F_32, C_29, D_30, E_31, B_28, A_27), '#skF_4'(F_32, C_29, D_30, E_31, B_28, A_27))=F_32 | k9_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.74/2.12  tff(c_816, plain, (![E_374]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(superposition, [status(thm), theory('equality')], [c_807, c_24])).
% 5.74/2.12  tff(c_1409, plain, (![E_374]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_816])).
% 5.74/2.12  tff(c_1410, plain, (![E_374]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_1409])).
% 5.74/2.12  tff(c_1521, plain, (![E_3994]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_3994, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_3994, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_3994, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3994)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_1409])).
% 5.74/2.12  tff(c_14, plain, (![H_25, G_24, F_23, C_16, D_17, A_14, B_15, I_26]: (k11_mcart_1(A_14, B_15, C_16, D_17, k4_mcart_1(F_23, G_24, H_25, I_26))=I_26 | k1_xboole_0=D_17 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14 | ~m1_subset_1(k4_mcart_1(F_23, G_24, H_25, I_26), k4_zfmisc_1(A_14, B_15, C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.74/2.12  tff(c_1844, plain, (![A_4489, E_4488, C_4486, B_4487, D_4485]: (k11_mcart_1(A_4489, B_4487, C_4486, D_4485, k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_4488, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_4488, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_4488, '#skF_6', '#skF_5'), '#skF_9'))='#skF_9' | k1_xboole_0=D_4485 | k1_xboole_0=C_4486 | k1_xboole_0=B_4487 | k1_xboole_0=A_4489 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_4489, B_4487, C_4486, D_4485)) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_4488)), inference(superposition, [status(thm), theory('equality')], [c_1521, c_14])).
% 5.74/2.12  tff(c_1853, plain, (![E_374, A_4489, C_4486, B_4487, D_4485]: (k11_mcart_1(A_4489, B_4487, C_4486, D_4485, '#skF_10')='#skF_9' | k1_xboole_0=D_4485 | k1_xboole_0=C_4486 | k1_xboole_0=B_4487 | k1_xboole_0=A_4489 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_4489, B_4487, C_4486, D_4485)) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(superposition, [status(thm), theory('equality')], [c_1410, c_1844])).
% 5.74/2.12  tff(c_1882, plain, (![E_374]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(splitLeft, [status(thm)], [c_1853])).
% 5.74/2.12  tff(c_3477, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_6'), inference(factorization, [status(thm), theory('equality')], [c_1882])).
% 5.74/2.12  tff(c_1903, plain, (![E_374]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(factorization, [status(thm), theory('equality')], [c_1882])).
% 5.74/2.12  tff(c_4313, plain, (![E_16832]: (E_16832='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3477, c_1903])).
% 5.74/2.12  tff(c_4756, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4313, c_40])).
% 5.74/2.12  tff(c_4758, plain, (![A_20904, B_20905, C_20906, D_20907]: (k11_mcart_1(A_20904, B_20905, C_20906, D_20907, '#skF_10')='#skF_9' | k1_xboole_0=D_20907 | k1_xboole_0=C_20906 | k1_xboole_0=B_20905 | k1_xboole_0=A_20904 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_20904, B_20905, C_20906, D_20907)))), inference(splitRight, [status(thm)], [c_1853])).
% 5.74/2.12  tff(c_4768, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_4758])).
% 5.74/2.12  tff(c_4770, plain, (k2_mcart_1('#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_4768])).
% 5.74/2.12  tff(c_4772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_167, c_4770])).
% 5.74/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.12  
% 5.74/2.12  Inference rules
% 5.74/2.12  ----------------------
% 5.74/2.12  #Ref     : 0
% 5.74/2.12  #Sup     : 632
% 5.74/2.12  #Fact    : 4
% 5.74/2.12  #Define  : 0
% 5.74/2.12  #Split   : 9
% 5.74/2.12  #Chain   : 0
% 5.74/2.12  #Close   : 0
% 5.74/2.12  
% 5.74/2.12  Ordering : KBO
% 5.74/2.12  
% 5.74/2.12  Simplification rules
% 5.74/2.12  ----------------------
% 5.74/2.12  #Subsume      : 80
% 5.74/2.12  #Demod        : 254
% 5.74/2.12  #Tautology    : 102
% 5.74/2.12  #SimpNegUnit  : 33
% 5.74/2.12  #BackRed      : 1
% 5.74/2.12  
% 5.74/2.12  #Partial instantiations: 5995
% 5.74/2.12  #Strategies tried      : 1
% 5.74/2.12  
% 5.74/2.12  Timing (in seconds)
% 5.74/2.12  ----------------------
% 5.74/2.12  Preprocessing        : 0.36
% 5.74/2.12  Parsing              : 0.19
% 5.74/2.12  CNF conversion       : 0.03
% 5.74/2.12  Main loop            : 0.96
% 5.74/2.12  Inferencing          : 0.45
% 5.74/2.12  Reduction            : 0.23
% 5.74/2.12  Demodulation         : 0.17
% 5.74/2.12  BG Simplification    : 0.06
% 5.74/2.12  Subsumption          : 0.16
% 5.74/2.12  Abstraction          : 0.09
% 5.74/2.12  MUC search           : 0.00
% 5.74/2.12  Cooper               : 0.00
% 5.74/2.12  Total                : 1.36
% 5.74/2.12  Index Insertion      : 0.00
% 5.74/2.12  Index Deletion       : 0.00
% 5.74/2.12  Index Matching       : 0.00
% 5.74/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
