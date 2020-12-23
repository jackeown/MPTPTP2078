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
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.15s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

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
                         => E = I ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k10_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

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
      | k10_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_3'(F_32,C_29,D_30,E_31,B_28,A_27),C_29)
      | k10_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_1'(F_32,C_29,D_30,E_31,B_28,A_27),A_27)
      | k10_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1('#skF_2'(F_32,C_29,D_30,E_31,B_28,A_27),B_28)
      | k10_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_487,plain,(
    ! [B_237,C_234,E_236,D_235,A_238,F_233] :
      ( k4_mcart_1('#skF_1'(F_233,C_234,D_235,E_236,B_237,A_238),'#skF_2'(F_233,C_234,D_235,E_236,B_237,A_238),'#skF_3'(F_233,C_234,D_235,E_236,B_237,A_238),'#skF_4'(F_233,C_234,D_235,E_236,B_237,A_238)) = F_233
      | k10_mcart_1(A_238,B_237,C_234,D_235,F_233) = E_236
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
      | k10_mcart_1(A_253,B_258,C_256,D_255,F_254) = E_257
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
      | k10_mcart_1(A_27,'#skF_6',C_29,D_30,F_32) = E_31
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
      | k10_mcart_1(A_325,'#skF_6',C_322,D_323,F_321) = E_324
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
      | k10_mcart_1('#skF_5','#skF_6',C_29,D_30,F_32) = E_31
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
      | k10_mcart_1('#skF_5','#skF_6',C_366,D_367,F_365) = E_368
      | k1_xboole_0 = D_367
      | k1_xboole_0 = C_366
      | ~ m1_subset_1(F_365,k4_zfmisc_1('#skF_5','#skF_6',C_366,D_367)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_42,c_697])).

tff(c_771,plain,(
    ! [F_32,D_30,E_31] :
      ( '#skF_4'(F_32,'#skF_7',D_30,E_31,'#skF_6','#skF_5') = '#skF_9'
      | F_32 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_32,'#skF_7',D_30,E_31,'#skF_6','#skF_5'),'#skF_8')
      | k10_mcart_1('#skF_5','#skF_6','#skF_7',D_30,F_32) = E_31
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
      | k10_mcart_1('#skF_5','#skF_6','#skF_7',D_370,F_369) = E_371
      | k1_xboole_0 = D_370
      | ~ m1_subset_1(F_369,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_370)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_38,c_771])).

tff(c_780,plain,(
    ! [F_32,E_31] :
      ( '#skF_4'(F_32,'#skF_7','#skF_8',E_31,'#skF_6','#skF_5') = '#skF_9'
      | F_32 != '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_32) = E_31
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
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_372) = E_373
      | ~ m1_subset_1(F_372,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_36,c_780])).

tff(c_807,plain,(
    ! [E_374] :
      ( '#skF_4'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5') = '#skF_9'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(resolution,[status(thm)],[c_46,c_785])).

tff(c_24,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( k4_mcart_1('#skF_1'(F_32,C_29,D_30,E_31,B_28,A_27),'#skF_2'(F_32,C_29,D_30,E_31,B_28,A_27),'#skF_3'(F_32,C_29,D_30,E_31,B_28,A_27),'#skF_4'(F_32,C_29,D_30,E_31,B_28,A_27)) = F_32
      | k10_mcart_1(A_27,B_28,C_29,D_30,F_32) = E_31
      | k1_xboole_0 = D_30
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(F_32,k4_zfmisc_1(A_27,B_28,C_29,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_816,plain,(
    ! [E_374] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_24])).

tff(c_1344,plain,(
    ! [E_374] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_816])).

tff(c_1345,plain,(
    ! [E_374] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_374,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_1344])).

tff(c_1453,plain,(
    ! [E_3994] :
      ( k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_3994,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_3994,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_3994,'#skF_6','#skF_5'),'#skF_9') = '#skF_10'
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3994 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_1344])).

tff(c_14,plain,(
    ! [H_25,G_24,F_23,C_16,D_17,A_14,B_15,I_26] :
      ( k11_mcart_1(A_14,B_15,C_16,D_17,k4_mcart_1(F_23,G_24,H_25,I_26)) = I_26
      | k1_xboole_0 = D_17
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(k4_mcart_1(F_23,G_24,H_25,I_26),k4_zfmisc_1(A_14,B_15,C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1785,plain,(
    ! [A_4489,E_4488,C_4486,B_4487,D_4485] :
      ( k11_mcart_1(A_4489,B_4487,C_4486,D_4485,k4_mcart_1('#skF_1'('#skF_10','#skF_7','#skF_8',E_4488,'#skF_6','#skF_5'),'#skF_2'('#skF_10','#skF_7','#skF_8',E_4488,'#skF_6','#skF_5'),'#skF_3'('#skF_10','#skF_7','#skF_8',E_4488,'#skF_6','#skF_5'),'#skF_9')) = '#skF_9'
      | k1_xboole_0 = D_4485
      | k1_xboole_0 = C_4486
      | k1_xboole_0 = B_4487
      | k1_xboole_0 = A_4489
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_4489,B_4487,C_4486,D_4485))
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_4488 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1453,c_14])).

tff(c_1794,plain,(
    ! [E_374,A_4489,C_4486,B_4487,D_4485] :
      ( k11_mcart_1(A_4489,B_4487,C_4486,D_4485,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_4485
      | k1_xboole_0 = C_4486
      | k1_xboole_0 = B_4487
      | k1_xboole_0 = A_4489
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_4489,B_4487,C_4486,D_4485))
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1345,c_1785])).

tff(c_1820,plain,(
    ! [E_374] :
      ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374
      | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_374 ) ),
    inference(splitLeft,[status(thm)],[c_1794])).

tff(c_3969,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(factorization,[status(thm),theory(equality)],[c_1820])).

tff(c_3260,plain,(
    ! [E_12869] : k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_12869 ),
    inference(factorization,[status(thm),theory(equality)],[c_1820])).

tff(c_4533,plain,(
    ! [E_20904] : E_20904 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_3260])).

tff(c_5019,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4533,c_38])).

tff(c_5060,plain,(
    ! [A_25158,B_25159,C_25160,D_25161] :
      ( k11_mcart_1(A_25158,B_25159,C_25160,D_25161,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_25161
      | k1_xboole_0 = C_25160
      | k1_xboole_0 = B_25159
      | k1_xboole_0 = A_25158
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_25158,B_25159,C_25160,D_25161)) ) ),
    inference(splitRight,[status(thm)],[c_1794])).

tff(c_5070,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_5060])).

tff(c_5072,plain,
    ( k2_mcart_1('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_5070])).

tff(c_5074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_167,c_5072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.23  
% 6.15/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.24  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 6.15/2.24  
% 6.15/2.24  %Foreground sorts:
% 6.15/2.24  
% 6.15/2.24  
% 6.15/2.24  %Background operators:
% 6.15/2.24  
% 6.15/2.24  
% 6.15/2.24  %Foreground operators:
% 6.15/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.15/2.24  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.15/2.24  tff('#skF_7', type, '#skF_7': $i).
% 6.15/2.24  tff('#skF_10', type, '#skF_10': $i).
% 6.15/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.15/2.24  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff('#skF_6', type, '#skF_6': $i).
% 6.15/2.24  tff('#skF_9', type, '#skF_9': $i).
% 6.15/2.24  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.15/2.24  tff('#skF_8', type, '#skF_8': $i).
% 6.15/2.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.15/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.15/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.15/2.24  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 6.15/2.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.15/2.24  
% 6.15/2.26  tff(f_138, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_mcart_1)).
% 6.15/2.26  tff(f_54, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 6.15/2.26  tff(f_109, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 6.15/2.26  tff(f_81, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 6.15/2.26  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_40, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_36, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_46, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_154, plain, (![B_121, E_122, A_120, D_124, C_123]: (k11_mcart_1(A_120, B_121, C_123, D_124, E_122)=k2_mcart_1(E_122) | ~m1_subset_1(E_122, k4_zfmisc_1(A_120, B_121, C_123, D_124)) | k1_xboole_0=D_124 | k1_xboole_0=C_123 | k1_xboole_0=B_121 | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.15/2.26  tff(c_163, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_154])).
% 6.15/2.26  tff(c_166, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_163])).
% 6.15/2.26  tff(c_34, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_167, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_34])).
% 6.15/2.26  tff(c_26, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_4'(F_32, C_29, D_30, E_31, B_28, A_27), D_30) | k10_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.15/2.26  tff(c_28, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_3'(F_32, C_29, D_30, E_31, B_28, A_27), C_29) | k10_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.15/2.26  tff(c_32, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_1'(F_32, C_29, D_30, E_31, B_28, A_27), A_27) | k10_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.15/2.26  tff(c_30, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1('#skF_2'(F_32, C_29, D_30, E_31, B_28, A_27), B_28) | k10_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.15/2.26  tff(c_487, plain, (![B_237, C_234, E_236, D_235, A_238, F_233]: (k4_mcart_1('#skF_1'(F_233, C_234, D_235, E_236, B_237, A_238), '#skF_2'(F_233, C_234, D_235, E_236, B_237, A_238), '#skF_3'(F_233, C_234, D_235, E_236, B_237, A_238), '#skF_4'(F_233, C_234, D_235, E_236, B_237, A_238))=F_233 | k10_mcart_1(A_238, B_237, C_234, D_235, F_233)=E_236 | k1_xboole_0=D_235 | k1_xboole_0=C_234 | k1_xboole_0=B_237 | k1_xboole_0=A_238 | ~m1_subset_1(F_233, k4_zfmisc_1(A_238, B_237, C_234, D_235)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.15/2.26  tff(c_44, plain, (![J_88, G_74, H_82, I_86]: (J_88='#skF_9' | k4_mcart_1(G_74, H_82, I_86, J_88)!='#skF_10' | ~m1_subset_1(J_88, '#skF_8') | ~m1_subset_1(I_86, '#skF_7') | ~m1_subset_1(H_82, '#skF_6') | ~m1_subset_1(G_74, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.15/2.26  tff(c_571, plain, (![F_254, C_256, D_255, B_258, A_253, E_257]: ('#skF_4'(F_254, C_256, D_255, E_257, B_258, A_253)='#skF_9' | F_254!='#skF_10' | ~m1_subset_1('#skF_4'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_8') | ~m1_subset_1('#skF_3'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_7') | ~m1_subset_1('#skF_2'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_6') | ~m1_subset_1('#skF_1'(F_254, C_256, D_255, E_257, B_258, A_253), '#skF_5') | k10_mcart_1(A_253, B_258, C_256, D_255, F_254)=E_257 | k1_xboole_0=D_255 | k1_xboole_0=C_256 | k1_xboole_0=B_258 | k1_xboole_0=A_253 | ~m1_subset_1(F_254, k4_zfmisc_1(A_253, B_258, C_256, D_255)))), inference(superposition, [status(thm), theory('equality')], [c_487, c_44])).
% 6.15/2.26  tff(c_575, plain, (![C_29, D_30, F_32, A_27, E_31]: ('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', A_27)='#skF_9' | F_32!='#skF_10' | ~m1_subset_1('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', A_27), '#skF_8') | ~m1_subset_1('#skF_3'(F_32, C_29, D_30, E_31, '#skF_6', A_27), '#skF_7') | ~m1_subset_1('#skF_1'(F_32, C_29, D_30, E_31, '#skF_6', A_27), '#skF_5') | k10_mcart_1(A_27, '#skF_6', C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0='#skF_6' | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, '#skF_6', C_29, D_30)))), inference(resolution, [status(thm)], [c_30, c_571])).
% 6.15/2.26  tff(c_693, plain, (![A_325, C_322, E_324, F_321, D_323]: ('#skF_4'(F_321, C_322, D_323, E_324, '#skF_6', A_325)='#skF_9' | F_321!='#skF_10' | ~m1_subset_1('#skF_4'(F_321, C_322, D_323, E_324, '#skF_6', A_325), '#skF_8') | ~m1_subset_1('#skF_3'(F_321, C_322, D_323, E_324, '#skF_6', A_325), '#skF_7') | ~m1_subset_1('#skF_1'(F_321, C_322, D_323, E_324, '#skF_6', A_325), '#skF_5') | k10_mcart_1(A_325, '#skF_6', C_322, D_323, F_321)=E_324 | k1_xboole_0=D_323 | k1_xboole_0=C_322 | k1_xboole_0=A_325 | ~m1_subset_1(F_321, k4_zfmisc_1(A_325, '#skF_6', C_322, D_323)))), inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_575])).
% 6.15/2.26  tff(c_697, plain, (![F_32, C_29, D_30, E_31]: ('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', '#skF_5')='#skF_9' | F_32!='#skF_10' | ~m1_subset_1('#skF_4'(F_32, C_29, D_30, E_31, '#skF_6', '#skF_5'), '#skF_8') | ~m1_subset_1('#skF_3'(F_32, C_29, D_30, E_31, '#skF_6', '#skF_5'), '#skF_7') | k10_mcart_1('#skF_5', '#skF_6', C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_32, k4_zfmisc_1('#skF_5', '#skF_6', C_29, D_30)))), inference(resolution, [status(thm)], [c_32, c_693])).
% 6.15/2.26  tff(c_767, plain, (![F_365, C_366, D_367, E_368]: ('#skF_4'(F_365, C_366, D_367, E_368, '#skF_6', '#skF_5')='#skF_9' | F_365!='#skF_10' | ~m1_subset_1('#skF_4'(F_365, C_366, D_367, E_368, '#skF_6', '#skF_5'), '#skF_8') | ~m1_subset_1('#skF_3'(F_365, C_366, D_367, E_368, '#skF_6', '#skF_5'), '#skF_7') | k10_mcart_1('#skF_5', '#skF_6', C_366, D_367, F_365)=E_368 | k1_xboole_0=D_367 | k1_xboole_0=C_366 | ~m1_subset_1(F_365, k4_zfmisc_1('#skF_5', '#skF_6', C_366, D_367)))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_42, c_697])).
% 6.15/2.26  tff(c_771, plain, (![F_32, D_30, E_31]: ('#skF_4'(F_32, '#skF_7', D_30, E_31, '#skF_6', '#skF_5')='#skF_9' | F_32!='#skF_10' | ~m1_subset_1('#skF_4'(F_32, '#skF_7', D_30, E_31, '#skF_6', '#skF_5'), '#skF_8') | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_32, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_30)))), inference(resolution, [status(thm)], [c_28, c_767])).
% 6.15/2.26  tff(c_776, plain, (![F_369, D_370, E_371]: ('#skF_4'(F_369, '#skF_7', D_370, E_371, '#skF_6', '#skF_5')='#skF_9' | F_369!='#skF_10' | ~m1_subset_1('#skF_4'(F_369, '#skF_7', D_370, E_371, '#skF_6', '#skF_5'), '#skF_8') | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', D_370, F_369)=E_371 | k1_xboole_0=D_370 | ~m1_subset_1(F_369, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_370)))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_38, c_771])).
% 6.15/2.26  tff(c_780, plain, (![F_32, E_31]: ('#skF_4'(F_32, '#skF_7', '#skF_8', E_31, '#skF_6', '#skF_5')='#skF_9' | F_32!='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_32)=E_31 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_32, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_26, c_776])).
% 6.15/2.26  tff(c_785, plain, (![F_372, E_373]: ('#skF_4'(F_372, '#skF_7', '#skF_8', E_373, '#skF_6', '#skF_5')='#skF_9' | F_372!='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_372)=E_373 | ~m1_subset_1(F_372, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_36, c_780])).
% 6.15/2.26  tff(c_807, plain, (![E_374]: ('#skF_4'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5')='#skF_9' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(resolution, [status(thm)], [c_46, c_785])).
% 6.15/2.26  tff(c_24, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k4_mcart_1('#skF_1'(F_32, C_29, D_30, E_31, B_28, A_27), '#skF_2'(F_32, C_29, D_30, E_31, B_28, A_27), '#skF_3'(F_32, C_29, D_30, E_31, B_28, A_27), '#skF_4'(F_32, C_29, D_30, E_31, B_28, A_27))=F_32 | k10_mcart_1(A_27, B_28, C_29, D_30, F_32)=E_31 | k1_xboole_0=D_30 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | ~m1_subset_1(F_32, k4_zfmisc_1(A_27, B_28, C_29, D_30)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.15/2.26  tff(c_816, plain, (![E_374]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(superposition, [status(thm), theory('equality')], [c_807, c_24])).
% 6.15/2.26  tff(c_1344, plain, (![E_374]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_816])).
% 6.15/2.26  tff(c_1345, plain, (![E_374]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_374, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_1344])).
% 6.15/2.26  tff(c_1453, plain, (![E_3994]: (k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_3994, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_3994, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_3994, '#skF_6', '#skF_5'), '#skF_9')='#skF_10' | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3994)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_1344])).
% 6.15/2.26  tff(c_14, plain, (![H_25, G_24, F_23, C_16, D_17, A_14, B_15, I_26]: (k11_mcart_1(A_14, B_15, C_16, D_17, k4_mcart_1(F_23, G_24, H_25, I_26))=I_26 | k1_xboole_0=D_17 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14 | ~m1_subset_1(k4_mcart_1(F_23, G_24, H_25, I_26), k4_zfmisc_1(A_14, B_15, C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.15/2.26  tff(c_1785, plain, (![A_4489, E_4488, C_4486, B_4487, D_4485]: (k11_mcart_1(A_4489, B_4487, C_4486, D_4485, k4_mcart_1('#skF_1'('#skF_10', '#skF_7', '#skF_8', E_4488, '#skF_6', '#skF_5'), '#skF_2'('#skF_10', '#skF_7', '#skF_8', E_4488, '#skF_6', '#skF_5'), '#skF_3'('#skF_10', '#skF_7', '#skF_8', E_4488, '#skF_6', '#skF_5'), '#skF_9'))='#skF_9' | k1_xboole_0=D_4485 | k1_xboole_0=C_4486 | k1_xboole_0=B_4487 | k1_xboole_0=A_4489 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_4489, B_4487, C_4486, D_4485)) | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_4488)), inference(superposition, [status(thm), theory('equality')], [c_1453, c_14])).
% 6.15/2.26  tff(c_1794, plain, (![E_374, A_4489, C_4486, B_4487, D_4485]: (k11_mcart_1(A_4489, B_4487, C_4486, D_4485, '#skF_10')='#skF_9' | k1_xboole_0=D_4485 | k1_xboole_0=C_4486 | k1_xboole_0=B_4487 | k1_xboole_0=A_4489 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_4489, B_4487, C_4486, D_4485)) | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374 | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(superposition, [status(thm), theory('equality')], [c_1345, c_1785])).
% 6.15/2.26  tff(c_1820, plain, (![E_374]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374 | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_374)), inference(splitLeft, [status(thm)], [c_1794])).
% 6.15/2.26  tff(c_3969, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(factorization, [status(thm), theory('equality')], [c_1820])).
% 6.15/2.26  tff(c_3260, plain, (![E_12869]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_12869)), inference(factorization, [status(thm), theory('equality')], [c_1820])).
% 6.15/2.26  tff(c_4533, plain, (![E_20904]: (E_20904='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3969, c_3260])).
% 6.15/2.26  tff(c_5019, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4533, c_38])).
% 6.15/2.26  tff(c_5060, plain, (![A_25158, B_25159, C_25160, D_25161]: (k11_mcart_1(A_25158, B_25159, C_25160, D_25161, '#skF_10')='#skF_9' | k1_xboole_0=D_25161 | k1_xboole_0=C_25160 | k1_xboole_0=B_25159 | k1_xboole_0=A_25158 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_25158, B_25159, C_25160, D_25161)))), inference(splitRight, [status(thm)], [c_1794])).
% 6.15/2.26  tff(c_5070, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_5060])).
% 6.15/2.26  tff(c_5072, plain, (k2_mcart_1('#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_5070])).
% 6.15/2.26  tff(c_5074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_167, c_5072])).
% 6.15/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.26  
% 6.15/2.26  Inference rules
% 6.15/2.26  ----------------------
% 6.15/2.26  #Ref     : 0
% 6.15/2.26  #Sup     : 826
% 6.15/2.26  #Fact    : 4
% 6.15/2.26  #Define  : 0
% 6.15/2.26  #Split   : 9
% 6.15/2.26  #Chain   : 0
% 6.15/2.26  #Close   : 0
% 6.15/2.26  
% 6.15/2.26  Ordering : KBO
% 6.15/2.26  
% 6.15/2.26  Simplification rules
% 6.15/2.26  ----------------------
% 6.15/2.26  #Subsume      : 105
% 6.15/2.26  #Demod        : 260
% 6.15/2.26  #Tautology    : 110
% 6.15/2.26  #SimpNegUnit  : 33
% 6.15/2.26  #BackRed      : 1
% 6.15/2.26  
% 6.15/2.26  #Partial instantiations: 5679
% 6.15/2.26  #Strategies tried      : 1
% 6.15/2.26  
% 6.15/2.26  Timing (in seconds)
% 6.15/2.26  ----------------------
% 6.15/2.26  Preprocessing        : 0.37
% 6.15/2.26  Parsing              : 0.19
% 6.15/2.26  CNF conversion       : 0.03
% 6.15/2.26  Main loop            : 1.07
% 6.15/2.26  Inferencing          : 0.51
% 6.15/2.26  Reduction            : 0.26
% 6.15/2.26  Demodulation         : 0.19
% 6.15/2.26  BG Simplification    : 0.08
% 6.15/2.26  Subsumption          : 0.16
% 6.15/2.26  Abstraction          : 0.10
% 6.15/2.26  MUC search           : 0.00
% 6.15/2.26  Cooper               : 0.00
% 6.15/2.26  Total                : 1.47
% 6.15/2.26  Index Insertion      : 0.00
% 6.15/2.26  Index Deletion       : 0.00
% 6.15/2.26  Index Matching       : 0.00
% 6.15/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
