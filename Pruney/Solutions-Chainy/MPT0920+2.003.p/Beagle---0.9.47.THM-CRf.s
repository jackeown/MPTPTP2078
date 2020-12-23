%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:16 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 127 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  188 ( 575 expanded)
%              Number of equality atoms :  134 ( 364 expanded)
%              Maximal formula depth    :   21 (   6 average)
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

tff(f_122,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_89,axiom,(
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

tff(c_32,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

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

tff(c_526,plain,(
    ! [A_246,E_245,D_243,B_244,C_242] :
      ( k4_mcart_1('#skF_1'(C_242,D_243,B_244,E_245,A_246),'#skF_2'(C_242,D_243,B_244,E_245,A_246),'#skF_3'(C_242,D_243,B_244,E_245,A_246),'#skF_4'(C_242,D_243,B_244,E_245,A_246)) = E_245
      | ~ m1_subset_1(E_245,k4_zfmisc_1(A_246,B_244,C_242,D_243))
      | k1_xboole_0 = D_243
      | k1_xboole_0 = C_242
      | k1_xboole_0 = B_244
      | k1_xboole_0 = A_246 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [H_108,G_100,I_112,J_114] :
      ( H_108 = '#skF_9'
      | k4_mcart_1(G_100,H_108,I_112,J_114) != '#skF_10'
      | ~ m1_subset_1(J_114,'#skF_8')
      | ~ m1_subset_1(I_112,'#skF_7')
      | ~ m1_subset_1(H_108,'#skF_6')
      | ~ m1_subset_1(G_100,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_590,plain,(
    ! [E_255,C_252,D_256,B_254,A_253] :
      ( '#skF_2'(C_252,D_256,B_254,E_255,A_253) = '#skF_9'
      | E_255 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_252,D_256,B_254,E_255,A_253),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_252,D_256,B_254,E_255,A_253),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_252,D_256,B_254,E_255,A_253),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_252,D_256,B_254,E_255,A_253),'#skF_5')
      | ~ m1_subset_1(E_255,k4_zfmisc_1(A_253,B_254,C_252,D_256))
      | k1_xboole_0 = D_256
      | k1_xboole_0 = C_252
      | k1_xboole_0 = B_254
      | k1_xboole_0 = A_253 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_42])).

tff(c_594,plain,(
    ! [C_17,D_18,E_50,A_15] :
      ( '#skF_2'(C_17,D_18,'#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_17,D_18,'#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6',C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_16,c_590])).

tff(c_842,plain,(
    ! [C_309,D_310,E_311,A_312] :
      ( '#skF_2'(C_309,D_310,'#skF_6',E_311,A_312) = '#skF_9'
      | E_311 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_309,D_310,'#skF_6',E_311,A_312),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_309,D_310,'#skF_6',E_311,A_312),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_309,D_310,'#skF_6',E_311,A_312),'#skF_5')
      | ~ m1_subset_1(E_311,k4_zfmisc_1(A_312,'#skF_6',C_309,D_310))
      | k1_xboole_0 = D_310
      | k1_xboole_0 = C_309
      | k1_xboole_0 = A_312 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_594])).

tff(c_846,plain,(
    ! [C_17,E_50,A_15] :
      ( '#skF_2'(C_17,'#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_17,'#skF_8','#skF_6',E_50,A_15),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_17,'#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6',C_17,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_12,c_842])).

tff(c_970,plain,(
    ! [C_342,E_343,A_344] :
      ( '#skF_2'(C_342,'#skF_8','#skF_6',E_343,A_344) = '#skF_9'
      | E_343 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_342,'#skF_8','#skF_6',E_343,A_344),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_342,'#skF_8','#skF_6',E_343,A_344),'#skF_5')
      | ~ m1_subset_1(E_343,k4_zfmisc_1(A_344,'#skF_6',C_342,'#skF_8'))
      | k1_xboole_0 = C_342
      | k1_xboole_0 = A_344 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_34,c_846])).

tff(c_974,plain,(
    ! [E_50,A_15] :
      ( '#skF_2'('#skF_7','#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_14,c_970])).

tff(c_979,plain,(
    ! [E_345,A_346] :
      ( '#skF_2'('#skF_7','#skF_8','#skF_6',E_345,A_346) = '#skF_9'
      | E_345 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_345,A_346),'#skF_5')
      | ~ m1_subset_1(E_345,k4_zfmisc_1(A_346,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_346 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_36,c_974])).

tff(c_983,plain,(
    ! [E_50] :
      ( '#skF_2'('#skF_7','#skF_8','#skF_6',E_50,'#skF_5') = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_979])).

tff(c_988,plain,(
    ! [E_347] :
      ( '#skF_2'('#skF_7','#skF_8','#skF_6',E_347,'#skF_5') = '#skF_9'
      | E_347 != '#skF_10'
      | ~ m1_subset_1(E_347,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_40,c_983])).

tff(c_1012,plain,(
    '#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_44,c_988])).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_50,C_17] :
      ( k4_mcart_1('#skF_1'(C_17,D_18,B_16,E_50,A_15),'#skF_2'(C_17,D_18,B_16,E_50,A_15),'#skF_3'(C_17,D_18,B_16,E_50,A_15),'#skF_4'(C_17,D_18,B_16,E_50,A_15)) = E_50
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,B_16,C_17,D_18))
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1019,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_10])).

tff(c_1030,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1019])).

tff(c_1031,plain,(
    k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_1030])).

tff(c_130,plain,(
    ! [A_139,B_140,C_141,D_142] : k4_tarski(k3_mcart_1(A_139,B_140,C_141),D_142) = k4_mcart_1(A_139,B_140,C_141,D_142) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_83,B_84] : k1_mcart_1(k4_tarski(A_83,B_84)) = A_83 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_139,plain,(
    ! [A_139,B_140,C_141,D_142] : k1_mcart_1(k4_mcart_1(A_139,B_140,C_141,D_142)) = k3_mcart_1(A_139,B_140,C_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_28])).

tff(c_1043,plain,(
    k3_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = k1_mcart_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_139])).

tff(c_63,plain,(
    ! [A_119,B_120,C_121] : k4_tarski(k4_tarski(A_119,B_120),C_121) = k3_mcart_1(A_119,B_120,C_121) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_119,B_120,C_121] : k1_mcart_1(k3_mcart_1(A_119,B_120,C_121)) = k4_tarski(A_119,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_28])).

tff(c_1092,plain,(
    k4_tarski('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = k1_mcart_1(k1_mcart_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_72])).

tff(c_30,plain,(
    ! [A_83,B_84] : k2_mcart_1(k4_tarski(A_83,B_84)) = B_84 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1119,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_30])).

tff(c_462,plain,(
    ! [B_234,A_233,D_232,C_235,E_236] :
      ( k9_mcart_1(A_233,B_234,C_235,D_232,E_236) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_236)))
      | ~ m1_subset_1(E_236,k4_zfmisc_1(A_233,B_234,C_235,D_232))
      | k1_xboole_0 = D_232
      | k1_xboole_0 = C_235
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_233 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_480,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_462])).

tff(c_487,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_480])).

tff(c_1127,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_487])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:53:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.92  
% 4.18/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.92  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 4.18/1.92  
% 4.18/1.92  %Foreground sorts:
% 4.18/1.92  
% 4.18/1.92  
% 4.18/1.92  %Background operators:
% 4.18/1.92  
% 4.18/1.92  
% 4.18/1.92  %Foreground operators:
% 4.18/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.18/1.92  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.18/1.92  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.18/1.92  tff('#skF_7', type, '#skF_7': $i).
% 4.18/1.92  tff('#skF_10', type, '#skF_10': $i).
% 4.18/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.18/1.92  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.18/1.92  tff('#skF_9', type, '#skF_9': $i).
% 4.18/1.92  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.18/1.92  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff('#skF_8', type, '#skF_8': $i).
% 4.18/1.92  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.92  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.18/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.18/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.92  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.18/1.92  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.18/1.92  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.18/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.18/1.92  
% 4.18/1.94  tff(f_122, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 4.18/1.94  tff(f_64, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 4.18/1.94  tff(f_31, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 4.18/1.94  tff(f_93, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.18/1.94  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.18/1.94  tff(f_89, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 4.18/1.94  tff(c_32, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_34, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_44, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_18, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), A_15) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.94  tff(c_14, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_3'(C_17, D_18, B_16, E_50, A_15), C_17) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.94  tff(c_12, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_4'(C_17, D_18, B_16, E_50, A_15), D_18) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.94  tff(c_16, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_2'(C_17, D_18, B_16, E_50, A_15), B_16) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.94  tff(c_526, plain, (![A_246, E_245, D_243, B_244, C_242]: (k4_mcart_1('#skF_1'(C_242, D_243, B_244, E_245, A_246), '#skF_2'(C_242, D_243, B_244, E_245, A_246), '#skF_3'(C_242, D_243, B_244, E_245, A_246), '#skF_4'(C_242, D_243, B_244, E_245, A_246))=E_245 | ~m1_subset_1(E_245, k4_zfmisc_1(A_246, B_244, C_242, D_243)) | k1_xboole_0=D_243 | k1_xboole_0=C_242 | k1_xboole_0=B_244 | k1_xboole_0=A_246)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.94  tff(c_42, plain, (![H_108, G_100, I_112, J_114]: (H_108='#skF_9' | k4_mcart_1(G_100, H_108, I_112, J_114)!='#skF_10' | ~m1_subset_1(J_114, '#skF_8') | ~m1_subset_1(I_112, '#skF_7') | ~m1_subset_1(H_108, '#skF_6') | ~m1_subset_1(G_100, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.18/1.94  tff(c_590, plain, (![E_255, C_252, D_256, B_254, A_253]: ('#skF_2'(C_252, D_256, B_254, E_255, A_253)='#skF_9' | E_255!='#skF_10' | ~m1_subset_1('#skF_4'(C_252, D_256, B_254, E_255, A_253), '#skF_8') | ~m1_subset_1('#skF_3'(C_252, D_256, B_254, E_255, A_253), '#skF_7') | ~m1_subset_1('#skF_2'(C_252, D_256, B_254, E_255, A_253), '#skF_6') | ~m1_subset_1('#skF_1'(C_252, D_256, B_254, E_255, A_253), '#skF_5') | ~m1_subset_1(E_255, k4_zfmisc_1(A_253, B_254, C_252, D_256)) | k1_xboole_0=D_256 | k1_xboole_0=C_252 | k1_xboole_0=B_254 | k1_xboole_0=A_253)), inference(superposition, [status(thm), theory('equality')], [c_526, c_42])).
% 4.18/1.94  tff(c_594, plain, (![C_17, D_18, E_50, A_15]: ('#skF_2'(C_17, D_18, '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_8') | ~m1_subset_1('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_16, c_590])).
% 4.18/1.94  tff(c_842, plain, (![C_309, D_310, E_311, A_312]: ('#skF_2'(C_309, D_310, '#skF_6', E_311, A_312)='#skF_9' | E_311!='#skF_10' | ~m1_subset_1('#skF_4'(C_309, D_310, '#skF_6', E_311, A_312), '#skF_8') | ~m1_subset_1('#skF_3'(C_309, D_310, '#skF_6', E_311, A_312), '#skF_7') | ~m1_subset_1('#skF_1'(C_309, D_310, '#skF_6', E_311, A_312), '#skF_5') | ~m1_subset_1(E_311, k4_zfmisc_1(A_312, '#skF_6', C_309, D_310)) | k1_xboole_0=D_310 | k1_xboole_0=C_309 | k1_xboole_0=A_312)), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_594])).
% 4.18/1.94  tff(c_846, plain, (![C_17, E_50, A_15]: ('#skF_2'(C_17, '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_842])).
% 4.18/1.94  tff(c_970, plain, (![C_342, E_343, A_344]: ('#skF_2'(C_342, '#skF_8', '#skF_6', E_343, A_344)='#skF_9' | E_343!='#skF_10' | ~m1_subset_1('#skF_3'(C_342, '#skF_8', '#skF_6', E_343, A_344), '#skF_7') | ~m1_subset_1('#skF_1'(C_342, '#skF_8', '#skF_6', E_343, A_344), '#skF_5') | ~m1_subset_1(E_343, k4_zfmisc_1(A_344, '#skF_6', C_342, '#skF_8')) | k1_xboole_0=C_342 | k1_xboole_0=A_344)), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_34, c_846])).
% 4.18/1.94  tff(c_974, plain, (![E_50, A_15]: ('#skF_2'('#skF_7', '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_970])).
% 4.18/1.94  tff(c_979, plain, (![E_345, A_346]: ('#skF_2'('#skF_7', '#skF_8', '#skF_6', E_345, A_346)='#skF_9' | E_345!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_345, A_346), '#skF_5') | ~m1_subset_1(E_345, k4_zfmisc_1(A_346, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_346)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_36, c_974])).
% 4.18/1.94  tff(c_983, plain, (![E_50]: ('#skF_2'('#skF_7', '#skF_8', '#skF_6', E_50, '#skF_5')='#skF_9' | E_50!='#skF_10' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_18, c_979])).
% 4.18/1.94  tff(c_988, plain, (![E_347]: ('#skF_2'('#skF_7', '#skF_8', '#skF_6', E_347, '#skF_5')='#skF_9' | E_347!='#skF_10' | ~m1_subset_1(E_347, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_40, c_983])).
% 4.18/1.94  tff(c_1012, plain, ('#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_44, c_988])).
% 4.18/1.94  tff(c_10, plain, (![B_16, A_15, D_18, E_50, C_17]: (k4_mcart_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), '#skF_2'(C_17, D_18, B_16, E_50, A_15), '#skF_3'(C_17, D_18, B_16, E_50, A_15), '#skF_4'(C_17, D_18, B_16, E_50, A_15))=E_50 | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.18/1.94  tff(c_1019, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1012, c_10])).
% 4.18/1.94  tff(c_1030, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1019])).
% 4.18/1.94  tff(c_1031, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_1030])).
% 4.18/1.94  tff(c_130, plain, (![A_139, B_140, C_141, D_142]: (k4_tarski(k3_mcart_1(A_139, B_140, C_141), D_142)=k4_mcart_1(A_139, B_140, C_141, D_142))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.18/1.94  tff(c_28, plain, (![A_83, B_84]: (k1_mcart_1(k4_tarski(A_83, B_84))=A_83)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.18/1.94  tff(c_139, plain, (![A_139, B_140, C_141, D_142]: (k1_mcart_1(k4_mcart_1(A_139, B_140, C_141, D_142))=k3_mcart_1(A_139, B_140, C_141))), inference(superposition, [status(thm), theory('equality')], [c_130, c_28])).
% 4.18/1.94  tff(c_1043, plain, (k3_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))=k1_mcart_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1031, c_139])).
% 4.18/1.94  tff(c_63, plain, (![A_119, B_120, C_121]: (k4_tarski(k4_tarski(A_119, B_120), C_121)=k3_mcart_1(A_119, B_120, C_121))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.18/1.94  tff(c_72, plain, (![A_119, B_120, C_121]: (k1_mcart_1(k3_mcart_1(A_119, B_120, C_121))=k4_tarski(A_119, B_120))), inference(superposition, [status(thm), theory('equality')], [c_63, c_28])).
% 4.18/1.94  tff(c_1092, plain, (k4_tarski('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')=k1_mcart_1(k1_mcart_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_72])).
% 4.18/1.94  tff(c_30, plain, (![A_83, B_84]: (k2_mcart_1(k4_tarski(A_83, B_84))=B_84)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.18/1.94  tff(c_1119, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1092, c_30])).
% 4.18/1.94  tff(c_462, plain, (![B_234, A_233, D_232, C_235, E_236]: (k9_mcart_1(A_233, B_234, C_235, D_232, E_236)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_236))) | ~m1_subset_1(E_236, k4_zfmisc_1(A_233, B_234, C_235, D_232)) | k1_xboole_0=D_232 | k1_xboole_0=C_235 | k1_xboole_0=B_234 | k1_xboole_0=A_233)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.18/1.94  tff(c_480, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_462])).
% 4.18/1.94  tff(c_487, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_480])).
% 4.18/1.94  tff(c_1127, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_487])).
% 4.18/1.94  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1127])).
% 4.18/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.94  
% 4.18/1.94  Inference rules
% 4.18/1.94  ----------------------
% 4.18/1.94  #Ref     : 0
% 4.18/1.94  #Sup     : 257
% 4.18/1.94  #Fact    : 0
% 4.18/1.94  #Define  : 0
% 4.18/1.94  #Split   : 0
% 4.18/1.94  #Chain   : 0
% 4.18/1.94  #Close   : 0
% 4.18/1.94  
% 4.18/1.94  Ordering : KBO
% 4.18/1.94  
% 4.18/1.94  Simplification rules
% 4.18/1.94  ----------------------
% 4.18/1.94  #Subsume      : 24
% 4.18/1.94  #Demod        : 169
% 4.18/1.94  #Tautology    : 93
% 4.18/1.94  #SimpNegUnit  : 13
% 4.18/1.94  #BackRed      : 3
% 4.18/1.94  
% 4.18/1.94  #Partial instantiations: 0
% 4.18/1.94  #Strategies tried      : 1
% 4.18/1.94  
% 4.18/1.94  Timing (in seconds)
% 4.18/1.94  ----------------------
% 4.18/1.94  Preprocessing        : 0.39
% 4.18/1.94  Parsing              : 0.22
% 4.18/1.94  CNF conversion       : 0.03
% 4.18/1.94  Main loop            : 0.63
% 4.18/1.94  Inferencing          : 0.25
% 4.18/1.94  Reduction            : 0.19
% 4.18/1.94  Demodulation         : 0.14
% 4.18/1.95  BG Simplification    : 0.05
% 4.18/1.95  Subsumption          : 0.09
% 4.18/1.95  Abstraction          : 0.07
% 4.18/1.95  MUC search           : 0.00
% 4.18/1.95  Cooper               : 0.00
% 4.18/1.95  Total                : 1.05
% 4.18/1.95  Index Insertion      : 0.00
% 4.18/1.95  Index Deletion       : 0.00
% 4.18/1.95  Index Matching       : 0.00
% 4.18/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
