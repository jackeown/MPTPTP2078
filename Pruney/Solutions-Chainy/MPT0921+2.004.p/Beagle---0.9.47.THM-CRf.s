%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:18 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  187 ( 571 expanded)
%              Number of equality atoms :  133 ( 360 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(c_32,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
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
    ! [I_112,G_100,H_108,J_114] :
      ( I_112 = '#skF_9'
      | k4_mcart_1(G_100,H_108,I_112,J_114) != '#skF_10'
      | ~ m1_subset_1(J_114,'#skF_8')
      | ~ m1_subset_1(I_112,'#skF_7')
      | ~ m1_subset_1(H_108,'#skF_6')
      | ~ m1_subset_1(G_100,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_590,plain,(
    ! [E_255,C_252,D_256,B_254,A_253] :
      ( '#skF_3'(C_252,D_256,B_254,E_255,A_253) = '#skF_9'
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
    inference(resolution,[status(thm)],[c_16,c_590])).

tff(c_842,plain,(
    ! [C_309,D_310,E_311,A_312] :
      ( '#skF_3'(C_309,D_310,'#skF_6',E_311,A_312) = '#skF_9'
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
      ( '#skF_3'(C_17,'#skF_8','#skF_6',E_50,A_15) = '#skF_9'
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
      ( '#skF_3'(C_342,'#skF_8','#skF_6',E_343,A_344) = '#skF_9'
      | E_343 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_342,'#skF_8','#skF_6',E_343,A_344),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_342,'#skF_8','#skF_6',E_343,A_344),'#skF_5')
      | ~ m1_subset_1(E_343,k4_zfmisc_1(A_344,'#skF_6',C_342,'#skF_8'))
      | k1_xboole_0 = C_342
      | k1_xboole_0 = A_344 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_34,c_846])).

tff(c_974,plain,(
    ! [E_50,A_15] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_50,A_15) = '#skF_9'
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
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_345,A_346) = '#skF_9'
      | E_345 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_345,A_346),'#skF_5')
      | ~ m1_subset_1(E_345,k4_zfmisc_1(A_346,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_346 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_36,c_974])).

tff(c_983,plain,(
    ! [E_50] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_50,'#skF_5') = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_979])).

tff(c_988,plain,(
    ! [E_347] :
      ( '#skF_3'('#skF_7','#skF_8','#skF_6',E_347,'#skF_5') = '#skF_9'
      | E_347 != '#skF_10'
      | ~ m1_subset_1(E_347,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_40,c_983])).

tff(c_1012,plain,(
    '#skF_3'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') = '#skF_9' ),
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
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_10])).

tff(c_1030,plain,
    ( k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1019])).

tff(c_1031,plain,(
    k4_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9','#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')) = '#skF_10' ),
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
    k3_mcart_1('#skF_1'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_2'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5'),'#skF_9') = k1_mcart_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_139])).

tff(c_63,plain,(
    ! [A_119,B_120,C_121] : k4_tarski(k4_tarski(A_119,B_120),C_121) = k3_mcart_1(A_119,B_120,C_121) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_83,B_84] : k2_mcart_1(k4_tarski(A_83,B_84)) = B_84 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_75,plain,(
    ! [A_119,B_120,C_121] : k2_mcart_1(k3_mcart_1(A_119,B_120,C_121)) = C_121 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_30])).

tff(c_1095,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_75])).

tff(c_425,plain,(
    ! [D_227,A_228,C_230,B_229,E_231] :
      ( k2_mcart_1(k1_mcart_1(E_231)) = k10_mcart_1(A_228,B_229,C_230,D_227,E_231)
      | ~ m1_subset_1(E_231,k4_zfmisc_1(A_228,B_229,C_230,D_227))
      | k1_xboole_0 = D_227
      | k1_xboole_0 = C_230
      | k1_xboole_0 = B_229
      | k1_xboole_0 = A_228 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_450,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_425])).

tff(c_457,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_450])).

tff(c_1099,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_457])).

tff(c_1101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.62  
% 3.85/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.62  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.85/1.62  
% 3.85/1.62  %Foreground sorts:
% 3.85/1.62  
% 3.85/1.62  
% 3.85/1.62  %Background operators:
% 3.85/1.62  
% 3.85/1.62  
% 3.85/1.62  %Foreground operators:
% 3.85/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.85/1.62  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.85/1.62  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.85/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.85/1.62  tff('#skF_10', type, '#skF_10': $i).
% 3.85/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.62  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.85/1.62  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.85/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.85/1.62  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.62  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.85/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.62  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.85/1.62  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.62  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.85/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.62  
% 3.85/1.64  tff(f_122, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 3.85/1.64  tff(f_64, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.85/1.64  tff(f_31, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.85/1.64  tff(f_93, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.85/1.64  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.85/1.64  tff(f_89, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.85/1.64  tff(c_32, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_34, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_44, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_18, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), A_15) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.64  tff(c_14, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_3'(C_17, D_18, B_16, E_50, A_15), C_17) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.64  tff(c_12, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_4'(C_17, D_18, B_16, E_50, A_15), D_18) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.64  tff(c_16, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_2'(C_17, D_18, B_16, E_50, A_15), B_16) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.64  tff(c_526, plain, (![A_246, E_245, D_243, B_244, C_242]: (k4_mcart_1('#skF_1'(C_242, D_243, B_244, E_245, A_246), '#skF_2'(C_242, D_243, B_244, E_245, A_246), '#skF_3'(C_242, D_243, B_244, E_245, A_246), '#skF_4'(C_242, D_243, B_244, E_245, A_246))=E_245 | ~m1_subset_1(E_245, k4_zfmisc_1(A_246, B_244, C_242, D_243)) | k1_xboole_0=D_243 | k1_xboole_0=C_242 | k1_xboole_0=B_244 | k1_xboole_0=A_246)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.64  tff(c_42, plain, (![I_112, G_100, H_108, J_114]: (I_112='#skF_9' | k4_mcart_1(G_100, H_108, I_112, J_114)!='#skF_10' | ~m1_subset_1(J_114, '#skF_8') | ~m1_subset_1(I_112, '#skF_7') | ~m1_subset_1(H_108, '#skF_6') | ~m1_subset_1(G_100, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_590, plain, (![E_255, C_252, D_256, B_254, A_253]: ('#skF_3'(C_252, D_256, B_254, E_255, A_253)='#skF_9' | E_255!='#skF_10' | ~m1_subset_1('#skF_4'(C_252, D_256, B_254, E_255, A_253), '#skF_8') | ~m1_subset_1('#skF_3'(C_252, D_256, B_254, E_255, A_253), '#skF_7') | ~m1_subset_1('#skF_2'(C_252, D_256, B_254, E_255, A_253), '#skF_6') | ~m1_subset_1('#skF_1'(C_252, D_256, B_254, E_255, A_253), '#skF_5') | ~m1_subset_1(E_255, k4_zfmisc_1(A_253, B_254, C_252, D_256)) | k1_xboole_0=D_256 | k1_xboole_0=C_252 | k1_xboole_0=B_254 | k1_xboole_0=A_253)), inference(superposition, [status(thm), theory('equality')], [c_526, c_42])).
% 3.85/1.64  tff(c_594, plain, (![C_17, D_18, E_50, A_15]: ('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_8') | ~m1_subset_1('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_16, c_590])).
% 3.85/1.64  tff(c_842, plain, (![C_309, D_310, E_311, A_312]: ('#skF_3'(C_309, D_310, '#skF_6', E_311, A_312)='#skF_9' | E_311!='#skF_10' | ~m1_subset_1('#skF_4'(C_309, D_310, '#skF_6', E_311, A_312), '#skF_8') | ~m1_subset_1('#skF_3'(C_309, D_310, '#skF_6', E_311, A_312), '#skF_7') | ~m1_subset_1('#skF_1'(C_309, D_310, '#skF_6', E_311, A_312), '#skF_5') | ~m1_subset_1(E_311, k4_zfmisc_1(A_312, '#skF_6', C_309, D_310)) | k1_xboole_0=D_310 | k1_xboole_0=C_309 | k1_xboole_0=A_312)), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_594])).
% 3.85/1.64  tff(c_846, plain, (![C_17, E_50, A_15]: ('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_842])).
% 3.85/1.64  tff(c_970, plain, (![C_342, E_343, A_344]: ('#skF_3'(C_342, '#skF_8', '#skF_6', E_343, A_344)='#skF_9' | E_343!='#skF_10' | ~m1_subset_1('#skF_3'(C_342, '#skF_8', '#skF_6', E_343, A_344), '#skF_7') | ~m1_subset_1('#skF_1'(C_342, '#skF_8', '#skF_6', E_343, A_344), '#skF_5') | ~m1_subset_1(E_343, k4_zfmisc_1(A_344, '#skF_6', C_342, '#skF_8')) | k1_xboole_0=C_342 | k1_xboole_0=A_344)), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_34, c_846])).
% 3.85/1.64  tff(c_974, plain, (![E_50, A_15]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_970])).
% 3.85/1.64  tff(c_979, plain, (![E_345, A_346]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_345, A_346)='#skF_9' | E_345!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_345, A_346), '#skF_5') | ~m1_subset_1(E_345, k4_zfmisc_1(A_346, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_346)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_36, c_974])).
% 3.85/1.64  tff(c_983, plain, (![E_50]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_50, '#skF_5')='#skF_9' | E_50!='#skF_10' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_18, c_979])).
% 3.85/1.64  tff(c_988, plain, (![E_347]: ('#skF_3'('#skF_7', '#skF_8', '#skF_6', E_347, '#skF_5')='#skF_9' | E_347!='#skF_10' | ~m1_subset_1(E_347, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_40, c_983])).
% 3.85/1.64  tff(c_1012, plain, ('#skF_3'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_44, c_988])).
% 3.85/1.64  tff(c_10, plain, (![B_16, A_15, D_18, E_50, C_17]: (k4_mcart_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), '#skF_2'(C_17, D_18, B_16, E_50, A_15), '#skF_3'(C_17, D_18, B_16, E_50, A_15), '#skF_4'(C_17, D_18, B_16, E_50, A_15))=E_50 | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.64  tff(c_1019, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1012, c_10])).
% 3.85/1.64  tff(c_1030, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1019])).
% 3.85/1.64  tff(c_1031, plain, (k4_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9', '#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_1030])).
% 3.85/1.64  tff(c_130, plain, (![A_139, B_140, C_141, D_142]: (k4_tarski(k3_mcart_1(A_139, B_140, C_141), D_142)=k4_mcart_1(A_139, B_140, C_141, D_142))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.64  tff(c_28, plain, (![A_83, B_84]: (k1_mcart_1(k4_tarski(A_83, B_84))=A_83)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.85/1.64  tff(c_139, plain, (![A_139, B_140, C_141, D_142]: (k1_mcart_1(k4_mcart_1(A_139, B_140, C_141, D_142))=k3_mcart_1(A_139, B_140, C_141))), inference(superposition, [status(thm), theory('equality')], [c_130, c_28])).
% 3.85/1.64  tff(c_1043, plain, (k3_mcart_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_2'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5'), '#skF_9')=k1_mcart_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1031, c_139])).
% 3.85/1.64  tff(c_63, plain, (![A_119, B_120, C_121]: (k4_tarski(k4_tarski(A_119, B_120), C_121)=k3_mcart_1(A_119, B_120, C_121))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.64  tff(c_30, plain, (![A_83, B_84]: (k2_mcart_1(k4_tarski(A_83, B_84))=B_84)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.85/1.64  tff(c_75, plain, (![A_119, B_120, C_121]: (k2_mcart_1(k3_mcart_1(A_119, B_120, C_121))=C_121)), inference(superposition, [status(thm), theory('equality')], [c_63, c_30])).
% 3.85/1.64  tff(c_1095, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1043, c_75])).
% 3.85/1.64  tff(c_425, plain, (![D_227, A_228, C_230, B_229, E_231]: (k2_mcart_1(k1_mcart_1(E_231))=k10_mcart_1(A_228, B_229, C_230, D_227, E_231) | ~m1_subset_1(E_231, k4_zfmisc_1(A_228, B_229, C_230, D_227)) | k1_xboole_0=D_227 | k1_xboole_0=C_230 | k1_xboole_0=B_229 | k1_xboole_0=A_228)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.85/1.64  tff(c_450, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_425])).
% 3.85/1.64  tff(c_457, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_450])).
% 3.85/1.64  tff(c_1099, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_457])).
% 3.85/1.64  tff(c_1101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1099])).
% 3.85/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.64  
% 3.85/1.64  Inference rules
% 3.85/1.64  ----------------------
% 3.85/1.64  #Ref     : 0
% 3.85/1.64  #Sup     : 246
% 3.85/1.64  #Fact    : 0
% 3.85/1.64  #Define  : 0
% 3.85/1.64  #Split   : 0
% 3.85/1.64  #Chain   : 0
% 3.85/1.64  #Close   : 0
% 3.85/1.64  
% 3.85/1.64  Ordering : KBO
% 3.85/1.64  
% 3.85/1.64  Simplification rules
% 3.85/1.64  ----------------------
% 3.85/1.64  #Subsume      : 24
% 3.85/1.64  #Demod        : 168
% 3.85/1.64  #Tautology    : 87
% 3.85/1.64  #SimpNegUnit  : 13
% 3.85/1.64  #BackRed      : 2
% 3.85/1.64  
% 3.85/1.64  #Partial instantiations: 0
% 3.85/1.64  #Strategies tried      : 1
% 3.85/1.64  
% 3.85/1.64  Timing (in seconds)
% 3.85/1.64  ----------------------
% 3.85/1.64  Preprocessing        : 0.33
% 3.85/1.64  Parsing              : 0.17
% 3.85/1.64  CNF conversion       : 0.03
% 3.85/1.64  Main loop            : 0.56
% 3.85/1.64  Inferencing          : 0.22
% 3.85/1.64  Reduction            : 0.17
% 3.85/1.64  Demodulation         : 0.13
% 3.85/1.64  BG Simplification    : 0.04
% 3.85/1.64  Subsumption          : 0.08
% 3.85/1.64  Abstraction          : 0.06
% 3.85/1.64  MUC search           : 0.00
% 3.85/1.64  Cooper               : 0.00
% 3.85/1.64  Total                : 0.92
% 3.85/1.64  Index Insertion      : 0.00
% 3.85/1.65  Index Deletion       : 0.00
% 3.85/1.65  Index Matching       : 0.00
% 3.85/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
