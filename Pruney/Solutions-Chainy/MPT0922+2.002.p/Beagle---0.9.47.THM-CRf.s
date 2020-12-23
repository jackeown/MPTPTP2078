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
% DateTime   : Thu Dec  3 10:10:19 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 564 expanded)
%              Number of equality atoms :  123 ( 353 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

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

tff(c_591,plain,(
    ! [A_258,B_256,D_255,E_257,C_254] :
      ( k4_mcart_1('#skF_1'(C_254,D_255,B_256,E_257,A_258),'#skF_2'(C_254,D_255,B_256,E_257,A_258),'#skF_3'(C_254,D_255,B_256,E_257,A_258),'#skF_4'(C_254,D_255,B_256,E_257,A_258)) = E_257
      | ~ m1_subset_1(E_257,k4_zfmisc_1(A_258,B_256,C_254,D_255))
      | k1_xboole_0 = D_255
      | k1_xboole_0 = C_254
      | k1_xboole_0 = B_256
      | k1_xboole_0 = A_258 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_130,plain,(
    ! [A_139,B_140,C_141,D_142] : k4_tarski(k3_mcart_1(A_139,B_140,C_141),D_142) = k4_mcart_1(A_139,B_140,C_141,D_142) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_83,B_84] : k2_mcart_1(k4_tarski(A_83,B_84)) = B_84 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    ! [A_139,B_140,C_141,D_142] : k2_mcart_1(k4_mcart_1(A_139,B_140,C_141,D_142)) = D_142 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_30])).

tff(c_612,plain,(
    ! [B_259,E_262,A_261,C_260,D_263] :
      ( k2_mcart_1(E_262) = '#skF_4'(C_260,D_263,B_259,E_262,A_261)
      | ~ m1_subset_1(E_262,k4_zfmisc_1(A_261,B_259,C_260,D_263))
      | k1_xboole_0 = D_263
      | k1_xboole_0 = C_260
      | k1_xboole_0 = B_259
      | k1_xboole_0 = A_261 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_142])).

tff(c_637,plain,
    ( k2_mcart_1('#skF_10') = '#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_612])).

tff(c_644,plain,(
    k2_mcart_1('#skF_10') = '#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_637])).

tff(c_370,plain,(
    ! [D_211,C_214,B_213,A_212,E_215] :
      ( k11_mcart_1(A_212,B_213,C_214,D_211,E_215) = k2_mcart_1(E_215)
      | ~ m1_subset_1(E_215,k4_zfmisc_1(A_212,B_213,C_214,D_211))
      | k1_xboole_0 = D_211
      | k1_xboole_0 = C_214
      | k1_xboole_0 = B_213
      | k1_xboole_0 = A_212 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_391,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_370])).

tff(c_397,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_391])).

tff(c_32,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_398,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_32])).

tff(c_645,plain,(
    '#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_398])).

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

tff(c_42,plain,(
    ! [J_114,G_100,H_108,I_112] :
      ( J_114 = '#skF_9'
      | k4_mcart_1(G_100,H_108,I_112,J_114) != '#skF_10'
      | ~ m1_subset_1(J_114,'#skF_8')
      | ~ m1_subset_1(I_112,'#skF_7')
      | ~ m1_subset_1(H_108,'#skF_6')
      | ~ m1_subset_1(G_100,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_686,plain,(
    ! [B_270,C_271,D_274,A_272,E_273] :
      ( '#skF_4'(C_271,D_274,B_270,E_273,A_272) = '#skF_9'
      | E_273 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_271,D_274,B_270,E_273,A_272),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_271,D_274,B_270,E_273,A_272),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_271,D_274,B_270,E_273,A_272),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_271,D_274,B_270,E_273,A_272),'#skF_5')
      | ~ m1_subset_1(E_273,k4_zfmisc_1(A_272,B_270,C_271,D_274))
      | k1_xboole_0 = D_274
      | k1_xboole_0 = C_271
      | k1_xboole_0 = B_270
      | k1_xboole_0 = A_272 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_42])).

tff(c_690,plain,(
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
    inference(resolution,[status(thm)],[c_16,c_686])).

tff(c_785,plain,(
    ! [C_294,D_295,E_296,A_297] :
      ( '#skF_4'(C_294,D_295,'#skF_6',E_296,A_297) = '#skF_9'
      | E_296 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_294,D_295,'#skF_6',E_296,A_297),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_294,D_295,'#skF_6',E_296,A_297),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_294,D_295,'#skF_6',E_296,A_297),'#skF_5')
      | ~ m1_subset_1(E_296,k4_zfmisc_1(A_297,'#skF_6',C_294,D_295))
      | k1_xboole_0 = D_295
      | k1_xboole_0 = C_294
      | k1_xboole_0 = A_297 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_690])).

tff(c_789,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_785])).

tff(c_943,plain,(
    ! [C_334,E_335,A_336] :
      ( '#skF_4'(C_334,'#skF_8','#skF_6',E_335,A_336) = '#skF_9'
      | E_335 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(C_334,'#skF_8','#skF_6',E_335,A_336),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_334,'#skF_8','#skF_6',E_335,A_336),'#skF_5')
      | ~ m1_subset_1(E_335,k4_zfmisc_1(A_336,'#skF_6',C_334,'#skF_8'))
      | k1_xboole_0 = C_334
      | k1_xboole_0 = A_336 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_34,c_789])).

tff(c_947,plain,(
    ! [E_50,A_15] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_50,A_15) = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_50,A_15),'#skF_5')
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_15,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_14,c_943])).

tff(c_952,plain,(
    ! [E_337,A_338] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_337,A_338) = '#skF_9'
      | E_337 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_6',E_337,A_338),'#skF_5')
      | ~ m1_subset_1(E_337,k4_zfmisc_1(A_338,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_338 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_36,c_947])).

tff(c_956,plain,(
    ! [E_50] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_50,'#skF_5') = '#skF_9'
      | E_50 != '#skF_10'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_952])).

tff(c_961,plain,(
    ! [E_339] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_6',E_339,'#skF_5') = '#skF_9'
      | E_339 != '#skF_10'
      | ~ m1_subset_1(E_339,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_40,c_956])).

tff(c_980,plain,(
    '#skF_4'('#skF_7','#skF_8','#skF_6','#skF_10','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_44,c_961])).

tff(c_988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.59  
% 3.54/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.59  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.54/1.59  
% 3.54/1.59  %Foreground sorts:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Background operators:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Foreground operators:
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.54/1.59  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.54/1.59  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.59  tff('#skF_10', type, '#skF_10': $i).
% 3.54/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.59  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.54/1.59  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.54/1.59  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.59  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.54/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.59  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.54/1.59  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.59  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.54/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.59  
% 3.54/1.61  tff(f_122, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_mcart_1)).
% 3.54/1.61  tff(f_64, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.54/1.61  tff(f_31, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.54/1.61  tff(f_93, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.54/1.61  tff(f_89, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.54/1.61  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_34, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_44, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_591, plain, (![A_258, B_256, D_255, E_257, C_254]: (k4_mcart_1('#skF_1'(C_254, D_255, B_256, E_257, A_258), '#skF_2'(C_254, D_255, B_256, E_257, A_258), '#skF_3'(C_254, D_255, B_256, E_257, A_258), '#skF_4'(C_254, D_255, B_256, E_257, A_258))=E_257 | ~m1_subset_1(E_257, k4_zfmisc_1(A_258, B_256, C_254, D_255)) | k1_xboole_0=D_255 | k1_xboole_0=C_254 | k1_xboole_0=B_256 | k1_xboole_0=A_258)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.61  tff(c_130, plain, (![A_139, B_140, C_141, D_142]: (k4_tarski(k3_mcart_1(A_139, B_140, C_141), D_142)=k4_mcart_1(A_139, B_140, C_141, D_142))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.61  tff(c_30, plain, (![A_83, B_84]: (k2_mcart_1(k4_tarski(A_83, B_84))=B_84)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.54/1.61  tff(c_142, plain, (![A_139, B_140, C_141, D_142]: (k2_mcart_1(k4_mcart_1(A_139, B_140, C_141, D_142))=D_142)), inference(superposition, [status(thm), theory('equality')], [c_130, c_30])).
% 3.54/1.61  tff(c_612, plain, (![B_259, E_262, A_261, C_260, D_263]: (k2_mcart_1(E_262)='#skF_4'(C_260, D_263, B_259, E_262, A_261) | ~m1_subset_1(E_262, k4_zfmisc_1(A_261, B_259, C_260, D_263)) | k1_xboole_0=D_263 | k1_xboole_0=C_260 | k1_xboole_0=B_259 | k1_xboole_0=A_261)), inference(superposition, [status(thm), theory('equality')], [c_591, c_142])).
% 3.54/1.61  tff(c_637, plain, (k2_mcart_1('#skF_10')='#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_612])).
% 3.54/1.61  tff(c_644, plain, (k2_mcart_1('#skF_10')='#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_637])).
% 3.54/1.61  tff(c_370, plain, (![D_211, C_214, B_213, A_212, E_215]: (k11_mcart_1(A_212, B_213, C_214, D_211, E_215)=k2_mcart_1(E_215) | ~m1_subset_1(E_215, k4_zfmisc_1(A_212, B_213, C_214, D_211)) | k1_xboole_0=D_211 | k1_xboole_0=C_214 | k1_xboole_0=B_213 | k1_xboole_0=A_212)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.54/1.61  tff(c_391, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_370])).
% 3.54/1.61  tff(c_397, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_391])).
% 3.54/1.61  tff(c_32, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_398, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_397, c_32])).
% 3.54/1.61  tff(c_645, plain, ('#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_644, c_398])).
% 3.54/1.61  tff(c_18, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_1'(C_17, D_18, B_16, E_50, A_15), A_15) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.61  tff(c_14, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_3'(C_17, D_18, B_16, E_50, A_15), C_17) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.61  tff(c_12, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_4'(C_17, D_18, B_16, E_50, A_15), D_18) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.61  tff(c_16, plain, (![B_16, A_15, D_18, E_50, C_17]: (m1_subset_1('#skF_2'(C_17, D_18, B_16, E_50, A_15), B_16) | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, B_16, C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.61  tff(c_42, plain, (![J_114, G_100, H_108, I_112]: (J_114='#skF_9' | k4_mcart_1(G_100, H_108, I_112, J_114)!='#skF_10' | ~m1_subset_1(J_114, '#skF_8') | ~m1_subset_1(I_112, '#skF_7') | ~m1_subset_1(H_108, '#skF_6') | ~m1_subset_1(G_100, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.54/1.61  tff(c_686, plain, (![B_270, C_271, D_274, A_272, E_273]: ('#skF_4'(C_271, D_274, B_270, E_273, A_272)='#skF_9' | E_273!='#skF_10' | ~m1_subset_1('#skF_4'(C_271, D_274, B_270, E_273, A_272), '#skF_8') | ~m1_subset_1('#skF_3'(C_271, D_274, B_270, E_273, A_272), '#skF_7') | ~m1_subset_1('#skF_2'(C_271, D_274, B_270, E_273, A_272), '#skF_6') | ~m1_subset_1('#skF_1'(C_271, D_274, B_270, E_273, A_272), '#skF_5') | ~m1_subset_1(E_273, k4_zfmisc_1(A_272, B_270, C_271, D_274)) | k1_xboole_0=D_274 | k1_xboole_0=C_271 | k1_xboole_0=B_270 | k1_xboole_0=A_272)), inference(superposition, [status(thm), theory('equality')], [c_591, c_42])).
% 3.54/1.61  tff(c_690, plain, (![C_17, D_18, E_50, A_15]: ('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_4'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_8') | ~m1_subset_1('#skF_3'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, D_18, '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, D_18)) | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_16, c_686])).
% 3.54/1.61  tff(c_785, plain, (![C_294, D_295, E_296, A_297]: ('#skF_4'(C_294, D_295, '#skF_6', E_296, A_297)='#skF_9' | E_296!='#skF_10' | ~m1_subset_1('#skF_4'(C_294, D_295, '#skF_6', E_296, A_297), '#skF_8') | ~m1_subset_1('#skF_3'(C_294, D_295, '#skF_6', E_296, A_297), '#skF_7') | ~m1_subset_1('#skF_1'(C_294, D_295, '#skF_6', E_296, A_297), '#skF_5') | ~m1_subset_1(E_296, k4_zfmisc_1(A_297, '#skF_6', C_294, D_295)) | k1_xboole_0=D_295 | k1_xboole_0=C_294 | k1_xboole_0=A_297)), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_690])).
% 3.54/1.61  tff(c_789, plain, (![C_17, E_50, A_15]: ('#skF_4'(C_17, '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_3'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_7') | ~m1_subset_1('#skF_1'(C_17, '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', C_17, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_17 | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_785])).
% 3.54/1.61  tff(c_943, plain, (![C_334, E_335, A_336]: ('#skF_4'(C_334, '#skF_8', '#skF_6', E_335, A_336)='#skF_9' | E_335!='#skF_10' | ~m1_subset_1('#skF_3'(C_334, '#skF_8', '#skF_6', E_335, A_336), '#skF_7') | ~m1_subset_1('#skF_1'(C_334, '#skF_8', '#skF_6', E_335, A_336), '#skF_5') | ~m1_subset_1(E_335, k4_zfmisc_1(A_336, '#skF_6', C_334, '#skF_8')) | k1_xboole_0=C_334 | k1_xboole_0=A_336)), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_34, c_789])).
% 3.54/1.61  tff(c_947, plain, (![E_50, A_15]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_50, A_15)='#skF_9' | E_50!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_50, A_15), '#skF_5') | ~m1_subset_1(E_50, k4_zfmisc_1(A_15, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_943])).
% 3.54/1.61  tff(c_952, plain, (![E_337, A_338]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_337, A_338)='#skF_9' | E_337!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_6', E_337, A_338), '#skF_5') | ~m1_subset_1(E_337, k4_zfmisc_1(A_338, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_338)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_36, c_947])).
% 3.54/1.61  tff(c_956, plain, (![E_50]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_50, '#skF_5')='#skF_9' | E_50!='#skF_10' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_18, c_952])).
% 3.54/1.61  tff(c_961, plain, (![E_339]: ('#skF_4'('#skF_7', '#skF_8', '#skF_6', E_339, '#skF_5')='#skF_9' | E_339!='#skF_10' | ~m1_subset_1(E_339, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_40, c_956])).
% 3.54/1.61  tff(c_980, plain, ('#skF_4'('#skF_7', '#skF_8', '#skF_6', '#skF_10', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_44, c_961])).
% 3.54/1.61  tff(c_988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_645, c_980])).
% 3.54/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.61  
% 3.54/1.61  Inference rules
% 3.54/1.61  ----------------------
% 3.54/1.61  #Ref     : 0
% 3.82/1.61  #Sup     : 213
% 3.82/1.61  #Fact    : 0
% 3.82/1.61  #Define  : 0
% 3.82/1.61  #Split   : 0
% 3.82/1.61  #Chain   : 0
% 3.82/1.61  #Close   : 0
% 3.82/1.61  
% 3.82/1.61  Ordering : KBO
% 3.82/1.61  
% 3.82/1.61  Simplification rules
% 3.82/1.61  ----------------------
% 3.82/1.61  #Subsume      : 23
% 3.82/1.61  #Demod        : 149
% 3.82/1.61  #Tautology    : 78
% 3.82/1.61  #SimpNegUnit  : 10
% 3.82/1.61  #BackRed      : 3
% 3.82/1.61  
% 3.82/1.61  #Partial instantiations: 0
% 3.82/1.61  #Strategies tried      : 1
% 3.82/1.61  
% 3.82/1.61  Timing (in seconds)
% 3.82/1.61  ----------------------
% 3.82/1.61  Preprocessing        : 0.34
% 3.82/1.61  Parsing              : 0.17
% 3.82/1.61  CNF conversion       : 0.03
% 3.82/1.61  Main loop            : 0.50
% 3.82/1.61  Inferencing          : 0.20
% 3.82/1.61  Reduction            : 0.15
% 3.82/1.61  Demodulation         : 0.11
% 3.82/1.61  BG Simplification    : 0.04
% 3.82/1.61  Subsumption          : 0.07
% 3.82/1.61  Abstraction          : 0.06
% 3.82/1.61  MUC search           : 0.00
% 3.82/1.61  Cooper               : 0.00
% 3.82/1.61  Total                : 0.87
% 3.82/1.61  Index Insertion      : 0.00
% 3.82/1.61  Index Deletion       : 0.00
% 3.82/1.61  Index Matching       : 0.00
% 3.82/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
