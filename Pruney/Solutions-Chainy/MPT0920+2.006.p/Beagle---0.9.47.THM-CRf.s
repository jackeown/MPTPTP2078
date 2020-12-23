%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:17 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
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

tff(c_245,plain,(
    ! [B_250,C_253,A_251,E_254,D_252] :
      ( k4_mcart_1('#skF_1'(B_250,A_251,D_252,C_253,E_254),'#skF_2'(B_250,A_251,D_252,C_253,E_254),'#skF_3'(B_250,A_251,D_252,C_253,E_254),'#skF_4'(B_250,A_251,D_252,C_253,E_254)) = E_254
      | ~ m1_subset_1(E_254,k4_zfmisc_1(A_251,B_250,C_253,D_252))
      | k1_xboole_0 = D_252
      | k1_xboole_0 = C_253
      | k1_xboole_0 = B_250
      | k1_xboole_0 = A_251 ) ),
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

tff(c_320,plain,(
    ! [A_289,C_285,E_287,B_288,D_286] :
      ( '#skF_2'(B_288,A_289,D_286,C_285,E_287) = '#skF_9'
      | E_287 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(B_288,A_289,D_286,C_285,E_287),'#skF_8')
      | ~ m1_subset_1('#skF_3'(B_288,A_289,D_286,C_285,E_287),'#skF_7')
      | ~ m1_subset_1('#skF_2'(B_288,A_289,D_286,C_285,E_287),'#skF_6')
      | ~ m1_subset_1('#skF_1'(B_288,A_289,D_286,C_285,E_287),'#skF_5')
      | ~ m1_subset_1(E_287,k4_zfmisc_1(A_289,B_288,C_285,D_286))
      | k1_xboole_0 = D_286
      | k1_xboole_0 = C_285
      | k1_xboole_0 = B_288
      | k1_xboole_0 = A_289 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_36])).

tff(c_324,plain,(
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
    inference(resolution,[status(thm)],[c_14,c_320])).

tff(c_329,plain,(
    ! [A_290,D_291,C_292,E_293] :
      ( '#skF_2'('#skF_6',A_290,D_291,C_292,E_293) = '#skF_9'
      | E_293 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_6',A_290,D_291,C_292,E_293),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',A_290,D_291,C_292,E_293),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_290,D_291,C_292,E_293),'#skF_5')
      | ~ m1_subset_1(E_293,k4_zfmisc_1(A_290,'#skF_6',C_292,D_291))
      | k1_xboole_0 = D_291
      | k1_xboole_0 = C_292
      | k1_xboole_0 = A_290 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_324])).

tff(c_333,plain,(
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
    inference(resolution,[status(thm)],[c_10,c_329])).

tff(c_354,plain,(
    ! [A_303,C_304,E_305] :
      ( '#skF_2'('#skF_6',A_303,'#skF_8',C_304,E_305) = '#skF_9'
      | E_305 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_6',A_303,'#skF_8',C_304,E_305),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_303,'#skF_8',C_304,E_305),'#skF_5')
      | ~ m1_subset_1(E_305,k4_zfmisc_1(A_303,'#skF_6',C_304,'#skF_8'))
      | k1_xboole_0 = C_304
      | k1_xboole_0 = A_303 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_28,c_333])).

tff(c_358,plain,(
    ! [A_12,E_47] :
      ( '#skF_2'('#skF_6',A_12,'#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,'#skF_8','#skF_7',E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_12,c_354])).

tff(c_363,plain,(
    ! [A_306,E_307] :
      ( '#skF_2'('#skF_6',A_306,'#skF_8','#skF_7',E_307) = '#skF_9'
      | E_307 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_306,'#skF_8','#skF_7',E_307),'#skF_5')
      | ~ m1_subset_1(E_307,k4_zfmisc_1(A_306,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_306 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_30,c_358])).

tff(c_367,plain,(
    ! [E_47] :
      ( '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1(E_47,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_16,c_363])).

tff(c_372,plain,(
    ! [E_308] :
      ( '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7',E_308) = '#skF_9'
      | E_308 != '#skF_10'
      | ~ m1_subset_1(E_308,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_34,c_367])).

tff(c_396,plain,(
    '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38,c_372])).

tff(c_8,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( k4_mcart_1('#skF_1'(B_13,A_12,D_15,C_14,E_47),'#skF_2'(B_13,A_12,D_15,C_14,E_47),'#skF_3'(B_13,A_12,D_15,C_14,E_47),'#skF_4'(B_13,A_12,D_15,C_14,E_47)) = E_47
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_406,plain,
    ( k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_8])).

tff(c_420,plain,
    ( k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_406])).

tff(c_421,plain,(
    k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_420])).

tff(c_22,plain,(
    ! [A_74,D_77,B_75,I_86,H_85,C_76,G_84,F_83] :
      ( k9_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_83,G_84,H_85,I_86)) = G_84
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74
      | ~ m1_subset_1(k4_mcart_1(F_83,G_84,H_85,I_86),k4_zfmisc_1(A_74,B_75,C_76,D_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_459,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k9_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'))) = '#skF_9'
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_74,B_75,C_76,D_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_22])).

tff(c_484,plain,(
    ! [A_309,B_310,C_311,D_312] :
      ( k9_mcart_1(A_309,B_310,C_311,D_312,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_312
      | k1_xboole_0 = C_311
      | k1_xboole_0 = B_310
      | k1_xboole_0 = A_309
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_309,B_310,C_311,D_312)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_459])).

tff(c_493,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_484])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_26,c_493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.77/1.43  
% 2.77/1.43  %Foreground sorts:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Background operators:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Foreground operators:
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.43  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.77/1.43  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.77/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.43  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.77/1.43  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.77/1.43  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.43  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.77/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.43  
% 2.77/1.44  tff(f_118, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_mcart_1)).
% 2.77/1.44  tff(f_62, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 2.77/1.44  tff(f_89, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.77/1.44  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_30, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_28, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_26, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_38, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_16, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), A_12) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.44  tff(c_12, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_3'(B_13, A_12, D_15, C_14, E_47), C_14) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.44  tff(c_10, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_4'(B_13, A_12, D_15, C_14, E_47), D_15) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.44  tff(c_14, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_2'(B_13, A_12, D_15, C_14, E_47), B_13) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.44  tff(c_245, plain, (![B_250, C_253, A_251, E_254, D_252]: (k4_mcart_1('#skF_1'(B_250, A_251, D_252, C_253, E_254), '#skF_2'(B_250, A_251, D_252, C_253, E_254), '#skF_3'(B_250, A_251, D_252, C_253, E_254), '#skF_4'(B_250, A_251, D_252, C_253, E_254))=E_254 | ~m1_subset_1(E_254, k4_zfmisc_1(A_251, B_250, C_253, D_252)) | k1_xboole_0=D_252 | k1_xboole_0=C_253 | k1_xboole_0=B_250 | k1_xboole_0=A_251)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.44  tff(c_36, plain, (![H_110, G_102, I_114, J_116]: (H_110='#skF_9' | k4_mcart_1(G_102, H_110, I_114, J_116)!='#skF_10' | ~m1_subset_1(J_116, '#skF_8') | ~m1_subset_1(I_114, '#skF_7') | ~m1_subset_1(H_110, '#skF_6') | ~m1_subset_1(G_102, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.77/1.44  tff(c_320, plain, (![A_289, C_285, E_287, B_288, D_286]: ('#skF_2'(B_288, A_289, D_286, C_285, E_287)='#skF_9' | E_287!='#skF_10' | ~m1_subset_1('#skF_4'(B_288, A_289, D_286, C_285, E_287), '#skF_8') | ~m1_subset_1('#skF_3'(B_288, A_289, D_286, C_285, E_287), '#skF_7') | ~m1_subset_1('#skF_2'(B_288, A_289, D_286, C_285, E_287), '#skF_6') | ~m1_subset_1('#skF_1'(B_288, A_289, D_286, C_285, E_287), '#skF_5') | ~m1_subset_1(E_287, k4_zfmisc_1(A_289, B_288, C_285, D_286)) | k1_xboole_0=D_286 | k1_xboole_0=C_285 | k1_xboole_0=B_288 | k1_xboole_0=A_289)), inference(superposition, [status(thm), theory('equality')], [c_245, c_36])).
% 2.77/1.44  tff(c_324, plain, (![A_12, D_15, C_14, E_47]: ('#skF_2'('#skF_6', A_12, D_15, C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_12, D_15, C_14, E_47), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_12, D_15, C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, D_15, C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_14, c_320])).
% 2.77/1.44  tff(c_329, plain, (![A_290, D_291, C_292, E_293]: ('#skF_2'('#skF_6', A_290, D_291, C_292, E_293)='#skF_9' | E_293!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_290, D_291, C_292, E_293), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_290, D_291, C_292, E_293), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_290, D_291, C_292, E_293), '#skF_5') | ~m1_subset_1(E_293, k4_zfmisc_1(A_290, '#skF_6', C_292, D_291)) | k1_xboole_0=D_291 | k1_xboole_0=C_292 | k1_xboole_0=A_290)), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_324])).
% 2.77/1.44  tff(c_333, plain, (![A_12, C_14, E_47]: ('#skF_2'('#skF_6', A_12, '#skF_8', C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_10, c_329])).
% 2.77/1.44  tff(c_354, plain, (![A_303, C_304, E_305]: ('#skF_2'('#skF_6', A_303, '#skF_8', C_304, E_305)='#skF_9' | E_305!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_303, '#skF_8', C_304, E_305), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_303, '#skF_8', C_304, E_305), '#skF_5') | ~m1_subset_1(E_305, k4_zfmisc_1(A_303, '#skF_6', C_304, '#skF_8')) | k1_xboole_0=C_304 | k1_xboole_0=A_303)), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_28, c_333])).
% 2.77/1.44  tff(c_358, plain, (![A_12, E_47]: ('#skF_2'('#skF_6', A_12, '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', '#skF_7', E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_12, c_354])).
% 2.77/1.44  tff(c_363, plain, (![A_306, E_307]: ('#skF_2'('#skF_6', A_306, '#skF_8', '#skF_7', E_307)='#skF_9' | E_307!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_306, '#skF_8', '#skF_7', E_307), '#skF_5') | ~m1_subset_1(E_307, k4_zfmisc_1(A_306, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_306)), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_30, c_358])).
% 2.77/1.44  tff(c_367, plain, (![E_47]: ('#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1(E_47, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_16, c_363])).
% 2.77/1.44  tff(c_372, plain, (![E_308]: ('#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_308)='#skF_9' | E_308!='#skF_10' | ~m1_subset_1(E_308, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_34, c_367])).
% 2.77/1.44  tff(c_396, plain, ('#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_38, c_372])).
% 2.77/1.44  tff(c_8, plain, (![D_15, E_47, C_14, A_12, B_13]: (k4_mcart_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), '#skF_2'(B_13, A_12, D_15, C_14, E_47), '#skF_3'(B_13, A_12, D_15, C_14, E_47), '#skF_4'(B_13, A_12, D_15, C_14, E_47))=E_47 | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.44  tff(c_406, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_396, c_8])).
% 2.77/1.44  tff(c_420, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_406])).
% 2.77/1.44  tff(c_421, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_420])).
% 2.77/1.44  tff(c_22, plain, (![A_74, D_77, B_75, I_86, H_85, C_76, G_84, F_83]: (k9_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_83, G_84, H_85, I_86))=G_84 | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74 | ~m1_subset_1(k4_mcart_1(F_83, G_84, H_85, I_86), k4_zfmisc_1(A_74, B_75, C_76, D_77)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.44  tff(c_459, plain, (![A_74, B_75, C_76, D_77]: (k9_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')))='#skF_9' | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_74, B_75, C_76, D_77)))), inference(superposition, [status(thm), theory('equality')], [c_421, c_22])).
% 2.77/1.44  tff(c_484, plain, (![A_309, B_310, C_311, D_312]: (k9_mcart_1(A_309, B_310, C_311, D_312, '#skF_10')='#skF_9' | k1_xboole_0=D_312 | k1_xboole_0=C_311 | k1_xboole_0=B_310 | k1_xboole_0=A_309 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_309, B_310, C_311, D_312)))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_459])).
% 2.77/1.44  tff(c_493, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_484])).
% 2.77/1.44  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_493])).
% 2.77/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  Inference rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Ref     : 0
% 2.77/1.44  #Sup     : 103
% 2.77/1.44  #Fact    : 0
% 2.77/1.44  #Define  : 0
% 2.77/1.44  #Split   : 0
% 2.77/1.44  #Chain   : 0
% 2.77/1.44  #Close   : 0
% 2.77/1.44  
% 2.77/1.44  Ordering : KBO
% 2.77/1.44  
% 2.77/1.44  Simplification rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Subsume      : 16
% 2.77/1.44  #Demod        : 92
% 2.77/1.44  #Tautology    : 34
% 2.77/1.44  #SimpNegUnit  : 9
% 2.77/1.44  #BackRed      : 0
% 2.77/1.44  
% 2.77/1.44  #Partial instantiations: 0
% 2.77/1.44  #Strategies tried      : 1
% 2.77/1.44  
% 2.77/1.44  Timing (in seconds)
% 2.77/1.44  ----------------------
% 2.77/1.45  Preprocessing        : 0.34
% 2.77/1.45  Parsing              : 0.16
% 2.77/1.45  CNF conversion       : 0.03
% 2.77/1.45  Main loop            : 0.34
% 2.77/1.45  Inferencing          : 0.14
% 2.77/1.45  Reduction            : 0.10
% 2.77/1.45  Demodulation         : 0.07
% 2.77/1.45  BG Simplification    : 0.03
% 2.77/1.45  Subsumption          : 0.06
% 2.77/1.45  Abstraction          : 0.03
% 2.77/1.45  MUC search           : 0.00
% 2.77/1.45  Cooper               : 0.00
% 2.77/1.45  Total                : 0.71
% 2.77/1.45  Index Insertion      : 0.00
% 2.77/1.45  Index Deletion       : 0.00
% 2.77/1.45  Index Matching       : 0.00
% 2.77/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
