%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:15 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
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

tff(f_119,negated_conjecture,(
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
                           => E = G ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

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
    ! [B_259,A_260,E_263,D_261,C_262] :
      ( k4_mcart_1('#skF_1'(B_259,A_260,D_261,C_262,E_263),'#skF_2'(B_259,A_260,D_261,C_262,E_263),'#skF_3'(B_259,A_260,D_261,C_262,E_263),'#skF_4'(B_259,A_260,D_261,C_262,E_263)) = E_263
      | ~ m1_subset_1(E_263,k4_zfmisc_1(A_260,B_259,C_262,D_261))
      | k1_xboole_0 = D_261
      | k1_xboole_0 = C_262
      | k1_xboole_0 = B_259
      | k1_xboole_0 = A_260 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [G_111,H_119,I_123,J_125] :
      ( G_111 = '#skF_9'
      | k4_mcart_1(G_111,H_119,I_123,J_125) != '#skF_10'
      | ~ m1_subset_1(J_125,'#skF_8')
      | ~ m1_subset_1(I_123,'#skF_7')
      | ~ m1_subset_1(H_119,'#skF_6')
      | ~ m1_subset_1(G_111,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_320,plain,(
    ! [B_296,A_294,E_298,C_295,D_297] :
      ( '#skF_1'(B_296,A_294,D_297,C_295,E_298) = '#skF_9'
      | E_298 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(B_296,A_294,D_297,C_295,E_298),'#skF_8')
      | ~ m1_subset_1('#skF_3'(B_296,A_294,D_297,C_295,E_298),'#skF_7')
      | ~ m1_subset_1('#skF_2'(B_296,A_294,D_297,C_295,E_298),'#skF_6')
      | ~ m1_subset_1('#skF_1'(B_296,A_294,D_297,C_295,E_298),'#skF_5')
      | ~ m1_subset_1(E_298,k4_zfmisc_1(A_294,B_296,C_295,D_297))
      | k1_xboole_0 = D_297
      | k1_xboole_0 = C_295
      | k1_xboole_0 = B_296
      | k1_xboole_0 = A_294 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_36])).

tff(c_324,plain,(
    ! [A_12,D_15,C_14,E_47] :
      ( '#skF_1'('#skF_6',A_12,D_15,C_14,E_47) = '#skF_9'
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
    ! [A_299,D_300,C_301,E_302] :
      ( '#skF_1'('#skF_6',A_299,D_300,C_301,E_302) = '#skF_9'
      | E_302 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_6',A_299,D_300,C_301,E_302),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',A_299,D_300,C_301,E_302),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_299,D_300,C_301,E_302),'#skF_5')
      | ~ m1_subset_1(E_302,k4_zfmisc_1(A_299,'#skF_6',C_301,D_300))
      | k1_xboole_0 = D_300
      | k1_xboole_0 = C_301
      | k1_xboole_0 = A_299 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_324])).

tff(c_333,plain,(
    ! [A_12,C_14,E_47] :
      ( '#skF_1'('#skF_6',A_12,'#skF_8',C_14,E_47) = '#skF_9'
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
    ! [A_312,C_313,E_314] :
      ( '#skF_1'('#skF_6',A_312,'#skF_8',C_313,E_314) = '#skF_9'
      | E_314 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_6',A_312,'#skF_8',C_313,E_314),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_312,'#skF_8',C_313,E_314),'#skF_5')
      | ~ m1_subset_1(E_314,k4_zfmisc_1(A_312,'#skF_6',C_313,'#skF_8'))
      | k1_xboole_0 = C_313
      | k1_xboole_0 = A_312 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_28,c_333])).

tff(c_358,plain,(
    ! [A_12,E_47] :
      ( '#skF_1'('#skF_6',A_12,'#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,'#skF_8','#skF_7',E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_12,c_354])).

tff(c_363,plain,(
    ! [A_315,E_316] :
      ( '#skF_1'('#skF_6',A_315,'#skF_8','#skF_7',E_316) = '#skF_9'
      | E_316 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_315,'#skF_8','#skF_7',E_316),'#skF_5')
      | ~ m1_subset_1(E_316,k4_zfmisc_1(A_315,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_315 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_30,c_358])).

tff(c_367,plain,(
    ! [E_47] :
      ( '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1(E_47,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_16,c_363])).

tff(c_372,plain,(
    ! [E_317] :
      ( '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7',E_317) = '#skF_9'
      | E_317 != '#skF_10'
      | ~ m1_subset_1(E_317,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_34,c_367])).

tff(c_396,plain,(
    '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10') = '#skF_9' ),
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
    ( k4_mcart_1('#skF_9','#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_8])).

tff(c_420,plain,
    ( k4_mcart_1('#skF_9','#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_406])).

tff(c_421,plain,(
    k4_mcart_1('#skF_9','#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_420])).

tff(c_24,plain,(
    ! [A_74,G_93,D_77,B_75,F_92,C_76,H_94,I_95] :
      ( k8_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_92,G_93,H_94,I_95)) = F_92
      | ~ m1_subset_1(k4_mcart_1(F_92,G_93,H_94,I_95),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_453,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k8_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1('#skF_9','#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'))) = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_24])).

tff(c_484,plain,(
    ! [A_318,B_319,C_320,D_321] :
      ( k8_mcart_1(A_318,B_319,C_320,D_321,'#skF_10') = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_318,B_319,C_320,D_321))
      | k1_xboole_0 = D_321
      | k1_xboole_0 = C_320
      | k1_xboole_0 = B_319
      | k1_xboole_0 = A_318 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_453])).

tff(c_493,plain,
    ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.44  
% 2.94/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.44  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.94/1.44  
% 2.94/1.44  %Foreground sorts:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Background operators:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Foreground operators:
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.94/1.44  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.94/1.44  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.94/1.44  tff('#skF_10', type, '#skF_10': $i).
% 2.94/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.44  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.94/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.94/1.44  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.94/1.44  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.44  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.44  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.44  
% 2.94/1.46  tff(f_119, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 2.94/1.46  tff(f_62, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 2.94/1.46  tff(f_90, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 2.94/1.46  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_30, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_28, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_26, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_38, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_16, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), A_12) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.46  tff(c_12, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_3'(B_13, A_12, D_15, C_14, E_47), C_14) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.46  tff(c_10, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_4'(B_13, A_12, D_15, C_14, E_47), D_15) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.46  tff(c_14, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_2'(B_13, A_12, D_15, C_14, E_47), B_13) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.46  tff(c_245, plain, (![B_259, A_260, E_263, D_261, C_262]: (k4_mcart_1('#skF_1'(B_259, A_260, D_261, C_262, E_263), '#skF_2'(B_259, A_260, D_261, C_262, E_263), '#skF_3'(B_259, A_260, D_261, C_262, E_263), '#skF_4'(B_259, A_260, D_261, C_262, E_263))=E_263 | ~m1_subset_1(E_263, k4_zfmisc_1(A_260, B_259, C_262, D_261)) | k1_xboole_0=D_261 | k1_xboole_0=C_262 | k1_xboole_0=B_259 | k1_xboole_0=A_260)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.46  tff(c_36, plain, (![G_111, H_119, I_123, J_125]: (G_111='#skF_9' | k4_mcart_1(G_111, H_119, I_123, J_125)!='#skF_10' | ~m1_subset_1(J_125, '#skF_8') | ~m1_subset_1(I_123, '#skF_7') | ~m1_subset_1(H_119, '#skF_6') | ~m1_subset_1(G_111, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.94/1.46  tff(c_320, plain, (![B_296, A_294, E_298, C_295, D_297]: ('#skF_1'(B_296, A_294, D_297, C_295, E_298)='#skF_9' | E_298!='#skF_10' | ~m1_subset_1('#skF_4'(B_296, A_294, D_297, C_295, E_298), '#skF_8') | ~m1_subset_1('#skF_3'(B_296, A_294, D_297, C_295, E_298), '#skF_7') | ~m1_subset_1('#skF_2'(B_296, A_294, D_297, C_295, E_298), '#skF_6') | ~m1_subset_1('#skF_1'(B_296, A_294, D_297, C_295, E_298), '#skF_5') | ~m1_subset_1(E_298, k4_zfmisc_1(A_294, B_296, C_295, D_297)) | k1_xboole_0=D_297 | k1_xboole_0=C_295 | k1_xboole_0=B_296 | k1_xboole_0=A_294)), inference(superposition, [status(thm), theory('equality')], [c_245, c_36])).
% 2.94/1.46  tff(c_324, plain, (![A_12, D_15, C_14, E_47]: ('#skF_1'('#skF_6', A_12, D_15, C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_12, D_15, C_14, E_47), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_12, D_15, C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, D_15, C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_14, c_320])).
% 2.94/1.46  tff(c_329, plain, (![A_299, D_300, C_301, E_302]: ('#skF_1'('#skF_6', A_299, D_300, C_301, E_302)='#skF_9' | E_302!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_299, D_300, C_301, E_302), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_299, D_300, C_301, E_302), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_299, D_300, C_301, E_302), '#skF_5') | ~m1_subset_1(E_302, k4_zfmisc_1(A_299, '#skF_6', C_301, D_300)) | k1_xboole_0=D_300 | k1_xboole_0=C_301 | k1_xboole_0=A_299)), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_324])).
% 2.94/1.46  tff(c_333, plain, (![A_12, C_14, E_47]: ('#skF_1'('#skF_6', A_12, '#skF_8', C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_10, c_329])).
% 2.94/1.46  tff(c_354, plain, (![A_312, C_313, E_314]: ('#skF_1'('#skF_6', A_312, '#skF_8', C_313, E_314)='#skF_9' | E_314!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_312, '#skF_8', C_313, E_314), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_312, '#skF_8', C_313, E_314), '#skF_5') | ~m1_subset_1(E_314, k4_zfmisc_1(A_312, '#skF_6', C_313, '#skF_8')) | k1_xboole_0=C_313 | k1_xboole_0=A_312)), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_28, c_333])).
% 2.94/1.46  tff(c_358, plain, (![A_12, E_47]: ('#skF_1'('#skF_6', A_12, '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', '#skF_7', E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_12, c_354])).
% 2.94/1.46  tff(c_363, plain, (![A_315, E_316]: ('#skF_1'('#skF_6', A_315, '#skF_8', '#skF_7', E_316)='#skF_9' | E_316!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_315, '#skF_8', '#skF_7', E_316), '#skF_5') | ~m1_subset_1(E_316, k4_zfmisc_1(A_315, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_315)), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_30, c_358])).
% 2.94/1.46  tff(c_367, plain, (![E_47]: ('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1(E_47, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_16, c_363])).
% 2.94/1.46  tff(c_372, plain, (![E_317]: ('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_317)='#skF_9' | E_317!='#skF_10' | ~m1_subset_1(E_317, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_34, c_367])).
% 2.94/1.46  tff(c_396, plain, ('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_38, c_372])).
% 2.94/1.46  tff(c_8, plain, (![D_15, E_47, C_14, A_12, B_13]: (k4_mcart_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), '#skF_2'(B_13, A_12, D_15, C_14, E_47), '#skF_3'(B_13, A_12, D_15, C_14, E_47), '#skF_4'(B_13, A_12, D_15, C_14, E_47))=E_47 | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.46  tff(c_406, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_396, c_8])).
% 2.94/1.46  tff(c_420, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_406])).
% 2.94/1.46  tff(c_421, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_420])).
% 2.94/1.46  tff(c_24, plain, (![A_74, G_93, D_77, B_75, F_92, C_76, H_94, I_95]: (k8_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_92, G_93, H_94, I_95))=F_92 | ~m1_subset_1(k4_mcart_1(F_92, G_93, H_94, I_95), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.94/1.46  tff(c_453, plain, (![A_74, B_75, C_76, D_77]: (k8_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1('#skF_9', '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')))='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(superposition, [status(thm), theory('equality')], [c_421, c_24])).
% 2.94/1.46  tff(c_484, plain, (![A_318, B_319, C_320, D_321]: (k8_mcart_1(A_318, B_319, C_320, D_321, '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_318, B_319, C_320, D_321)) | k1_xboole_0=D_321 | k1_xboole_0=C_320 | k1_xboole_0=B_319 | k1_xboole_0=A_318)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_453])).
% 2.94/1.46  tff(c_493, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_484])).
% 2.94/1.46  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_493])).
% 2.94/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.46  
% 2.94/1.46  Inference rules
% 2.94/1.46  ----------------------
% 2.94/1.46  #Ref     : 0
% 2.94/1.46  #Sup     : 103
% 2.94/1.46  #Fact    : 0
% 2.94/1.46  #Define  : 0
% 2.94/1.46  #Split   : 0
% 2.94/1.46  #Chain   : 0
% 2.94/1.46  #Close   : 0
% 2.94/1.46  
% 2.94/1.46  Ordering : KBO
% 2.94/1.46  
% 2.94/1.46  Simplification rules
% 2.94/1.46  ----------------------
% 2.94/1.46  #Subsume      : 16
% 2.94/1.46  #Demod        : 91
% 2.94/1.46  #Tautology    : 34
% 2.94/1.46  #SimpNegUnit  : 9
% 2.94/1.46  #BackRed      : 0
% 2.94/1.46  
% 2.94/1.46  #Partial instantiations: 0
% 2.94/1.46  #Strategies tried      : 1
% 2.94/1.46  
% 2.94/1.46  Timing (in seconds)
% 2.94/1.46  ----------------------
% 2.94/1.46  Preprocessing        : 0.31
% 2.94/1.46  Parsing              : 0.15
% 2.94/1.46  CNF conversion       : 0.03
% 2.94/1.46  Main loop            : 0.33
% 2.94/1.46  Inferencing          : 0.14
% 2.94/1.46  Reduction            : 0.10
% 2.94/1.46  Demodulation         : 0.07
% 2.94/1.46  BG Simplification    : 0.02
% 2.94/1.46  Subsumption          : 0.06
% 2.94/1.46  Abstraction          : 0.03
% 2.94/1.46  MUC search           : 0.00
% 2.94/1.46  Cooper               : 0.00
% 2.94/1.46  Total                : 0.67
% 2.94/1.46  Index Insertion      : 0.00
% 2.94/1.46  Index Deletion       : 0.00
% 2.94/1.46  Index Matching       : 0.00
% 2.94/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
