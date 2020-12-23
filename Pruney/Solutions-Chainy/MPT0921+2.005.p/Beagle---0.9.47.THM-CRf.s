%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:18 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 179 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  186 (1024 expanded)
%              Number of equality atoms :  130 ( 634 expanded)
%              Maximal formula depth    :   21 (   7 average)
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

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

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

tff(c_372,plain,(
    ! [A_246,B_245,E_249,C_248,D_247] :
      ( k4_mcart_1('#skF_1'(B_245,A_246,D_247,C_248,E_249),'#skF_2'(B_245,A_246,D_247,C_248,E_249),'#skF_3'(B_245,A_246,D_247,C_248,E_249),'#skF_4'(B_245,A_246,D_247,C_248,E_249)) = E_249
      | ~ m1_subset_1(E_249,k4_zfmisc_1(A_246,B_245,C_248,D_247))
      | k1_xboole_0 = D_247
      | k1_xboole_0 = C_248
      | k1_xboole_0 = B_245
      | k1_xboole_0 = A_246 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [I_129,G_117,H_125,J_131] :
      ( I_129 = '#skF_9'
      | k4_mcart_1(G_117,H_125,I_129,J_131) != '#skF_10'
      | ~ m1_subset_1(J_131,'#skF_8')
      | ~ m1_subset_1(I_129,'#skF_7')
      | ~ m1_subset_1(H_125,'#skF_6')
      | ~ m1_subset_1(G_117,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_516,plain,(
    ! [B_278,A_279,C_277,E_275,D_276] :
      ( '#skF_3'(B_278,A_279,D_276,C_277,E_275) = '#skF_9'
      | E_275 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(B_278,A_279,D_276,C_277,E_275),'#skF_8')
      | ~ m1_subset_1('#skF_3'(B_278,A_279,D_276,C_277,E_275),'#skF_7')
      | ~ m1_subset_1('#skF_2'(B_278,A_279,D_276,C_277,E_275),'#skF_6')
      | ~ m1_subset_1('#skF_1'(B_278,A_279,D_276,C_277,E_275),'#skF_5')
      | ~ m1_subset_1(E_275,k4_zfmisc_1(A_279,B_278,C_277,D_276))
      | k1_xboole_0 = D_276
      | k1_xboole_0 = C_277
      | k1_xboole_0 = B_278
      | k1_xboole_0 = A_279 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_44])).

tff(c_520,plain,(
    ! [A_12,D_15,C_14,E_47] :
      ( '#skF_3'('#skF_6',A_12,D_15,C_14,E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_6',A_12,D_15,C_14,E_47),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',A_12,D_15,C_14,E_47),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,D_15,C_14,E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6',C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_14,c_516])).

tff(c_585,plain,(
    ! [A_294,D_295,C_296,E_297] :
      ( '#skF_3'('#skF_6',A_294,D_295,C_296,E_297) = '#skF_9'
      | E_297 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_6',A_294,D_295,C_296,E_297),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_6',A_294,D_295,C_296,E_297),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_294,D_295,C_296,E_297),'#skF_5')
      | ~ m1_subset_1(E_297,k4_zfmisc_1(A_294,'#skF_6',C_296,D_295))
      | k1_xboole_0 = D_295
      | k1_xboole_0 = C_296
      | k1_xboole_0 = A_294 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_520])).

tff(c_589,plain,(
    ! [A_12,C_14,E_47] :
      ( '#skF_3'('#skF_6',A_12,'#skF_8',C_14,E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_6',A_12,'#skF_8',C_14,E_47),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,'#skF_8',C_14,E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6',C_14,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_14
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_10,c_585])).

tff(c_689,plain,(
    ! [A_340,C_341,E_342] :
      ( '#skF_3'('#skF_6',A_340,'#skF_8',C_341,E_342) = '#skF_9'
      | E_342 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_6',A_340,'#skF_8',C_341,E_342),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_6',A_340,'#skF_8',C_341,E_342),'#skF_5')
      | ~ m1_subset_1(E_342,k4_zfmisc_1(A_340,'#skF_6',C_341,'#skF_8'))
      | k1_xboole_0 = C_341
      | k1_xboole_0 = A_340 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_36,c_589])).

tff(c_693,plain,(
    ! [A_12,E_47] :
      ( '#skF_3'('#skF_6',A_12,'#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_12,'#skF_8','#skF_7',E_47),'#skF_5')
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_12,c_689])).

tff(c_698,plain,(
    ! [A_343,E_344] :
      ( '#skF_3'('#skF_6',A_343,'#skF_8','#skF_7',E_344) = '#skF_9'
      | E_344 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_6',A_343,'#skF_8','#skF_7',E_344),'#skF_5')
      | ~ m1_subset_1(E_344,k4_zfmisc_1(A_343,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_343 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_38,c_693])).

tff(c_702,plain,(
    ! [E_47] :
      ( '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7',E_47) = '#skF_9'
      | E_47 != '#skF_10'
      | ~ m1_subset_1(E_47,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_16,c_698])).

tff(c_707,plain,(
    ! [E_345] :
      ( '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7',E_345) = '#skF_9'
      | E_345 != '#skF_10'
      | ~ m1_subset_1(E_345,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_42,c_702])).

tff(c_731,plain,(
    '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_46,c_707])).

tff(c_8,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( k4_mcart_1('#skF_1'(B_13,A_12,D_15,C_14,E_47),'#skF_2'(B_13,A_12,D_15,C_14,E_47),'#skF_3'(B_13,A_12,D_15,C_14,E_47),'#skF_4'(B_13,A_12,D_15,C_14,E_47)) = E_47
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_738,plain,
    ( k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_8])).

tff(c_749,plain,
    ( k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_738])).

tff(c_750,plain,(
    k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_749])).

tff(c_20,plain,(
    ! [A_74,G_93,D_77,B_75,F_92,C_76,H_94,I_95] :
      ( k10_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_92,G_93,H_94,I_95)) = H_94
      | ~ m1_subset_1(k4_mcart_1(F_92,G_93,H_94,I_95),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_776,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k10_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1('#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'),'#skF_9','#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_10'))) = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_20])).

tff(c_793,plain,(
    ! [A_346,B_347,C_348,D_349] :
      ( k10_mcart_1(A_346,B_347,C_348,D_349,'#skF_10') = '#skF_9'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_346,B_347,C_348,D_349))
      | k1_xboole_0 = D_349
      | k1_xboole_0 = C_348
      | k1_xboole_0 = B_347
      | k1_xboole_0 = A_346 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_776])).

tff(c_802,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_793])).

tff(c_806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_34,c_802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.27/1.52  
% 3.27/1.52  %Foreground sorts:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Background operators:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Foreground operators:
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.27/1.52  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.27/1.52  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.27/1.52  tff('#skF_10', type, '#skF_10': $i).
% 3.27/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.52  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.52  tff('#skF_9', type, '#skF_9': $i).
% 3.27/1.52  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.27/1.52  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.52  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.27/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.52  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.27/1.52  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.52  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.27/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.52  
% 3.56/1.54  tff(f_144, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 3.56/1.54  tff(f_62, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.56/1.54  tff(f_90, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 3.56/1.54  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_40, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_36, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_34, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_46, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_16, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), A_12) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.56/1.54  tff(c_12, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_3'(B_13, A_12, D_15, C_14, E_47), C_14) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.56/1.54  tff(c_10, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_4'(B_13, A_12, D_15, C_14, E_47), D_15) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.56/1.54  tff(c_14, plain, (![D_15, E_47, C_14, A_12, B_13]: (m1_subset_1('#skF_2'(B_13, A_12, D_15, C_14, E_47), B_13) | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.56/1.54  tff(c_372, plain, (![A_246, B_245, E_249, C_248, D_247]: (k4_mcart_1('#skF_1'(B_245, A_246, D_247, C_248, E_249), '#skF_2'(B_245, A_246, D_247, C_248, E_249), '#skF_3'(B_245, A_246, D_247, C_248, E_249), '#skF_4'(B_245, A_246, D_247, C_248, E_249))=E_249 | ~m1_subset_1(E_249, k4_zfmisc_1(A_246, B_245, C_248, D_247)) | k1_xboole_0=D_247 | k1_xboole_0=C_248 | k1_xboole_0=B_245 | k1_xboole_0=A_246)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.56/1.54  tff(c_44, plain, (![I_129, G_117, H_125, J_131]: (I_129='#skF_9' | k4_mcart_1(G_117, H_125, I_129, J_131)!='#skF_10' | ~m1_subset_1(J_131, '#skF_8') | ~m1_subset_1(I_129, '#skF_7') | ~m1_subset_1(H_125, '#skF_6') | ~m1_subset_1(G_117, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.56/1.54  tff(c_516, plain, (![B_278, A_279, C_277, E_275, D_276]: ('#skF_3'(B_278, A_279, D_276, C_277, E_275)='#skF_9' | E_275!='#skF_10' | ~m1_subset_1('#skF_4'(B_278, A_279, D_276, C_277, E_275), '#skF_8') | ~m1_subset_1('#skF_3'(B_278, A_279, D_276, C_277, E_275), '#skF_7') | ~m1_subset_1('#skF_2'(B_278, A_279, D_276, C_277, E_275), '#skF_6') | ~m1_subset_1('#skF_1'(B_278, A_279, D_276, C_277, E_275), '#skF_5') | ~m1_subset_1(E_275, k4_zfmisc_1(A_279, B_278, C_277, D_276)) | k1_xboole_0=D_276 | k1_xboole_0=C_277 | k1_xboole_0=B_278 | k1_xboole_0=A_279)), inference(superposition, [status(thm), theory('equality')], [c_372, c_44])).
% 3.56/1.54  tff(c_520, plain, (![A_12, D_15, C_14, E_47]: ('#skF_3'('#skF_6', A_12, D_15, C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_12, D_15, C_14, E_47), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_12, D_15, C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, D_15, C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_14, c_516])).
% 3.56/1.54  tff(c_585, plain, (![A_294, D_295, C_296, E_297]: ('#skF_3'('#skF_6', A_294, D_295, C_296, E_297)='#skF_9' | E_297!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_6', A_294, D_295, C_296, E_297), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_6', A_294, D_295, C_296, E_297), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_294, D_295, C_296, E_297), '#skF_5') | ~m1_subset_1(E_297, k4_zfmisc_1(A_294, '#skF_6', C_296, D_295)) | k1_xboole_0=D_295 | k1_xboole_0=C_296 | k1_xboole_0=A_294)), inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_520])).
% 3.56/1.54  tff(c_589, plain, (![A_12, C_14, E_47]: ('#skF_3'('#skF_6', A_12, '#skF_8', C_14, E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', C_14, E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', C_14, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_14 | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_10, c_585])).
% 3.56/1.54  tff(c_689, plain, (![A_340, C_341, E_342]: ('#skF_3'('#skF_6', A_340, '#skF_8', C_341, E_342)='#skF_9' | E_342!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_6', A_340, '#skF_8', C_341, E_342), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6', A_340, '#skF_8', C_341, E_342), '#skF_5') | ~m1_subset_1(E_342, k4_zfmisc_1(A_340, '#skF_6', C_341, '#skF_8')) | k1_xboole_0=C_341 | k1_xboole_0=A_340)), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_36, c_589])).
% 3.56/1.54  tff(c_693, plain, (![A_12, E_47]: ('#skF_3'('#skF_6', A_12, '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_12, '#skF_8', '#skF_7', E_47), '#skF_5') | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_12, c_689])).
% 3.56/1.54  tff(c_698, plain, (![A_343, E_344]: ('#skF_3'('#skF_6', A_343, '#skF_8', '#skF_7', E_344)='#skF_9' | E_344!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_6', A_343, '#skF_8', '#skF_7', E_344), '#skF_5') | ~m1_subset_1(E_344, k4_zfmisc_1(A_343, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_343)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_38, c_693])).
% 3.56/1.54  tff(c_702, plain, (![E_47]: ('#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_47)='#skF_9' | E_47!='#skF_10' | ~m1_subset_1(E_47, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_16, c_698])).
% 3.56/1.54  tff(c_707, plain, (![E_345]: ('#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', E_345)='#skF_9' | E_345!='#skF_10' | ~m1_subset_1(E_345, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_42, c_702])).
% 3.56/1.54  tff(c_731, plain, ('#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_46, c_707])).
% 3.56/1.54  tff(c_8, plain, (![D_15, E_47, C_14, A_12, B_13]: (k4_mcart_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), '#skF_2'(B_13, A_12, D_15, C_14, E_47), '#skF_3'(B_13, A_12, D_15, C_14, E_47), '#skF_4'(B_13, A_12, D_15, C_14, E_47))=E_47 | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.56/1.54  tff(c_738, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_731, c_8])).
% 3.56/1.54  tff(c_749, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_738])).
% 3.56/1.54  tff(c_750, plain, (k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_749])).
% 3.56/1.54  tff(c_20, plain, (![A_74, G_93, D_77, B_75, F_92, C_76, H_94, I_95]: (k10_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_92, G_93, H_94, I_95))=H_94 | ~m1_subset_1(k4_mcart_1(F_92, G_93, H_94, I_95), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.56/1.54  tff(c_776, plain, (![A_74, B_75, C_76, D_77]: (k10_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1('#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10'), '#skF_9', '#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_10')))='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(superposition, [status(thm), theory('equality')], [c_750, c_20])).
% 3.56/1.54  tff(c_793, plain, (![A_346, B_347, C_348, D_349]: (k10_mcart_1(A_346, B_347, C_348, D_349, '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_346, B_347, C_348, D_349)) | k1_xboole_0=D_349 | k1_xboole_0=C_348 | k1_xboole_0=B_347 | k1_xboole_0=A_346)), inference(demodulation, [status(thm), theory('equality')], [c_750, c_776])).
% 3.56/1.54  tff(c_802, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_793])).
% 3.56/1.54  tff(c_806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_34, c_802])).
% 3.56/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.54  
% 3.56/1.54  Inference rules
% 3.56/1.54  ----------------------
% 3.56/1.54  #Ref     : 0
% 3.56/1.54  #Sup     : 171
% 3.56/1.54  #Fact    : 0
% 3.56/1.54  #Define  : 0
% 3.56/1.54  #Split   : 0
% 3.56/1.54  #Chain   : 0
% 3.56/1.54  #Close   : 0
% 3.56/1.54  
% 3.56/1.54  Ordering : KBO
% 3.56/1.54  
% 3.56/1.54  Simplification rules
% 3.56/1.54  ----------------------
% 3.56/1.54  #Subsume      : 19
% 3.56/1.54  #Demod        : 117
% 3.56/1.54  #Tautology    : 40
% 3.56/1.54  #SimpNegUnit  : 12
% 3.56/1.54  #BackRed      : 0
% 3.56/1.54  
% 3.56/1.54  #Partial instantiations: 0
% 3.56/1.54  #Strategies tried      : 1
% 3.56/1.54  
% 3.56/1.54  Timing (in seconds)
% 3.56/1.54  ----------------------
% 3.56/1.54  Preprocessing        : 0.34
% 3.56/1.54  Parsing              : 0.17
% 3.56/1.54  CNF conversion       : 0.03
% 3.56/1.54  Main loop            : 0.44
% 3.56/1.54  Inferencing          : 0.17
% 3.56/1.54  Reduction            : 0.13
% 3.56/1.54  Demodulation         : 0.09
% 3.56/1.54  BG Simplification    : 0.04
% 3.56/1.54  Subsumption          : 0.07
% 3.56/1.54  Abstraction          : 0.05
% 3.56/1.54  MUC search           : 0.00
% 3.56/1.54  Cooper               : 0.00
% 3.56/1.54  Total                : 0.81
% 3.56/1.54  Index Insertion      : 0.00
% 3.56/1.54  Index Deletion       : 0.00
% 3.56/1.54  Index Matching       : 0.00
% 3.56/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
