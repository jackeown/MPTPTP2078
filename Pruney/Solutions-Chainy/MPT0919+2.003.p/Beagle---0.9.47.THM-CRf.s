%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:15 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.28s
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
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

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

tff(f_141,negated_conjecture,(
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

tff(f_60,axiom,(
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

tff(f_112,axiom,(
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

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_14,plain,(
    ! [D_11,A_8,E_43,C_10,B_9] :
      ( m1_subset_1('#skF_1'(A_8,B_9,C_10,E_43,D_11),A_8)
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,B_9,C_10,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [D_11,A_8,E_43,C_10,B_9] :
      ( m1_subset_1('#skF_3'(A_8,B_9,C_10,E_43,D_11),C_10)
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,B_9,C_10,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [D_11,A_8,E_43,C_10,B_9] :
      ( m1_subset_1('#skF_4'(A_8,B_9,C_10,E_43,D_11),D_11)
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,B_9,C_10,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [D_11,A_8,E_43,C_10,B_9] :
      ( m1_subset_1('#skF_2'(A_8,B_9,C_10,E_43,D_11),B_9)
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,B_9,C_10,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_383,plain,(
    ! [B_281,D_284,C_282,A_280,E_283] :
      ( k4_mcart_1('#skF_1'(A_280,B_281,C_282,E_283,D_284),'#skF_2'(A_280,B_281,C_282,E_283,D_284),'#skF_3'(A_280,B_281,C_282,E_283,D_284),'#skF_4'(A_280,B_281,C_282,E_283,D_284)) = E_283
      | ~ m1_subset_1(E_283,k4_zfmisc_1(A_280,B_281,C_282,D_284))
      | k1_xboole_0 = D_284
      | k1_xboole_0 = C_282
      | k1_xboole_0 = B_281
      | k1_xboole_0 = A_280 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [G_104,H_112,I_116,J_118] :
      ( G_104 = '#skF_9'
      | k4_mcart_1(G_104,H_112,I_116,J_118) != '#skF_10'
      | ~ m1_subset_1(J_118,'#skF_8')
      | ~ m1_subset_1(I_116,'#skF_7')
      | ~ m1_subset_1(H_112,'#skF_6')
      | ~ m1_subset_1(G_104,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_450,plain,(
    ! [A_308,E_305,D_307,B_306,C_304] :
      ( '#skF_1'(A_308,B_306,C_304,E_305,D_307) = '#skF_9'
      | E_305 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_308,B_306,C_304,E_305,D_307),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_308,B_306,C_304,E_305,D_307),'#skF_7')
      | ~ m1_subset_1('#skF_2'(A_308,B_306,C_304,E_305,D_307),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_308,B_306,C_304,E_305,D_307),'#skF_5')
      | ~ m1_subset_1(E_305,k4_zfmisc_1(A_308,B_306,C_304,D_307))
      | k1_xboole_0 = D_307
      | k1_xboole_0 = C_304
      | k1_xboole_0 = B_306
      | k1_xboole_0 = A_308 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_42])).

tff(c_454,plain,(
    ! [A_8,C_10,E_43,D_11] :
      ( '#skF_1'(A_8,'#skF_6',C_10,E_43,D_11) = '#skF_9'
      | E_43 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_8,'#skF_6',C_10,E_43,D_11),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_8,'#skF_6',C_10,E_43,D_11),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_8,'#skF_6',C_10,E_43,D_11),'#skF_5')
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,'#skF_6',C_10,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_12,c_450])).

tff(c_471,plain,(
    ! [A_319,C_320,E_321,D_322] :
      ( '#skF_1'(A_319,'#skF_6',C_320,E_321,D_322) = '#skF_9'
      | E_321 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_319,'#skF_6',C_320,E_321,D_322),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_319,'#skF_6',C_320,E_321,D_322),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_319,'#skF_6',C_320,E_321,D_322),'#skF_5')
      | ~ m1_subset_1(E_321,k4_zfmisc_1(A_319,'#skF_6',C_320,D_322))
      | k1_xboole_0 = D_322
      | k1_xboole_0 = C_320
      | k1_xboole_0 = A_319 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_454])).

tff(c_475,plain,(
    ! [A_8,C_10,E_43] :
      ( '#skF_1'(A_8,'#skF_6',C_10,E_43,'#skF_8') = '#skF_9'
      | E_43 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(A_8,'#skF_6',C_10,E_43,'#skF_8'),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_8,'#skF_6',C_10,E_43,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,'#skF_6',C_10,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_10
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_8,c_471])).

tff(c_497,plain,(
    ! [A_331,C_332,E_333] :
      ( '#skF_1'(A_331,'#skF_6',C_332,E_333,'#skF_8') = '#skF_9'
      | E_333 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(A_331,'#skF_6',C_332,E_333,'#skF_8'),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_331,'#skF_6',C_332,E_333,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_333,k4_zfmisc_1(A_331,'#skF_6',C_332,'#skF_8'))
      | k1_xboole_0 = C_332
      | k1_xboole_0 = A_331 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_34,c_34,c_475])).

tff(c_501,plain,(
    ! [A_8,E_43] :
      ( '#skF_1'(A_8,'#skF_6','#skF_7',E_43,'#skF_8') = '#skF_9'
      | E_43 != '#skF_10'
      | ~ m1_subset_1('#skF_1'(A_8,'#skF_6','#skF_7',E_43,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_10,c_497])).

tff(c_506,plain,(
    ! [A_334,E_335] :
      ( '#skF_1'(A_334,'#skF_6','#skF_7',E_335,'#skF_8') = '#skF_9'
      | E_335 != '#skF_10'
      | ~ m1_subset_1('#skF_1'(A_334,'#skF_6','#skF_7',E_335,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(E_335,k4_zfmisc_1(A_334,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_334 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_36,c_501])).

tff(c_510,plain,(
    ! [E_43] :
      ( '#skF_1'('#skF_5','#skF_6','#skF_7',E_43,'#skF_8') = '#skF_9'
      | E_43 != '#skF_10'
      | ~ m1_subset_1(E_43,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_14,c_506])).

tff(c_515,plain,(
    ! [E_336] :
      ( '#skF_1'('#skF_5','#skF_6','#skF_7',E_336,'#skF_8') = '#skF_9'
      | E_336 != '#skF_10'
      | ~ m1_subset_1(E_336,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_40,c_510])).

tff(c_539,plain,(
    '#skF_1'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_44,c_515])).

tff(c_6,plain,(
    ! [D_11,A_8,E_43,C_10,B_9] :
      ( k4_mcart_1('#skF_1'(A_8,B_9,C_10,E_43,D_11),'#skF_2'(A_8,B_9,C_10,E_43,D_11),'#skF_3'(A_8,B_9,C_10,E_43,D_11),'#skF_4'(A_8,B_9,C_10,E_43,D_11)) = E_43
      | ~ m1_subset_1(E_43,k4_zfmisc_1(A_8,B_9,C_10,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_546,plain,
    ( k4_mcart_1('#skF_9','#skF_2'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_3'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_6])).

tff(c_557,plain,
    ( k4_mcart_1('#skF_9','#skF_2'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_3'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_546])).

tff(c_558,plain,(
    k4_mcart_1('#skF_9','#skF_2'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_3'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_557])).

tff(c_30,plain,(
    ! [B_77,A_76,C_78,F_85,G_86,D_79,I_88,H_87] :
      ( k8_mcart_1(A_76,B_77,C_78,D_79,k4_mcart_1(F_85,G_86,H_87,I_88)) = F_85
      | k1_xboole_0 = D_79
      | k1_xboole_0 = C_78
      | k1_xboole_0 = B_77
      | k1_xboole_0 = A_76
      | ~ m1_subset_1(k4_mcart_1(F_85,G_86,H_87,I_88),k4_zfmisc_1(A_76,B_77,C_78,D_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_590,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k8_mcart_1(A_76,B_77,C_78,D_79,k4_mcart_1('#skF_9','#skF_2'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_3'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_10','#skF_8'))) = '#skF_9'
      | k1_xboole_0 = D_79
      | k1_xboole_0 = C_78
      | k1_xboole_0 = B_77
      | k1_xboole_0 = A_76
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_76,B_77,C_78,D_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_30])).

tff(c_625,plain,(
    ! [A_337,B_338,C_339,D_340] :
      ( k8_mcart_1(A_337,B_338,C_339,D_340,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_340
      | k1_xboole_0 = C_339
      | k1_xboole_0 = B_338
      | k1_xboole_0 = A_337
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_337,B_338,C_339,D_340)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_590])).

tff(c_628,plain,
    ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_625])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_32,c_628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.46  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.23/1.46  
% 3.23/1.46  %Foreground sorts:
% 3.23/1.46  
% 3.23/1.46  
% 3.23/1.46  %Background operators:
% 3.23/1.46  
% 3.23/1.46  
% 3.23/1.46  %Foreground operators:
% 3.23/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.23/1.46  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.23/1.46  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.23/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.23/1.46  tff('#skF_10', type, '#skF_10': $i).
% 3.23/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.46  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.46  tff('#skF_9', type, '#skF_9': $i).
% 3.23/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff('#skF_8', type, '#skF_8': $i).
% 3.23/1.46  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.23/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.23/1.46  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.46  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.23/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.46  
% 3.28/1.48  tff(f_141, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 3.28/1.48  tff(f_60, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.28/1.48  tff(f_112, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 3.28/1.48  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_34, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_32, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_44, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_14, plain, (![D_11, A_8, E_43, C_10, B_9]: (m1_subset_1('#skF_1'(A_8, B_9, C_10, E_43, D_11), A_8) | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, B_9, C_10, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.48  tff(c_10, plain, (![D_11, A_8, E_43, C_10, B_9]: (m1_subset_1('#skF_3'(A_8, B_9, C_10, E_43, D_11), C_10) | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, B_9, C_10, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.48  tff(c_8, plain, (![D_11, A_8, E_43, C_10, B_9]: (m1_subset_1('#skF_4'(A_8, B_9, C_10, E_43, D_11), D_11) | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, B_9, C_10, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.48  tff(c_12, plain, (![D_11, A_8, E_43, C_10, B_9]: (m1_subset_1('#skF_2'(A_8, B_9, C_10, E_43, D_11), B_9) | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, B_9, C_10, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.48  tff(c_383, plain, (![B_281, D_284, C_282, A_280, E_283]: (k4_mcart_1('#skF_1'(A_280, B_281, C_282, E_283, D_284), '#skF_2'(A_280, B_281, C_282, E_283, D_284), '#skF_3'(A_280, B_281, C_282, E_283, D_284), '#skF_4'(A_280, B_281, C_282, E_283, D_284))=E_283 | ~m1_subset_1(E_283, k4_zfmisc_1(A_280, B_281, C_282, D_284)) | k1_xboole_0=D_284 | k1_xboole_0=C_282 | k1_xboole_0=B_281 | k1_xboole_0=A_280)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.48  tff(c_42, plain, (![G_104, H_112, I_116, J_118]: (G_104='#skF_9' | k4_mcart_1(G_104, H_112, I_116, J_118)!='#skF_10' | ~m1_subset_1(J_118, '#skF_8') | ~m1_subset_1(I_116, '#skF_7') | ~m1_subset_1(H_112, '#skF_6') | ~m1_subset_1(G_104, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.48  tff(c_450, plain, (![A_308, E_305, D_307, B_306, C_304]: ('#skF_1'(A_308, B_306, C_304, E_305, D_307)='#skF_9' | E_305!='#skF_10' | ~m1_subset_1('#skF_4'(A_308, B_306, C_304, E_305, D_307), '#skF_8') | ~m1_subset_1('#skF_3'(A_308, B_306, C_304, E_305, D_307), '#skF_7') | ~m1_subset_1('#skF_2'(A_308, B_306, C_304, E_305, D_307), '#skF_6') | ~m1_subset_1('#skF_1'(A_308, B_306, C_304, E_305, D_307), '#skF_5') | ~m1_subset_1(E_305, k4_zfmisc_1(A_308, B_306, C_304, D_307)) | k1_xboole_0=D_307 | k1_xboole_0=C_304 | k1_xboole_0=B_306 | k1_xboole_0=A_308)), inference(superposition, [status(thm), theory('equality')], [c_383, c_42])).
% 3.28/1.48  tff(c_454, plain, (![A_8, C_10, E_43, D_11]: ('#skF_1'(A_8, '#skF_6', C_10, E_43, D_11)='#skF_9' | E_43!='#skF_10' | ~m1_subset_1('#skF_4'(A_8, '#skF_6', C_10, E_43, D_11), '#skF_8') | ~m1_subset_1('#skF_3'(A_8, '#skF_6', C_10, E_43, D_11), '#skF_7') | ~m1_subset_1('#skF_1'(A_8, '#skF_6', C_10, E_43, D_11), '#skF_5') | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, '#skF_6', C_10, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0='#skF_6' | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_12, c_450])).
% 3.28/1.48  tff(c_471, plain, (![A_319, C_320, E_321, D_322]: ('#skF_1'(A_319, '#skF_6', C_320, E_321, D_322)='#skF_9' | E_321!='#skF_10' | ~m1_subset_1('#skF_4'(A_319, '#skF_6', C_320, E_321, D_322), '#skF_8') | ~m1_subset_1('#skF_3'(A_319, '#skF_6', C_320, E_321, D_322), '#skF_7') | ~m1_subset_1('#skF_1'(A_319, '#skF_6', C_320, E_321, D_322), '#skF_5') | ~m1_subset_1(E_321, k4_zfmisc_1(A_319, '#skF_6', C_320, D_322)) | k1_xboole_0=D_322 | k1_xboole_0=C_320 | k1_xboole_0=A_319)), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_454])).
% 3.28/1.48  tff(c_475, plain, (![A_8, C_10, E_43]: ('#skF_1'(A_8, '#skF_6', C_10, E_43, '#skF_8')='#skF_9' | E_43!='#skF_10' | ~m1_subset_1('#skF_3'(A_8, '#skF_6', C_10, E_43, '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_1'(A_8, '#skF_6', C_10, E_43, '#skF_8'), '#skF_5') | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, '#skF_6', C_10, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_10 | k1_xboole_0='#skF_6' | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_8, c_471])).
% 3.28/1.48  tff(c_497, plain, (![A_331, C_332, E_333]: ('#skF_1'(A_331, '#skF_6', C_332, E_333, '#skF_8')='#skF_9' | E_333!='#skF_10' | ~m1_subset_1('#skF_3'(A_331, '#skF_6', C_332, E_333, '#skF_8'), '#skF_7') | ~m1_subset_1('#skF_1'(A_331, '#skF_6', C_332, E_333, '#skF_8'), '#skF_5') | ~m1_subset_1(E_333, k4_zfmisc_1(A_331, '#skF_6', C_332, '#skF_8')) | k1_xboole_0=C_332 | k1_xboole_0=A_331)), inference(negUnitSimplification, [status(thm)], [c_38, c_34, c_34, c_475])).
% 3.28/1.48  tff(c_501, plain, (![A_8, E_43]: ('#skF_1'(A_8, '#skF_6', '#skF_7', E_43, '#skF_8')='#skF_9' | E_43!='#skF_10' | ~m1_subset_1('#skF_1'(A_8, '#skF_6', '#skF_7', E_43, '#skF_8'), '#skF_5') | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_10, c_497])).
% 3.28/1.48  tff(c_506, plain, (![A_334, E_335]: ('#skF_1'(A_334, '#skF_6', '#skF_7', E_335, '#skF_8')='#skF_9' | E_335!='#skF_10' | ~m1_subset_1('#skF_1'(A_334, '#skF_6', '#skF_7', E_335, '#skF_8'), '#skF_5') | ~m1_subset_1(E_335, k4_zfmisc_1(A_334, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_334)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_36, c_501])).
% 3.28/1.48  tff(c_510, plain, (![E_43]: ('#skF_1'('#skF_5', '#skF_6', '#skF_7', E_43, '#skF_8')='#skF_9' | E_43!='#skF_10' | ~m1_subset_1(E_43, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_14, c_506])).
% 3.28/1.48  tff(c_515, plain, (![E_336]: ('#skF_1'('#skF_5', '#skF_6', '#skF_7', E_336, '#skF_8')='#skF_9' | E_336!='#skF_10' | ~m1_subset_1(E_336, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_40, c_510])).
% 3.28/1.48  tff(c_539, plain, ('#skF_1'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_44, c_515])).
% 3.28/1.48  tff(c_6, plain, (![D_11, A_8, E_43, C_10, B_9]: (k4_mcart_1('#skF_1'(A_8, B_9, C_10, E_43, D_11), '#skF_2'(A_8, B_9, C_10, E_43, D_11), '#skF_3'(A_8, B_9, C_10, E_43, D_11), '#skF_4'(A_8, B_9, C_10, E_43, D_11))=E_43 | ~m1_subset_1(E_43, k4_zfmisc_1(A_8, B_9, C_10, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.48  tff(c_546, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_539, c_6])).
% 3.28/1.48  tff(c_557, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_546])).
% 3.28/1.48  tff(c_558, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_557])).
% 3.28/1.48  tff(c_30, plain, (![B_77, A_76, C_78, F_85, G_86, D_79, I_88, H_87]: (k8_mcart_1(A_76, B_77, C_78, D_79, k4_mcart_1(F_85, G_86, H_87, I_88))=F_85 | k1_xboole_0=D_79 | k1_xboole_0=C_78 | k1_xboole_0=B_77 | k1_xboole_0=A_76 | ~m1_subset_1(k4_mcart_1(F_85, G_86, H_87, I_88), k4_zfmisc_1(A_76, B_77, C_78, D_79)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.28/1.48  tff(c_590, plain, (![A_76, B_77, C_78, D_79]: (k8_mcart_1(A_76, B_77, C_78, D_79, k4_mcart_1('#skF_9', '#skF_2'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_10', '#skF_8')))='#skF_9' | k1_xboole_0=D_79 | k1_xboole_0=C_78 | k1_xboole_0=B_77 | k1_xboole_0=A_76 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_76, B_77, C_78, D_79)))), inference(superposition, [status(thm), theory('equality')], [c_558, c_30])).
% 3.28/1.48  tff(c_625, plain, (![A_337, B_338, C_339, D_340]: (k8_mcart_1(A_337, B_338, C_339, D_340, '#skF_10')='#skF_9' | k1_xboole_0=D_340 | k1_xboole_0=C_339 | k1_xboole_0=B_338 | k1_xboole_0=A_337 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_337, B_338, C_339, D_340)))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_590])).
% 3.28/1.48  tff(c_628, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_625])).
% 3.28/1.48  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_32, c_628])).
% 3.28/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  Inference rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Ref     : 0
% 3.28/1.48  #Sup     : 137
% 3.28/1.48  #Fact    : 0
% 3.28/1.48  #Define  : 0
% 3.28/1.48  #Split   : 0
% 3.28/1.48  #Chain   : 0
% 3.28/1.48  #Close   : 0
% 3.28/1.48  
% 3.28/1.48  Ordering : KBO
% 3.28/1.48  
% 3.28/1.48  Simplification rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Subsume      : 20
% 3.28/1.48  #Demod        : 114
% 3.28/1.48  #Tautology    : 38
% 3.28/1.48  #SimpNegUnit  : 12
% 3.28/1.48  #BackRed      : 0
% 3.28/1.48  
% 3.28/1.48  #Partial instantiations: 0
% 3.28/1.48  #Strategies tried      : 1
% 3.28/1.48  
% 3.28/1.48  Timing (in seconds)
% 3.28/1.48  ----------------------
% 3.28/1.48  Preprocessing        : 0.34
% 3.28/1.48  Parsing              : 0.17
% 3.28/1.48  CNF conversion       : 0.03
% 3.28/1.48  Main loop            : 0.38
% 3.28/1.48  Inferencing          : 0.15
% 3.28/1.48  Reduction            : 0.12
% 3.28/1.48  Demodulation         : 0.08
% 3.28/1.48  BG Simplification    : 0.03
% 3.28/1.48  Subsumption          : 0.06
% 3.28/1.48  Abstraction          : 0.04
% 3.28/1.48  MUC search           : 0.00
% 3.28/1.48  Cooper               : 0.00
% 3.28/1.48  Total                : 0.75
% 3.28/1.48  Index Insertion      : 0.00
% 3.28/1.48  Index Deletion       : 0.00
% 3.28/1.48  Index Matching       : 0.00
% 3.28/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
