%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:58 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 723 expanded)
%              Number of leaves         :   27 ( 280 expanded)
%              Depth                    :   20
%              Number of atoms          :  177 (2776 expanded)
%              Number of equality atoms :  129 (1923 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_2'(A_7,B_8,C_9,D_25),B_8)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_3'(A_7,B_8,C_9,D_25),C_9)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_9,D_25),A_7)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k3_mcart_1('#skF_1'(A_101,B_102,C_103,D_104),'#skF_2'(A_101,B_102,C_103,D_104),'#skF_3'(A_101,B_102,C_103,D_104)) = D_104
      | ~ m1_subset_1(D_104,k3_zfmisc_1(A_101,B_102,C_103))
      | k1_xboole_0 = C_103
      | k1_xboole_0 = B_102
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,(
    ! [A_62,B_63,C_64] : k4_tarski(k4_tarski(A_62,B_63),C_64) = k3_mcart_1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    ! [A_62,B_63,C_64] : k2_mcart_1(k3_mcart_1(A_62,B_63,C_64)) = C_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_18])).

tff(c_174,plain,(
    ! [D_105,A_106,B_107,C_108] :
      ( k2_mcart_1(D_105) = '#skF_3'(A_106,B_107,C_108,D_105)
      | ~ m1_subset_1(D_105,k3_zfmisc_1(A_106,B_107,C_108))
      | k1_xboole_0 = C_108
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_106 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_58])).

tff(c_192,plain,
    ( k2_mcart_1('#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_174])).

tff(c_198,plain,(
    k2_mcart_1('#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_192])).

tff(c_258,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k3_mcart_1(k5_mcart_1(A_117,B_118,C_119,D_120),k6_mcart_1(A_117,B_118,C_119,D_120),k7_mcart_1(A_117,B_118,C_119,D_120)) = D_120
      | ~ m1_subset_1(D_120,k3_zfmisc_1(A_117,B_118,C_119))
      | k1_xboole_0 = C_119
      | k1_xboole_0 = B_118
      | k1_xboole_0 = A_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_281,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_mcart_1(A_121,B_122,C_123,D_124) = k2_mcart_1(D_124)
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_58])).

tff(c_299,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_281])).

tff(c_304,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_299])).

tff(c_305,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_304])).

tff(c_14,plain,(
    ! [A_37,B_38,C_39,D_41] :
      ( k3_mcart_1(k5_mcart_1(A_37,B_38,C_39,D_41),k6_mcart_1(A_37,B_38,C_39,D_41),k7_mcart_1(A_37,B_38,C_39,D_41)) = D_41
      | ~ m1_subset_1(D_41,k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_309,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_14])).

tff(c_313,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_309])).

tff(c_314,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_313])).

tff(c_16,plain,(
    ! [A_42,B_43] : k1_mcart_1(k4_tarski(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_61,plain,(
    ! [A_62,B_63,C_64] : k1_mcart_1(k3_mcart_1(A_62,B_63,C_64)) = k4_tarski(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_16])).

tff(c_321,plain,(
    k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_61])).

tff(c_346,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_16])).

tff(c_206,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k4_tarski('#skF_1'(A_109,B_110,C_111,D_112),'#skF_2'(A_109,B_110,C_111,D_112)) = k1_mcart_1(D_112)
      | ~ m1_subset_1(D_112,k3_zfmisc_1(A_109,B_110,C_111))
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_110
      | k1_xboole_0 = A_109 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_61])).

tff(c_499,plain,(
    ! [D_135,A_136,B_137,C_138] :
      ( k1_mcart_1(k1_mcart_1(D_135)) = '#skF_1'(A_136,B_137,C_138,D_135)
      | ~ m1_subset_1(D_135,k3_zfmisc_1(A_136,B_137,C_138))
      | k1_xboole_0 = C_138
      | k1_xboole_0 = B_137
      | k1_xboole_0 = A_136 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_16])).

tff(c_517,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_499])).

tff(c_522,plain,
    ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_517])).

tff(c_523,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_522])).

tff(c_227,plain,(
    ! [D_113,A_114,B_115,C_116] :
      ( k2_mcart_1(k1_mcart_1(D_113)) = '#skF_2'(A_114,B_115,C_116,D_113)
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_114,B_115,C_116))
      | k1_xboole_0 = C_116
      | k1_xboole_0 = B_115
      | k1_xboole_0 = A_114 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_18])).

tff(c_245,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_251,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_245])).

tff(c_343,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_18])).

tff(c_349,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_343])).

tff(c_20,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [F_51,G_55,H_57] :
      ( F_51 = '#skF_7'
      | k3_mcart_1(F_51,G_55,H_57) != '#skF_8'
      | ~ m1_subset_1(H_57,'#skF_6')
      | ~ m1_subset_1(G_55,'#skF_5')
      | ~ m1_subset_1(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_323,plain,
    ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_6')
    | ~ m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_28])).

tff(c_331,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_6')
    | ~ m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_323])).

tff(c_717,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_349,c_331])).

tff(c_718,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_721,plain,
    ( ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_718])).

tff(c_724,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_721])).

tff(c_726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_724])).

tff(c_727,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_729,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_732,plain,
    ( ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_729])).

tff(c_735,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_732])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_735])).

tff(c_738,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_742,plain,
    ( ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_738])).

tff(c_745,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_742])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.46  
% 2.51/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.46  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.51/1.46  
% 2.51/1.46  %Foreground sorts:
% 2.51/1.46  
% 2.51/1.46  
% 2.51/1.46  %Background operators:
% 2.51/1.46  
% 2.51/1.46  
% 2.51/1.46  %Foreground operators:
% 2.51/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.46  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.51/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.51/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.46  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.51/1.46  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.51/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.51/1.46  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.51/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.51/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.46  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.51/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.51/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.51/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.51/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.46  
% 2.51/1.48  tff(f_98, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 2.51/1.48  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.51/1.48  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.51/1.48  tff(f_74, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.51/1.48  tff(f_70, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.51/1.48  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.48  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.48  tff(c_22, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.48  tff(c_30, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.48  tff(c_10, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_2'(A_7, B_8, C_9, D_25), B_8) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.48  tff(c_8, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_3'(A_7, B_8, C_9, D_25), C_9) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.48  tff(c_12, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_1'(A_7, B_8, C_9, D_25), A_7) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.48  tff(c_155, plain, (![A_101, B_102, C_103, D_104]: (k3_mcart_1('#skF_1'(A_101, B_102, C_103, D_104), '#skF_2'(A_101, B_102, C_103, D_104), '#skF_3'(A_101, B_102, C_103, D_104))=D_104 | ~m1_subset_1(D_104, k3_zfmisc_1(A_101, B_102, C_103)) | k1_xboole_0=C_103 | k1_xboole_0=B_102 | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.48  tff(c_49, plain, (![A_62, B_63, C_64]: (k4_tarski(k4_tarski(A_62, B_63), C_64)=k3_mcart_1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.48  tff(c_18, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.51/1.48  tff(c_58, plain, (![A_62, B_63, C_64]: (k2_mcart_1(k3_mcart_1(A_62, B_63, C_64))=C_64)), inference(superposition, [status(thm), theory('equality')], [c_49, c_18])).
% 2.51/1.48  tff(c_174, plain, (![D_105, A_106, B_107, C_108]: (k2_mcart_1(D_105)='#skF_3'(A_106, B_107, C_108, D_105) | ~m1_subset_1(D_105, k3_zfmisc_1(A_106, B_107, C_108)) | k1_xboole_0=C_108 | k1_xboole_0=B_107 | k1_xboole_0=A_106)), inference(superposition, [status(thm), theory('equality')], [c_155, c_58])).
% 2.51/1.48  tff(c_192, plain, (k2_mcart_1('#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_174])).
% 2.51/1.48  tff(c_198, plain, (k2_mcart_1('#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_192])).
% 2.51/1.48  tff(c_258, plain, (![A_117, B_118, C_119, D_120]: (k3_mcart_1(k5_mcart_1(A_117, B_118, C_119, D_120), k6_mcart_1(A_117, B_118, C_119, D_120), k7_mcart_1(A_117, B_118, C_119, D_120))=D_120 | ~m1_subset_1(D_120, k3_zfmisc_1(A_117, B_118, C_119)) | k1_xboole_0=C_119 | k1_xboole_0=B_118 | k1_xboole_0=A_117)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.48  tff(c_281, plain, (![A_121, B_122, C_123, D_124]: (k7_mcart_1(A_121, B_122, C_123, D_124)=k2_mcart_1(D_124) | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(superposition, [status(thm), theory('equality')], [c_258, c_58])).
% 2.51/1.48  tff(c_299, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_281])).
% 2.51/1.48  tff(c_304, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_299])).
% 2.51/1.48  tff(c_305, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_304])).
% 2.51/1.48  tff(c_14, plain, (![A_37, B_38, C_39, D_41]: (k3_mcart_1(k5_mcart_1(A_37, B_38, C_39, D_41), k6_mcart_1(A_37, B_38, C_39, D_41), k7_mcart_1(A_37, B_38, C_39, D_41))=D_41 | ~m1_subset_1(D_41, k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.48  tff(c_309, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_305, c_14])).
% 2.51/1.48  tff(c_313, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_309])).
% 2.51/1.48  tff(c_314, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_313])).
% 2.51/1.48  tff(c_16, plain, (![A_42, B_43]: (k1_mcart_1(k4_tarski(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.51/1.48  tff(c_61, plain, (![A_62, B_63, C_64]: (k1_mcart_1(k3_mcart_1(A_62, B_63, C_64))=k4_tarski(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_49, c_16])).
% 2.51/1.48  tff(c_321, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_314, c_61])).
% 2.51/1.48  tff(c_346, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_321, c_16])).
% 2.51/1.48  tff(c_206, plain, (![A_109, B_110, C_111, D_112]: (k4_tarski('#skF_1'(A_109, B_110, C_111, D_112), '#skF_2'(A_109, B_110, C_111, D_112))=k1_mcart_1(D_112) | ~m1_subset_1(D_112, k3_zfmisc_1(A_109, B_110, C_111)) | k1_xboole_0=C_111 | k1_xboole_0=B_110 | k1_xboole_0=A_109)), inference(superposition, [status(thm), theory('equality')], [c_155, c_61])).
% 2.51/1.48  tff(c_499, plain, (![D_135, A_136, B_137, C_138]: (k1_mcart_1(k1_mcart_1(D_135))='#skF_1'(A_136, B_137, C_138, D_135) | ~m1_subset_1(D_135, k3_zfmisc_1(A_136, B_137, C_138)) | k1_xboole_0=C_138 | k1_xboole_0=B_137 | k1_xboole_0=A_136)), inference(superposition, [status(thm), theory('equality')], [c_206, c_16])).
% 2.51/1.48  tff(c_517, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_499])).
% 2.51/1.48  tff(c_522, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_517])).
% 2.51/1.48  tff(c_523, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_522])).
% 2.51/1.48  tff(c_227, plain, (![D_113, A_114, B_115, C_116]: (k2_mcart_1(k1_mcart_1(D_113))='#skF_2'(A_114, B_115, C_116, D_113) | ~m1_subset_1(D_113, k3_zfmisc_1(A_114, B_115, C_116)) | k1_xboole_0=C_116 | k1_xboole_0=B_115 | k1_xboole_0=A_114)), inference(superposition, [status(thm), theory('equality')], [c_206, c_18])).
% 2.51/1.48  tff(c_245, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_227])).
% 2.51/1.48  tff(c_251, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_245])).
% 2.51/1.48  tff(c_343, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_321, c_18])).
% 2.51/1.48  tff(c_349, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_343])).
% 2.51/1.48  tff(c_20, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.48  tff(c_28, plain, (![F_51, G_55, H_57]: (F_51='#skF_7' | k3_mcart_1(F_51, G_55, H_57)!='#skF_8' | ~m1_subset_1(H_57, '#skF_6') | ~m1_subset_1(G_55, '#skF_5') | ~m1_subset_1(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.48  tff(c_323, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_6') | ~m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_314, c_28])).
% 2.51/1.48  tff(c_331, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_6') | ~m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_323])).
% 2.51/1.48  tff(c_717, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_523, c_349, c_331])).
% 2.51/1.48  tff(c_718, plain, (~m1_subset_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(splitLeft, [status(thm)], [c_717])).
% 2.51/1.48  tff(c_721, plain, (~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_12, c_718])).
% 2.51/1.48  tff(c_724, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_721])).
% 2.51/1.48  tff(c_726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_724])).
% 2.51/1.48  tff(c_727, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_717])).
% 2.51/1.48  tff(c_729, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_727])).
% 2.51/1.48  tff(c_732, plain, (~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_729])).
% 2.51/1.48  tff(c_735, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_732])).
% 2.51/1.48  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_735])).
% 2.51/1.48  tff(c_738, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_727])).
% 2.51/1.48  tff(c_742, plain, (~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_738])).
% 2.51/1.48  tff(c_745, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_742])).
% 2.51/1.48  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_745])).
% 2.51/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.48  
% 2.51/1.48  Inference rules
% 2.51/1.48  ----------------------
% 2.51/1.48  #Ref     : 0
% 2.51/1.48  #Sup     : 171
% 2.51/1.48  #Fact    : 0
% 2.51/1.48  #Define  : 0
% 2.51/1.48  #Split   : 2
% 2.51/1.48  #Chain   : 0
% 2.51/1.48  #Close   : 0
% 2.51/1.48  
% 2.51/1.48  Ordering : KBO
% 2.51/1.48  
% 2.51/1.48  Simplification rules
% 2.51/1.48  ----------------------
% 2.51/1.48  #Subsume      : 4
% 2.51/1.48  #Demod        : 98
% 2.51/1.48  #Tautology    : 101
% 2.51/1.48  #SimpNegUnit  : 26
% 2.51/1.48  #BackRed      : 7
% 2.51/1.48  
% 2.51/1.48  #Partial instantiations: 0
% 2.51/1.48  #Strategies tried      : 1
% 2.51/1.48  
% 2.51/1.48  Timing (in seconds)
% 2.51/1.48  ----------------------
% 2.51/1.48  Preprocessing        : 0.29
% 2.51/1.48  Parsing              : 0.15
% 2.51/1.48  CNF conversion       : 0.02
% 2.51/1.48  Main loop            : 0.36
% 2.51/1.48  Inferencing          : 0.15
% 2.51/1.48  Reduction            : 0.11
% 2.51/1.48  Demodulation         : 0.08
% 2.51/1.48  BG Simplification    : 0.02
% 2.51/1.48  Subsumption          : 0.05
% 2.51/1.48  Abstraction          : 0.03
% 2.51/1.48  MUC search           : 0.00
% 3.02/1.48  Cooper               : 0.00
% 3.02/1.48  Total                : 0.68
% 3.02/1.48  Index Insertion      : 0.00
% 3.02/1.48  Index Deletion       : 0.00
% 3.02/1.48  Index Matching       : 0.00
% 3.02/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
