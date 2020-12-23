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
% DateTime   : Thu Dec  3 10:10:22 EST 2020

% Result     : Theorem 11.76s
% Output     : CNFRefutation 11.76s
% Verified   : 
% Statistics : Number of formulae       :  159 (1214 expanded)
%              Number of leaves         :   45 ( 413 expanded)
%              Depth                    :   18
%              Number of atoms          :  219 (2650 expanded)
%              Number of equality atoms :   25 ( 610 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_20 > #skF_18 > #skF_17 > #skF_11 > #skF_6 > #skF_15 > #skF_19 > #skF_4 > #skF_10 > #skF_8 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_21 > #skF_9 > #skF_22 > #skF_3 > #skF_2 > #skF_24 > #skF_23 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_24',type,(
    '#skF_24': $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_50,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
      <=> ( r2_hidden(A,E)
          & r2_hidden(B,F)
          & r2_hidden(C,G)
          & r2_hidden(D,H) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_42,plain,(
    ! [A_46,B_47,C_48,D_49] : k4_tarski(k3_mcart_1(A_46,B_47,C_48),D_49) = k4_mcart_1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_247,plain,(
    ! [E_109,F_110,A_111,B_112] :
      ( r2_hidden(k4_tarski(E_109,F_110),k2_zfmisc_1(A_111,B_112))
      | ~ r2_hidden(F_110,B_112)
      | ~ r2_hidden(E_109,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [A_54,C_56,B_55] :
      ( r2_hidden(k2_mcart_1(A_54),C_56)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_55,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_266,plain,(
    ! [E_113,F_114,B_115,A_116] :
      ( r2_hidden(k2_mcart_1(k4_tarski(E_113,F_114)),B_115)
      | ~ r2_hidden(F_114,B_115)
      | ~ r2_hidden(E_113,A_116) ) ),
    inference(resolution,[status(thm)],[c_247,c_46])).

tff(c_323,plain,(
    ! [C_120,F_121,B_122] :
      ( r2_hidden(k2_mcart_1(k4_tarski(C_120,F_121)),B_122)
      | ~ r2_hidden(F_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_4,c_266])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,(
    ! [C_123,F_124,A_125] :
      ( k2_mcart_1(k4_tarski(C_123,F_124)) = A_125
      | ~ r2_hidden(F_124,k1_tarski(A_125)) ) ),
    inference(resolution,[status(thm)],[c_323,c_2])).

tff(c_377,plain,(
    ! [C_126,C_127] : k2_mcart_1(k4_tarski(C_126,C_127)) = C_127 ),
    inference(resolution,[status(thm)],[c_4,c_355])).

tff(c_386,plain,(
    ! [A_46,B_47,C_48,D_49] : k2_mcart_1(k4_mcart_1(A_46,B_47,C_48,D_49)) = D_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_377])).

tff(c_62,plain,
    ( r2_hidden('#skF_12','#skF_16')
    | r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_126,plain,(
    r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_127,plain,(
    ! [A_82,B_83,C_84,D_85] : k2_zfmisc_1(k3_zfmisc_1(A_82,B_83,C_84),D_85) = k4_zfmisc_1(A_82,B_83,C_84,D_85) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_143,plain,(
    ! [B_89,D_87,C_88,A_86,A_90] :
      ( r2_hidden(k2_mcart_1(A_86),D_87)
      | ~ r2_hidden(A_86,k4_zfmisc_1(A_90,B_89,C_88,D_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_46])).

tff(c_146,plain,(
    r2_hidden(k2_mcart_1(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20')),'#skF_24') ),
    inference(resolution,[status(thm)],[c_126,c_143])).

tff(c_405,plain,(
    r2_hidden('#skF_20','#skF_24') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_146])).

tff(c_58,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_20','#skF_24')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_579,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_58])).

tff(c_580,plain,(
    ~ r2_hidden('#skF_17','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_48,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden(k1_mcart_1(A_54),B_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_55,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_456,plain,(
    ! [E_138,F_139,A_140,B_141] :
      ( r2_hidden(k1_mcart_1(k4_tarski(E_138,F_139)),A_140)
      | ~ r2_hidden(F_139,B_141)
      | ~ r2_hidden(E_138,A_140) ) ),
    inference(resolution,[status(thm)],[c_247,c_48])).

tff(c_481,plain,(
    ! [E_142,C_143,A_144] :
      ( r2_hidden(k1_mcart_1(k4_tarski(E_142,C_143)),A_144)
      | ~ r2_hidden(E_142,A_144) ) ),
    inference(resolution,[status(thm)],[c_4,c_456])).

tff(c_514,plain,(
    ! [E_145,C_146,A_147] :
      ( k1_mcart_1(k4_tarski(E_145,C_146)) = A_147
      | ~ r2_hidden(E_145,k1_tarski(A_147)) ) ),
    inference(resolution,[status(thm)],[c_481,c_2])).

tff(c_537,plain,(
    ! [C_5,C_146] : k1_mcart_1(k4_tarski(C_5,C_146)) = C_5 ),
    inference(resolution,[status(thm)],[c_4,c_514])).

tff(c_38,plain,(
    ! [A_40,B_41,C_42] : k4_tarski(k4_tarski(A_40,B_41),C_42) = k3_mcart_1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_540,plain,(
    ! [C_148,C_149] : k1_mcart_1(k4_tarski(C_148,C_149)) = C_148 ),
    inference(resolution,[status(thm)],[c_4,c_514])).

tff(c_552,plain,(
    ! [A_40,B_41,C_42] : k1_mcart_1(k3_mcart_1(A_40,B_41,C_42)) = k4_tarski(A_40,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_540])).

tff(c_549,plain,(
    ! [A_46,B_47,C_48,D_49] : k1_mcart_1(k4_mcart_1(A_46,B_47,C_48,D_49)) = k3_mcart_1(A_46,B_47,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_540])).

tff(c_651,plain,(
    ! [C_166,B_167,D_165,A_164,A_168] :
      ( r2_hidden(k1_mcart_1(A_164),k3_zfmisc_1(A_168,B_167,C_166))
      | ~ r2_hidden(A_164,k4_zfmisc_1(A_168,B_167,C_166,D_165)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_48])).

tff(c_665,plain,(
    r2_hidden(k1_mcart_1(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20')),k3_zfmisc_1('#skF_21','#skF_22','#skF_23')) ),
    inference(resolution,[status(thm)],[c_126,c_651])).

tff(c_671,plain,(
    r2_hidden(k3_mcart_1('#skF_17','#skF_18','#skF_19'),k3_zfmisc_1('#skF_21','#skF_22','#skF_23')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_665])).

tff(c_93,plain,(
    ! [A_69,B_70,C_71] : k2_zfmisc_1(k2_zfmisc_1(A_69,B_70),C_71) = k3_zfmisc_1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_103,plain,(
    ! [A_54,A_69,B_70,C_71] :
      ( r2_hidden(k1_mcart_1(A_54),k2_zfmisc_1(A_69,B_70))
      | ~ r2_hidden(A_54,k3_zfmisc_1(A_69,B_70,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_48])).

tff(c_703,plain,(
    r2_hidden(k1_mcart_1(k3_mcart_1('#skF_17','#skF_18','#skF_19')),k2_zfmisc_1('#skF_21','#skF_22')) ),
    inference(resolution,[status(thm)],[c_671,c_103])).

tff(c_707,plain,(
    r2_hidden(k4_tarski('#skF_17','#skF_18'),k2_zfmisc_1('#skF_21','#skF_22')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_703])).

tff(c_713,plain,(
    r2_hidden(k1_mcart_1(k4_tarski('#skF_17','#skF_18')),'#skF_21') ),
    inference(resolution,[status(thm)],[c_707,c_48])).

tff(c_717,plain,(
    r2_hidden('#skF_17','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_713])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_717])).

tff(c_721,plain,(
    r2_hidden('#skF_17','#skF_21') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_54,plain,
    ( r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_20','#skF_24')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_931,plain,
    ( r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_405,c_54])).

tff(c_932,plain,(
    ~ r2_hidden('#skF_18','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_931])).

tff(c_374,plain,(
    ! [C_123,C_5] : k2_mcart_1(k4_tarski(C_123,C_5)) = C_5 ),
    inference(resolution,[status(thm)],[c_4,c_355])).

tff(c_1007,plain,(
    ! [C_200,A_202,D_199,A_198,B_201] :
      ( r2_hidden(k1_mcart_1(A_198),k3_zfmisc_1(A_202,B_201,C_200))
      | ~ r2_hidden(A_198,k4_zfmisc_1(A_202,B_201,C_200,D_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_48])).

tff(c_1024,plain,(
    r2_hidden(k1_mcart_1(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20')),k3_zfmisc_1('#skF_21','#skF_22','#skF_23')) ),
    inference(resolution,[status(thm)],[c_126,c_1007])).

tff(c_1031,plain,(
    r2_hidden(k3_mcart_1('#skF_17','#skF_18','#skF_19'),k3_zfmisc_1('#skF_21','#skF_22','#skF_23')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_1024])).

tff(c_1033,plain,(
    r2_hidden(k1_mcart_1(k3_mcart_1('#skF_17','#skF_18','#skF_19')),k2_zfmisc_1('#skF_21','#skF_22')) ),
    inference(resolution,[status(thm)],[c_1031,c_103])).

tff(c_1037,plain,(
    r2_hidden(k4_tarski('#skF_17','#skF_18'),k2_zfmisc_1('#skF_21','#skF_22')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_1033])).

tff(c_1041,plain,(
    r2_hidden(k2_mcart_1(k4_tarski('#skF_17','#skF_18')),'#skF_22') ),
    inference(resolution,[status(thm)],[c_1037,c_46])).

tff(c_1045,plain,(
    r2_hidden('#skF_18','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_1041])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_932,c_1045])).

tff(c_1049,plain,(
    r2_hidden('#skF_18','#skF_22') ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_720,plain,
    ( ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_19','#skF_23')
    | r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_730,plain,(
    ~ r2_hidden('#skF_19','#skF_23') ),
    inference(splitLeft,[status(thm)],[c_720])).

tff(c_389,plain,(
    ! [A_40,B_41,C_42] : k2_mcart_1(k3_mcart_1(A_40,B_41,C_42)) = C_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_377])).

tff(c_885,plain,(
    ! [C_187,B_188,A_185,D_186,A_189] :
      ( r2_hidden(k1_mcart_1(A_185),k3_zfmisc_1(A_189,B_188,C_187))
      | ~ r2_hidden(A_185,k4_zfmisc_1(A_189,B_188,C_187,D_186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_48])).

tff(c_908,plain,(
    r2_hidden(k1_mcart_1(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20')),k3_zfmisc_1('#skF_21','#skF_22','#skF_23')) ),
    inference(resolution,[status(thm)],[c_126,c_885])).

tff(c_917,plain,(
    r2_hidden(k3_mcart_1('#skF_17','#skF_18','#skF_19'),k3_zfmisc_1('#skF_21','#skF_22','#skF_23')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_908])).

tff(c_101,plain,(
    ! [A_54,C_71,A_69,B_70] :
      ( r2_hidden(k2_mcart_1(A_54),C_71)
      | ~ r2_hidden(A_54,k3_zfmisc_1(A_69,B_70,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_46])).

tff(c_921,plain,(
    r2_hidden(k2_mcart_1(k3_mcart_1('#skF_17','#skF_18','#skF_19')),'#skF_23') ),
    inference(resolution,[status(thm)],[c_917,c_101])).

tff(c_925,plain,(
    r2_hidden('#skF_19','#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_921])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_925])).

tff(c_928,plain,
    ( ~ r2_hidden('#skF_18','#skF_22')
    | r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_1060,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_928])).

tff(c_929,plain,(
    r2_hidden('#skF_19','#skF_23') ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_56,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_20','#skF_24')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1051,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_18','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_929,c_405,c_56])).

tff(c_1052,plain,(
    ~ r2_hidden('#skF_18','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_1051])).

tff(c_1054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1052])).

tff(c_1055,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(splitRight,[status(thm)],[c_1051])).

tff(c_14,plain,(
    ! [E_38,F_39,A_6,B_7] :
      ( r2_hidden(k4_tarski(E_38,F_39),k2_zfmisc_1(A_6,B_7))
      | ~ r2_hidden(F_39,B_7)
      | ~ r2_hidden(E_38,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1048,plain,
    ( ~ r2_hidden('#skF_19','#skF_23')
    | r2_hidden('#skF_11','#skF_15') ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_1062,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_1048])).

tff(c_40,plain,(
    ! [A_43,B_44,C_45] : k2_zfmisc_1(k2_zfmisc_1(A_43,B_44),C_45) = k3_zfmisc_1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1621,plain,(
    ! [A_257,C_256,E_260,B_258,F_259] :
      ( r2_hidden(k4_tarski(E_260,F_259),k3_zfmisc_1(A_257,B_258,C_256))
      | ~ r2_hidden(F_259,C_256)
      | ~ r2_hidden(E_260,k2_zfmisc_1(A_257,B_258)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_247])).

tff(c_1643,plain,(
    ! [C_42,A_257,C_256,B_258,A_40,B_41] :
      ( r2_hidden(k3_mcart_1(A_40,B_41,C_42),k3_zfmisc_1(A_257,B_258,C_256))
      | ~ r2_hidden(C_42,C_256)
      | ~ r2_hidden(k4_tarski(A_40,B_41),k2_zfmisc_1(A_257,B_258)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1621])).

tff(c_52,plain,
    ( r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_20','#skF_24')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_723,plain,
    ( r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_52])).

tff(c_724,plain,(
    ~ r2_hidden('#skF_17','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_724])).

tff(c_727,plain,
    ( ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_19','#skF_23')
    | r2_hidden('#skF_12','#skF_16') ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_1064,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_1049,c_727])).

tff(c_44,plain,(
    ! [A_50,B_51,C_52,D_53] : k2_zfmisc_1(k3_zfmisc_1(A_50,B_51,C_52),D_53) = k4_zfmisc_1(A_50,B_51,C_52,D_53) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1944,plain,(
    ! [D_313,A_315,B_316,B_312,A_317,C_314] :
      ( r2_hidden(k4_mcart_1(A_317,B_312,C_314,D_313),k2_zfmisc_1(A_315,B_316))
      | ~ r2_hidden(D_313,B_316)
      | ~ r2_hidden(k3_mcart_1(A_317,B_312,C_314),A_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_247])).

tff(c_10259,plain,(
    ! [D_854,D_859,B_858,A_861,C_856,C_857,B_860,A_855] :
      ( r2_hidden(k4_mcart_1(A_861,B_860,C_856,D_854),k4_zfmisc_1(A_855,B_858,C_857,D_859))
      | ~ r2_hidden(D_854,D_859)
      | ~ r2_hidden(k3_mcart_1(A_861,B_860,C_856),k3_zfmisc_1(A_855,B_858,C_857)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1944])).

tff(c_50,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16'))
    | ~ r2_hidden('#skF_20','#skF_24')
    | ~ r2_hidden('#skF_19','#skF_23')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1095,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_1049,c_929,c_405,c_50])).

tff(c_10283,plain,
    ( ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(resolution,[status(thm)],[c_10259,c_1095])).

tff(c_10313,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_10283])).

tff(c_10322,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_1643,c_10313])).

tff(c_10325,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_10322])).

tff(c_10354,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(resolution,[status(thm)],[c_14,c_10325])).

tff(c_10358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1055,c_10354])).

tff(c_10360,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_68,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10612,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_10360,c_68])).

tff(c_66,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10430,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_10360,c_66])).

tff(c_64,plain,
    ( r2_hidden('#skF_11','#skF_15')
    | r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10810,plain,(
    r2_hidden('#skF_11','#skF_15') ),
    inference(negUnitSimplification,[status(thm)],[c_10360,c_64])).

tff(c_10478,plain,(
    ! [E_893,F_894,A_895,B_896] :
      ( r2_hidden(k4_tarski(E_893,F_894),k2_zfmisc_1(A_895,B_896))
      | ~ r2_hidden(F_894,B_896)
      | ~ r2_hidden(E_893,A_895) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_11620,plain,(
    ! [A_1021,B_1020,B_1024,C_1022,A_1023] :
      ( r2_hidden(k3_mcart_1(A_1021,B_1024,C_1022),k2_zfmisc_1(A_1023,B_1020))
      | ~ r2_hidden(C_1022,B_1020)
      | ~ r2_hidden(k4_tarski(A_1021,B_1024),A_1023) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10478])).

tff(c_11640,plain,(
    ! [A_1021,B_1024,C_45,A_43,C_1022,B_44] :
      ( r2_hidden(k3_mcart_1(A_1021,B_1024,C_1022),k3_zfmisc_1(A_43,B_44,C_45))
      | ~ r2_hidden(C_1022,C_45)
      | ~ r2_hidden(k4_tarski(A_1021,B_1024),k2_zfmisc_1(A_43,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_11620])).

tff(c_10359,plain,(
    r2_hidden('#skF_12','#skF_16') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12061,plain,(
    ! [A_1084,B_1082,D_1083,B_1081,C_1085,A_1086] :
      ( r2_hidden(k4_mcart_1(A_1086,B_1082,C_1085,D_1083),k2_zfmisc_1(A_1084,B_1081))
      | ~ r2_hidden(D_1083,B_1081)
      | ~ r2_hidden(k3_mcart_1(A_1086,B_1082,C_1085),A_1084) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_10478])).

tff(c_18615,plain,(
    ! [C_1499,C_1496,A_1494,B_1501,D_1500,D_1497,A_1495,B_1498] :
      ( r2_hidden(k4_mcart_1(A_1494,B_1501,C_1499,D_1497),k4_zfmisc_1(A_1495,B_1498,C_1496,D_1500))
      | ~ r2_hidden(D_1497,D_1500)
      | ~ r2_hidden(k3_mcart_1(A_1494,B_1501,C_1499),k3_zfmisc_1(A_1495,B_1498,C_1496)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_12061])).

tff(c_60,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16'))
    | r2_hidden(k4_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20'),k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11111,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_9','#skF_10','#skF_11','#skF_12'),k4_zfmisc_1('#skF_13','#skF_14','#skF_15','#skF_16')) ),
    inference(negUnitSimplification,[status(thm)],[c_10360,c_60])).

tff(c_18639,plain,
    ( ~ r2_hidden('#skF_12','#skF_16')
    | ~ r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(resolution,[status(thm)],[c_18615,c_11111])).

tff(c_18672,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_9','#skF_10','#skF_11'),k3_zfmisc_1('#skF_13','#skF_14','#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10359,c_18639])).

tff(c_18741,plain,
    ( ~ r2_hidden('#skF_11','#skF_15')
    | ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_11640,c_18672])).

tff(c_18744,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10810,c_18741])).

tff(c_18747,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_9','#skF_13') ),
    inference(resolution,[status(thm)],[c_14,c_18744])).

tff(c_18751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10612,c_10430,c_18747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.76/4.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.76/4.30  
% 11.76/4.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.76/4.30  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_20 > #skF_18 > #skF_17 > #skF_11 > #skF_6 > #skF_15 > #skF_19 > #skF_4 > #skF_10 > #skF_8 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_21 > #skF_9 > #skF_22 > #skF_3 > #skF_2 > #skF_24 > #skF_23 > #skF_1 > #skF_12
% 11.76/4.30  
% 11.76/4.30  %Foreground sorts:
% 11.76/4.30  
% 11.76/4.30  
% 11.76/4.30  %Background operators:
% 11.76/4.30  
% 11.76/4.30  
% 11.76/4.30  %Foreground operators:
% 11.76/4.30  tff('#skF_20', type, '#skF_20': $i).
% 11.76/4.30  tff('#skF_18', type, '#skF_18': $i).
% 11.76/4.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.76/4.30  tff('#skF_17', type, '#skF_17': $i).
% 11.76/4.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.76/4.30  tff('#skF_11', type, '#skF_11': $i).
% 11.76/4.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.76/4.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.76/4.30  tff('#skF_15', type, '#skF_15': $i).
% 11.76/4.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.76/4.30  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.76/4.30  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 11.76/4.30  tff('#skF_19', type, '#skF_19': $i).
% 11.76/4.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.76/4.31  tff('#skF_10', type, '#skF_10': $i).
% 11.76/4.31  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 11.76/4.31  tff('#skF_16', type, '#skF_16': $i).
% 11.76/4.31  tff('#skF_14', type, '#skF_14': $i).
% 11.76/4.31  tff('#skF_13', type, '#skF_13': $i).
% 11.76/4.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.76/4.31  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 11.76/4.31  tff('#skF_21', type, '#skF_21': $i).
% 11.76/4.31  tff('#skF_9', type, '#skF_9': $i).
% 11.76/4.31  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.76/4.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.76/4.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 11.76/4.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.76/4.31  tff('#skF_22', type, '#skF_22': $i).
% 11.76/4.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.76/4.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.76/4.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.76/4.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 11.76/4.31  tff('#skF_24', type, '#skF_24': $i).
% 11.76/4.31  tff('#skF_23', type, '#skF_23': $i).
% 11.76/4.31  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 11.76/4.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.76/4.31  tff('#skF_12', type, '#skF_12': $i).
% 11.76/4.31  
% 11.76/4.33  tff(f_50, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 11.76/4.33  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.76/4.33  tff(f_44, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 11.76/4.33  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 11.76/4.33  tff(f_69, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (r2_hidden(k4_mcart_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) <=> (((r2_hidden(A, E) & r2_hidden(B, F)) & r2_hidden(C, G)) & r2_hidden(D, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_mcart_1)).
% 11.76/4.33  tff(f_52, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 11.76/4.33  tff(f_46, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 11.76/4.33  tff(f_48, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 11.76/4.33  tff(c_42, plain, (![A_46, B_47, C_48, D_49]: (k4_tarski(k3_mcart_1(A_46, B_47, C_48), D_49)=k4_mcart_1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.76/4.33  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.76/4.33  tff(c_247, plain, (![E_109, F_110, A_111, B_112]: (r2_hidden(k4_tarski(E_109, F_110), k2_zfmisc_1(A_111, B_112)) | ~r2_hidden(F_110, B_112) | ~r2_hidden(E_109, A_111))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.76/4.33  tff(c_46, plain, (![A_54, C_56, B_55]: (r2_hidden(k2_mcart_1(A_54), C_56) | ~r2_hidden(A_54, k2_zfmisc_1(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.76/4.33  tff(c_266, plain, (![E_113, F_114, B_115, A_116]: (r2_hidden(k2_mcart_1(k4_tarski(E_113, F_114)), B_115) | ~r2_hidden(F_114, B_115) | ~r2_hidden(E_113, A_116))), inference(resolution, [status(thm)], [c_247, c_46])).
% 11.76/4.33  tff(c_323, plain, (![C_120, F_121, B_122]: (r2_hidden(k2_mcart_1(k4_tarski(C_120, F_121)), B_122) | ~r2_hidden(F_121, B_122))), inference(resolution, [status(thm)], [c_4, c_266])).
% 11.76/4.33  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.76/4.33  tff(c_355, plain, (![C_123, F_124, A_125]: (k2_mcart_1(k4_tarski(C_123, F_124))=A_125 | ~r2_hidden(F_124, k1_tarski(A_125)))), inference(resolution, [status(thm)], [c_323, c_2])).
% 11.76/4.33  tff(c_377, plain, (![C_126, C_127]: (k2_mcart_1(k4_tarski(C_126, C_127))=C_127)), inference(resolution, [status(thm)], [c_4, c_355])).
% 11.76/4.33  tff(c_386, plain, (![A_46, B_47, C_48, D_49]: (k2_mcart_1(k4_mcart_1(A_46, B_47, C_48, D_49))=D_49)), inference(superposition, [status(thm), theory('equality')], [c_42, c_377])).
% 11.76/4.33  tff(c_62, plain, (r2_hidden('#skF_12', '#skF_16') | r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_126, plain, (r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(splitLeft, [status(thm)], [c_62])).
% 11.76/4.33  tff(c_127, plain, (![A_82, B_83, C_84, D_85]: (k2_zfmisc_1(k3_zfmisc_1(A_82, B_83, C_84), D_85)=k4_zfmisc_1(A_82, B_83, C_84, D_85))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.76/4.33  tff(c_143, plain, (![B_89, D_87, C_88, A_86, A_90]: (r2_hidden(k2_mcart_1(A_86), D_87) | ~r2_hidden(A_86, k4_zfmisc_1(A_90, B_89, C_88, D_87)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_46])).
% 11.76/4.33  tff(c_146, plain, (r2_hidden(k2_mcart_1(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20')), '#skF_24')), inference(resolution, [status(thm)], [c_126, c_143])).
% 11.76/4.33  tff(c_405, plain, (r2_hidden('#skF_20', '#skF_24')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_146])).
% 11.76/4.33  tff(c_58, plain, (r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_20', '#skF_24') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_579, plain, (r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_58])).
% 11.76/4.33  tff(c_580, plain, (~r2_hidden('#skF_17', '#skF_21')), inference(splitLeft, [status(thm)], [c_579])).
% 11.76/4.33  tff(c_48, plain, (![A_54, B_55, C_56]: (r2_hidden(k1_mcart_1(A_54), B_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.76/4.33  tff(c_456, plain, (![E_138, F_139, A_140, B_141]: (r2_hidden(k1_mcart_1(k4_tarski(E_138, F_139)), A_140) | ~r2_hidden(F_139, B_141) | ~r2_hidden(E_138, A_140))), inference(resolution, [status(thm)], [c_247, c_48])).
% 11.76/4.33  tff(c_481, plain, (![E_142, C_143, A_144]: (r2_hidden(k1_mcart_1(k4_tarski(E_142, C_143)), A_144) | ~r2_hidden(E_142, A_144))), inference(resolution, [status(thm)], [c_4, c_456])).
% 11.76/4.33  tff(c_514, plain, (![E_145, C_146, A_147]: (k1_mcart_1(k4_tarski(E_145, C_146))=A_147 | ~r2_hidden(E_145, k1_tarski(A_147)))), inference(resolution, [status(thm)], [c_481, c_2])).
% 11.76/4.33  tff(c_537, plain, (![C_5, C_146]: (k1_mcart_1(k4_tarski(C_5, C_146))=C_5)), inference(resolution, [status(thm)], [c_4, c_514])).
% 11.76/4.33  tff(c_38, plain, (![A_40, B_41, C_42]: (k4_tarski(k4_tarski(A_40, B_41), C_42)=k3_mcart_1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.76/4.33  tff(c_540, plain, (![C_148, C_149]: (k1_mcart_1(k4_tarski(C_148, C_149))=C_148)), inference(resolution, [status(thm)], [c_4, c_514])).
% 11.76/4.33  tff(c_552, plain, (![A_40, B_41, C_42]: (k1_mcart_1(k3_mcart_1(A_40, B_41, C_42))=k4_tarski(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_38, c_540])).
% 11.76/4.33  tff(c_549, plain, (![A_46, B_47, C_48, D_49]: (k1_mcart_1(k4_mcart_1(A_46, B_47, C_48, D_49))=k3_mcart_1(A_46, B_47, C_48))), inference(superposition, [status(thm), theory('equality')], [c_42, c_540])).
% 11.76/4.33  tff(c_651, plain, (![C_166, B_167, D_165, A_164, A_168]: (r2_hidden(k1_mcart_1(A_164), k3_zfmisc_1(A_168, B_167, C_166)) | ~r2_hidden(A_164, k4_zfmisc_1(A_168, B_167, C_166, D_165)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_48])).
% 11.76/4.33  tff(c_665, plain, (r2_hidden(k1_mcart_1(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20')), k3_zfmisc_1('#skF_21', '#skF_22', '#skF_23'))), inference(resolution, [status(thm)], [c_126, c_651])).
% 11.76/4.33  tff(c_671, plain, (r2_hidden(k3_mcart_1('#skF_17', '#skF_18', '#skF_19'), k3_zfmisc_1('#skF_21', '#skF_22', '#skF_23'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_665])).
% 11.76/4.33  tff(c_93, plain, (![A_69, B_70, C_71]: (k2_zfmisc_1(k2_zfmisc_1(A_69, B_70), C_71)=k3_zfmisc_1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.76/4.33  tff(c_103, plain, (![A_54, A_69, B_70, C_71]: (r2_hidden(k1_mcart_1(A_54), k2_zfmisc_1(A_69, B_70)) | ~r2_hidden(A_54, k3_zfmisc_1(A_69, B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_48])).
% 11.76/4.33  tff(c_703, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_17', '#skF_18', '#skF_19')), k2_zfmisc_1('#skF_21', '#skF_22'))), inference(resolution, [status(thm)], [c_671, c_103])).
% 11.76/4.33  tff(c_707, plain, (r2_hidden(k4_tarski('#skF_17', '#skF_18'), k2_zfmisc_1('#skF_21', '#skF_22'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_703])).
% 11.76/4.33  tff(c_713, plain, (r2_hidden(k1_mcart_1(k4_tarski('#skF_17', '#skF_18')), '#skF_21')), inference(resolution, [status(thm)], [c_707, c_48])).
% 11.76/4.33  tff(c_717, plain, (r2_hidden('#skF_17', '#skF_21')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_713])).
% 11.76/4.33  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_580, c_717])).
% 11.76/4.33  tff(c_721, plain, (r2_hidden('#skF_17', '#skF_21')), inference(splitRight, [status(thm)], [c_579])).
% 11.76/4.33  tff(c_54, plain, (r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_20', '#skF_24') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_931, plain, (r2_hidden('#skF_11', '#skF_15') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22')), inference(demodulation, [status(thm), theory('equality')], [c_721, c_405, c_54])).
% 11.76/4.33  tff(c_932, plain, (~r2_hidden('#skF_18', '#skF_22')), inference(splitLeft, [status(thm)], [c_931])).
% 11.76/4.33  tff(c_374, plain, (![C_123, C_5]: (k2_mcart_1(k4_tarski(C_123, C_5))=C_5)), inference(resolution, [status(thm)], [c_4, c_355])).
% 11.76/4.33  tff(c_1007, plain, (![C_200, A_202, D_199, A_198, B_201]: (r2_hidden(k1_mcart_1(A_198), k3_zfmisc_1(A_202, B_201, C_200)) | ~r2_hidden(A_198, k4_zfmisc_1(A_202, B_201, C_200, D_199)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_48])).
% 11.76/4.33  tff(c_1024, plain, (r2_hidden(k1_mcart_1(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20')), k3_zfmisc_1('#skF_21', '#skF_22', '#skF_23'))), inference(resolution, [status(thm)], [c_126, c_1007])).
% 11.76/4.33  tff(c_1031, plain, (r2_hidden(k3_mcart_1('#skF_17', '#skF_18', '#skF_19'), k3_zfmisc_1('#skF_21', '#skF_22', '#skF_23'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_1024])).
% 11.76/4.33  tff(c_1033, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_17', '#skF_18', '#skF_19')), k2_zfmisc_1('#skF_21', '#skF_22'))), inference(resolution, [status(thm)], [c_1031, c_103])).
% 11.76/4.33  tff(c_1037, plain, (r2_hidden(k4_tarski('#skF_17', '#skF_18'), k2_zfmisc_1('#skF_21', '#skF_22'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_1033])).
% 11.76/4.33  tff(c_1041, plain, (r2_hidden(k2_mcart_1(k4_tarski('#skF_17', '#skF_18')), '#skF_22')), inference(resolution, [status(thm)], [c_1037, c_46])).
% 11.76/4.33  tff(c_1045, plain, (r2_hidden('#skF_18', '#skF_22')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_1041])).
% 11.76/4.33  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_932, c_1045])).
% 11.76/4.33  tff(c_1049, plain, (r2_hidden('#skF_18', '#skF_22')), inference(splitRight, [status(thm)], [c_931])).
% 11.76/4.33  tff(c_720, plain, (~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_19', '#skF_23') | r2_hidden('#skF_9', '#skF_13')), inference(splitRight, [status(thm)], [c_579])).
% 11.76/4.33  tff(c_730, plain, (~r2_hidden('#skF_19', '#skF_23')), inference(splitLeft, [status(thm)], [c_720])).
% 11.76/4.33  tff(c_389, plain, (![A_40, B_41, C_42]: (k2_mcart_1(k3_mcart_1(A_40, B_41, C_42))=C_42)), inference(superposition, [status(thm), theory('equality')], [c_38, c_377])).
% 11.76/4.33  tff(c_885, plain, (![C_187, B_188, A_185, D_186, A_189]: (r2_hidden(k1_mcart_1(A_185), k3_zfmisc_1(A_189, B_188, C_187)) | ~r2_hidden(A_185, k4_zfmisc_1(A_189, B_188, C_187, D_186)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_48])).
% 11.76/4.33  tff(c_908, plain, (r2_hidden(k1_mcart_1(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20')), k3_zfmisc_1('#skF_21', '#skF_22', '#skF_23'))), inference(resolution, [status(thm)], [c_126, c_885])).
% 11.76/4.33  tff(c_917, plain, (r2_hidden(k3_mcart_1('#skF_17', '#skF_18', '#skF_19'), k3_zfmisc_1('#skF_21', '#skF_22', '#skF_23'))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_908])).
% 11.76/4.33  tff(c_101, plain, (![A_54, C_71, A_69, B_70]: (r2_hidden(k2_mcart_1(A_54), C_71) | ~r2_hidden(A_54, k3_zfmisc_1(A_69, B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_46])).
% 11.76/4.33  tff(c_921, plain, (r2_hidden(k2_mcart_1(k3_mcart_1('#skF_17', '#skF_18', '#skF_19')), '#skF_23')), inference(resolution, [status(thm)], [c_917, c_101])).
% 11.76/4.33  tff(c_925, plain, (r2_hidden('#skF_19', '#skF_23')), inference(demodulation, [status(thm), theory('equality')], [c_389, c_921])).
% 11.76/4.33  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_730, c_925])).
% 11.76/4.33  tff(c_928, plain, (~r2_hidden('#skF_18', '#skF_22') | r2_hidden('#skF_9', '#skF_13')), inference(splitRight, [status(thm)], [c_720])).
% 11.76/4.33  tff(c_1060, plain, (r2_hidden('#skF_9', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_928])).
% 11.76/4.33  tff(c_929, plain, (r2_hidden('#skF_19', '#skF_23')), inference(splitRight, [status(thm)], [c_720])).
% 11.76/4.33  tff(c_56, plain, (r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_20', '#skF_24') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_1051, plain, (r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_18', '#skF_22')), inference(demodulation, [status(thm), theory('equality')], [c_721, c_929, c_405, c_56])).
% 11.76/4.33  tff(c_1052, plain, (~r2_hidden('#skF_18', '#skF_22')), inference(splitLeft, [status(thm)], [c_1051])).
% 11.76/4.33  tff(c_1054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1052])).
% 11.76/4.33  tff(c_1055, plain, (r2_hidden('#skF_10', '#skF_14')), inference(splitRight, [status(thm)], [c_1051])).
% 11.76/4.33  tff(c_14, plain, (![E_38, F_39, A_6, B_7]: (r2_hidden(k4_tarski(E_38, F_39), k2_zfmisc_1(A_6, B_7)) | ~r2_hidden(F_39, B_7) | ~r2_hidden(E_38, A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.76/4.33  tff(c_1048, plain, (~r2_hidden('#skF_19', '#skF_23') | r2_hidden('#skF_11', '#skF_15')), inference(splitRight, [status(thm)], [c_931])).
% 11.76/4.33  tff(c_1062, plain, (r2_hidden('#skF_11', '#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_929, c_1048])).
% 11.76/4.33  tff(c_40, plain, (![A_43, B_44, C_45]: (k2_zfmisc_1(k2_zfmisc_1(A_43, B_44), C_45)=k3_zfmisc_1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.76/4.33  tff(c_1621, plain, (![A_257, C_256, E_260, B_258, F_259]: (r2_hidden(k4_tarski(E_260, F_259), k3_zfmisc_1(A_257, B_258, C_256)) | ~r2_hidden(F_259, C_256) | ~r2_hidden(E_260, k2_zfmisc_1(A_257, B_258)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_247])).
% 11.76/4.33  tff(c_1643, plain, (![C_42, A_257, C_256, B_258, A_40, B_41]: (r2_hidden(k3_mcart_1(A_40, B_41, C_42), k3_zfmisc_1(A_257, B_258, C_256)) | ~r2_hidden(C_42, C_256) | ~r2_hidden(k4_tarski(A_40, B_41), k2_zfmisc_1(A_257, B_258)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1621])).
% 11.76/4.33  tff(c_52, plain, (r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_20', '#skF_24') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_723, plain, (r2_hidden('#skF_12', '#skF_16') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_52])).
% 11.76/4.33  tff(c_724, plain, (~r2_hidden('#skF_17', '#skF_21')), inference(splitLeft, [status(thm)], [c_723])).
% 11.76/4.33  tff(c_726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_721, c_724])).
% 11.76/4.33  tff(c_727, plain, (~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_19', '#skF_23') | r2_hidden('#skF_12', '#skF_16')), inference(splitRight, [status(thm)], [c_723])).
% 11.76/4.33  tff(c_1064, plain, (r2_hidden('#skF_12', '#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_929, c_1049, c_727])).
% 11.76/4.33  tff(c_44, plain, (![A_50, B_51, C_52, D_53]: (k2_zfmisc_1(k3_zfmisc_1(A_50, B_51, C_52), D_53)=k4_zfmisc_1(A_50, B_51, C_52, D_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.76/4.33  tff(c_1944, plain, (![D_313, A_315, B_316, B_312, A_317, C_314]: (r2_hidden(k4_mcart_1(A_317, B_312, C_314, D_313), k2_zfmisc_1(A_315, B_316)) | ~r2_hidden(D_313, B_316) | ~r2_hidden(k3_mcart_1(A_317, B_312, C_314), A_315))), inference(superposition, [status(thm), theory('equality')], [c_42, c_247])).
% 11.76/4.33  tff(c_10259, plain, (![D_854, D_859, B_858, A_861, C_856, C_857, B_860, A_855]: (r2_hidden(k4_mcart_1(A_861, B_860, C_856, D_854), k4_zfmisc_1(A_855, B_858, C_857, D_859)) | ~r2_hidden(D_854, D_859) | ~r2_hidden(k3_mcart_1(A_861, B_860, C_856), k3_zfmisc_1(A_855, B_858, C_857)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1944])).
% 11.76/4.33  tff(c_50, plain, (~r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16')) | ~r2_hidden('#skF_20', '#skF_24') | ~r2_hidden('#skF_19', '#skF_23') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21')), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_1095, plain, (~r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_1049, c_929, c_405, c_50])).
% 11.76/4.33  tff(c_10283, plain, (~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(resolution, [status(thm)], [c_10259, c_1095])).
% 11.76/4.33  tff(c_10313, plain, (~r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_10283])).
% 11.76/4.33  tff(c_10322, plain, (~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_1643, c_10313])).
% 11.76/4.33  tff(c_10325, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_10322])).
% 11.76/4.33  tff(c_10354, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(resolution, [status(thm)], [c_14, c_10325])).
% 11.76/4.33  tff(c_10358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1055, c_10354])).
% 11.76/4.33  tff(c_10360, plain, (~r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(splitRight, [status(thm)], [c_62])).
% 11.76/4.33  tff(c_68, plain, (r2_hidden('#skF_9', '#skF_13') | r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_10612, plain, (r2_hidden('#skF_9', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_10360, c_68])).
% 11.76/4.33  tff(c_66, plain, (r2_hidden('#skF_10', '#skF_14') | r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_10430, plain, (r2_hidden('#skF_10', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_10360, c_66])).
% 11.76/4.33  tff(c_64, plain, (r2_hidden('#skF_11', '#skF_15') | r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_10810, plain, (r2_hidden('#skF_11', '#skF_15')), inference(negUnitSimplification, [status(thm)], [c_10360, c_64])).
% 11.76/4.33  tff(c_10478, plain, (![E_893, F_894, A_895, B_896]: (r2_hidden(k4_tarski(E_893, F_894), k2_zfmisc_1(A_895, B_896)) | ~r2_hidden(F_894, B_896) | ~r2_hidden(E_893, A_895))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.76/4.33  tff(c_11620, plain, (![A_1021, B_1020, B_1024, C_1022, A_1023]: (r2_hidden(k3_mcart_1(A_1021, B_1024, C_1022), k2_zfmisc_1(A_1023, B_1020)) | ~r2_hidden(C_1022, B_1020) | ~r2_hidden(k4_tarski(A_1021, B_1024), A_1023))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10478])).
% 11.76/4.33  tff(c_11640, plain, (![A_1021, B_1024, C_45, A_43, C_1022, B_44]: (r2_hidden(k3_mcart_1(A_1021, B_1024, C_1022), k3_zfmisc_1(A_43, B_44, C_45)) | ~r2_hidden(C_1022, C_45) | ~r2_hidden(k4_tarski(A_1021, B_1024), k2_zfmisc_1(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_11620])).
% 11.76/4.33  tff(c_10359, plain, (r2_hidden('#skF_12', '#skF_16')), inference(splitRight, [status(thm)], [c_62])).
% 11.76/4.33  tff(c_12061, plain, (![A_1084, B_1082, D_1083, B_1081, C_1085, A_1086]: (r2_hidden(k4_mcart_1(A_1086, B_1082, C_1085, D_1083), k2_zfmisc_1(A_1084, B_1081)) | ~r2_hidden(D_1083, B_1081) | ~r2_hidden(k3_mcart_1(A_1086, B_1082, C_1085), A_1084))), inference(superposition, [status(thm), theory('equality')], [c_42, c_10478])).
% 11.76/4.33  tff(c_18615, plain, (![C_1499, C_1496, A_1494, B_1501, D_1500, D_1497, A_1495, B_1498]: (r2_hidden(k4_mcart_1(A_1494, B_1501, C_1499, D_1497), k4_zfmisc_1(A_1495, B_1498, C_1496, D_1500)) | ~r2_hidden(D_1497, D_1500) | ~r2_hidden(k3_mcart_1(A_1494, B_1501, C_1499), k3_zfmisc_1(A_1495, B_1498, C_1496)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_12061])).
% 11.76/4.33  tff(c_60, plain, (~r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16')) | r2_hidden(k4_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'), k4_zfmisc_1('#skF_21', '#skF_22', '#skF_23', '#skF_24'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.76/4.33  tff(c_11111, plain, (~r2_hidden(k4_mcart_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'), k4_zfmisc_1('#skF_13', '#skF_14', '#skF_15', '#skF_16'))), inference(negUnitSimplification, [status(thm)], [c_10360, c_60])).
% 11.76/4.33  tff(c_18639, plain, (~r2_hidden('#skF_12', '#skF_16') | ~r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(resolution, [status(thm)], [c_18615, c_11111])).
% 11.76/4.33  tff(c_18672, plain, (~r2_hidden(k3_mcart_1('#skF_9', '#skF_10', '#skF_11'), k3_zfmisc_1('#skF_13', '#skF_14', '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_10359, c_18639])).
% 11.76/4.33  tff(c_18741, plain, (~r2_hidden('#skF_11', '#skF_15') | ~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_11640, c_18672])).
% 11.76/4.33  tff(c_18744, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_10810, c_18741])).
% 11.76/4.33  tff(c_18747, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_9', '#skF_13')), inference(resolution, [status(thm)], [c_14, c_18744])).
% 11.76/4.33  tff(c_18751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10612, c_10430, c_18747])).
% 11.76/4.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.76/4.33  
% 11.76/4.33  Inference rules
% 11.76/4.33  ----------------------
% 11.76/4.33  #Ref     : 0
% 11.76/4.33  #Sup     : 4254
% 11.76/4.33  #Fact    : 0
% 11.76/4.33  #Define  : 0
% 11.76/4.33  #Split   : 21
% 11.76/4.33  #Chain   : 0
% 11.76/4.33  #Close   : 0
% 11.76/4.33  
% 11.76/4.33  Ordering : KBO
% 11.76/4.33  
% 11.76/4.33  Simplification rules
% 11.76/4.33  ----------------------
% 11.76/4.33  #Subsume      : 1220
% 11.76/4.33  #Demod        : 2911
% 11.76/4.33  #Tautology    : 540
% 11.76/4.33  #SimpNegUnit  : 506
% 11.76/4.33  #BackRed      : 213
% 11.76/4.33  
% 11.76/4.33  #Partial instantiations: 0
% 11.76/4.33  #Strategies tried      : 1
% 11.76/4.33  
% 11.76/4.33  Timing (in seconds)
% 11.76/4.33  ----------------------
% 11.96/4.33  Preprocessing        : 0.30
% 11.96/4.33  Parsing              : 0.15
% 11.96/4.33  CNF conversion       : 0.03
% 11.96/4.33  Main loop            : 3.26
% 11.96/4.33  Inferencing          : 1.04
% 11.96/4.33  Reduction            : 1.09
% 11.96/4.33  Demodulation         : 0.83
% 11.96/4.33  BG Simplification    : 0.18
% 11.96/4.33  Subsumption          : 0.67
% 11.96/4.33  Abstraction          : 0.28
% 11.96/4.33  MUC search           : 0.00
% 11.96/4.33  Cooper               : 0.00
% 11.96/4.33  Total                : 3.60
% 11.96/4.33  Index Insertion      : 0.00
% 11.96/4.33  Index Deletion       : 0.00
% 11.96/4.33  Index Matching       : 0.00
% 11.96/4.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
