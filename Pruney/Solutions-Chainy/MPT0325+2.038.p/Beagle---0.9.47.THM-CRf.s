%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 8.36s
% Output     : CNFRefutation 8.36s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 269 expanded)
%              Number of leaves         :   34 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 472 expanded)
%              Number of equality atoms :   50 ( 149 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_11','#skF_13')
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_393,plain,(
    ! [A_119,B_120,D_121] :
      ( r2_hidden('#skF_9'(A_119,B_120,k2_zfmisc_1(A_119,B_120),D_121),B_120)
      | ~ r2_hidden(D_121,k2_zfmisc_1(A_119,B_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_91,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_109,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_106])).

tff(c_110,plain,(
    ! [A_71] : k4_xboole_0(A_71,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_106])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [A_71] : k4_xboole_0(A_71,k1_xboole_0) = k3_xboole_0(A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_18])).

tff(c_127,plain,(
    ! [A_71] : k3_xboole_0(A_71,A_71) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_150,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_188,plain,(
    ! [A_81,C_82] :
      ( ~ r1_xboole_0(A_81,A_81)
      | ~ r2_hidden(C_82,A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_150])).

tff(c_191,plain,(
    ! [C_82,B_18] :
      ( ~ r2_hidden(C_82,B_18)
      | k4_xboole_0(B_18,B_18) != B_18 ) ),
    inference(resolution,[status(thm)],[c_22,c_188])).

tff(c_193,plain,(
    ! [C_82,B_18] :
      ( ~ r2_hidden(C_82,B_18)
      | k1_xboole_0 != B_18 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_191])).

tff(c_774,plain,(
    ! [B_143,D_144,A_145] :
      ( k1_xboole_0 != B_143
      | ~ r2_hidden(D_144,k2_zfmisc_1(A_145,B_143)) ) ),
    inference(resolution,[status(thm)],[c_393,c_193])).

tff(c_838,plain,(
    ! [B_146,A_147] :
      ( k1_xboole_0 != B_146
      | k2_zfmisc_1(A_147,B_146) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_774])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_889,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_56])).

tff(c_486,plain,(
    ! [A_126,B_127,D_128] :
      ( r2_hidden('#skF_8'(A_126,B_127,k2_zfmisc_1(A_126,B_127),D_128),A_126)
      | ~ r2_hidden(D_128,k2_zfmisc_1(A_126,B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_164,plain,(
    ! [A_13,C_75] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_75,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_167,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_508,plain,(
    ! [D_129,B_130] : ~ r2_hidden(D_129,k2_zfmisc_1(k1_xboole_0,B_130)) ),
    inference(resolution,[status(thm)],[c_486,c_167])).

tff(c_546,plain,(
    ! [B_130] : k2_zfmisc_1(k1_xboole_0,B_130) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_508])).

tff(c_584,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_5'(A_132,B_133,C_134),A_132)
      | r2_hidden('#skF_7'(A_132,B_133,C_134),C_134)
      | k2_zfmisc_1(A_132,B_133) = C_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_593,plain,(
    ! [B_133,C_134] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_133,C_134),C_134)
      | k2_zfmisc_1(k1_xboole_0,B_133) = C_134 ) ),
    inference(resolution,[status(thm)],[c_584,c_167])).

tff(c_612,plain,(
    ! [B_133,C_134] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_133,C_134),C_134)
      | k1_xboole_0 = C_134 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_593])).

tff(c_58,plain,(
    r1_tarski(k2_zfmisc_1('#skF_10','#skF_11'),k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_319,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( r2_hidden(k4_tarski(A_111,B_112),k2_zfmisc_1(C_113,D_114))
      | ~ r2_hidden(B_112,D_114)
      | ~ r2_hidden(A_111,C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4801,plain,(
    ! [C_349,D_350,A_352,B_353,B_351] :
      ( r2_hidden(k4_tarski(A_352,B_353),B_351)
      | ~ r1_tarski(k2_zfmisc_1(C_349,D_350),B_351)
      | ~ r2_hidden(B_353,D_350)
      | ~ r2_hidden(A_352,C_349) ) ),
    inference(resolution,[status(thm)],[c_319,c_2])).

tff(c_5035,plain,(
    ! [A_360,B_361] :
      ( r2_hidden(k4_tarski(A_360,B_361),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_361,'#skF_11')
      | ~ r2_hidden(A_360,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_58,c_4801])).

tff(c_52,plain,(
    ! [A_53,C_55,B_54,D_56] :
      ( r2_hidden(A_53,C_55)
      | ~ r2_hidden(k4_tarski(A_53,B_54),k2_zfmisc_1(C_55,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5075,plain,(
    ! [A_360,B_361] :
      ( r2_hidden(A_360,'#skF_12')
      | ~ r2_hidden(B_361,'#skF_11')
      | ~ r2_hidden(A_360,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_5035,c_52])).

tff(c_5415,plain,(
    ! [B_373] : ~ r2_hidden(B_373,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_5075])).

tff(c_5431,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_612,c_5415])).

tff(c_5478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_889,c_5431])).

tff(c_5480,plain,(
    ! [A_374] :
      ( r2_hidden(A_374,'#skF_12')
      | ~ r2_hidden(A_374,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_5075])).

tff(c_6692,plain,(
    ! [B_411] :
      ( r2_hidden('#skF_1'('#skF_10',B_411),'#skF_12')
      | r1_tarski('#skF_10',B_411) ) ),
    inference(resolution,[status(thm)],[c_6,c_5480])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6704,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_6692,c_4])).

tff(c_6711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_6704])).

tff(c_6713,plain,(
    ! [A_412] : ~ r1_xboole_0(A_412,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_6717,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) != A_17 ),
    inference(resolution,[status(thm)],[c_22,c_6713])).

tff(c_6721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6717])).

tff(c_6722,plain,(
    ~ r1_tarski('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_7238,plain,(
    ! [A_486,B_487,D_488] :
      ( r2_hidden('#skF_8'(A_486,B_487,k2_zfmisc_1(A_486,B_487),D_488),A_486)
      | ~ r2_hidden(D_488,k2_zfmisc_1(A_486,B_487)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6753,plain,(
    ! [A_425,B_426] : k4_xboole_0(A_425,k4_xboole_0(A_425,B_426)) = k3_xboole_0(A_425,B_426) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6768,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6753])).

tff(c_6771,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6768])).

tff(c_6772,plain,(
    ! [A_427] : k4_xboole_0(A_427,A_427) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6768])).

tff(c_6777,plain,(
    ! [A_427] : k4_xboole_0(A_427,k1_xboole_0) = k3_xboole_0(A_427,A_427) ),
    inference(superposition,[status(thm),theory(equality)],[c_6772,c_18])).

tff(c_6811,plain,(
    ! [A_432] : k3_xboole_0(A_432,A_432) = A_432 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6777])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6840,plain,(
    ! [A_436,C_437] :
      ( ~ r1_xboole_0(A_436,A_436)
      | ~ r2_hidden(C_437,A_436) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6811,c_10])).

tff(c_6843,plain,(
    ! [C_437,B_18] :
      ( ~ r2_hidden(C_437,B_18)
      | k4_xboole_0(B_18,B_18) != B_18 ) ),
    inference(resolution,[status(thm)],[c_22,c_6840])).

tff(c_6845,plain,(
    ! [C_437,B_18] :
      ( ~ r2_hidden(C_437,B_18)
      | k1_xboole_0 != B_18 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6771,c_6843])).

tff(c_7378,plain,(
    ! [A_498,D_499,B_500] :
      ( k1_xboole_0 != A_498
      | ~ r2_hidden(D_499,k2_zfmisc_1(A_498,B_500)) ) ),
    inference(resolution,[status(thm)],[c_7238,c_6845])).

tff(c_7432,plain,(
    ! [A_501,B_502] :
      ( k1_xboole_0 != A_501
      | k2_zfmisc_1(A_501,B_502) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_7378])).

tff(c_7480,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_7432,c_56])).

tff(c_7430,plain,(
    ! [B_500] : k2_zfmisc_1(k1_xboole_0,B_500) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_7378])).

tff(c_7483,plain,(
    ! [A_503,B_504,C_505] :
      ( r2_hidden('#skF_5'(A_503,B_504,C_505),A_503)
      | r2_hidden('#skF_7'(A_503,B_504,C_505),C_505)
      | k2_zfmisc_1(A_503,B_504) = C_505 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6731,plain,(
    ! [A_419,B_420,C_421] :
      ( ~ r1_xboole_0(A_419,B_420)
      | ~ r2_hidden(C_421,k3_xboole_0(A_419,B_420)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6738,plain,(
    ! [A_13,C_421] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_421,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6731])).

tff(c_6740,plain,(
    ! [C_421] : ~ r2_hidden(C_421,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_6738])).

tff(c_7496,plain,(
    ! [B_504,C_505] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_504,C_505),C_505)
      | k2_zfmisc_1(k1_xboole_0,B_504) = C_505 ) ),
    inference(resolution,[status(thm)],[c_7483,c_6740])).

tff(c_7520,plain,(
    ! [B_504,C_505] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_504,C_505),C_505)
      | k1_xboole_0 = C_505 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7430,c_7496])).

tff(c_7029,plain,(
    ! [A_468,B_469,C_470,D_471] :
      ( r2_hidden(k4_tarski(A_468,B_469),k2_zfmisc_1(C_470,D_471))
      | ~ r2_hidden(B_469,D_471)
      | ~ r2_hidden(A_468,C_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10884,plain,(
    ! [C_677,D_675,B_674,B_673,A_676] :
      ( r2_hidden(k4_tarski(A_676,B_673),B_674)
      | ~ r1_tarski(k2_zfmisc_1(C_677,D_675),B_674)
      | ~ r2_hidden(B_673,D_675)
      | ~ r2_hidden(A_676,C_677) ) ),
    inference(resolution,[status(thm)],[c_7029,c_2])).

tff(c_11700,plain,(
    ! [A_698,B_699] :
      ( r2_hidden(k4_tarski(A_698,B_699),k2_zfmisc_1('#skF_12','#skF_13'))
      | ~ r2_hidden(B_699,'#skF_11')
      | ~ r2_hidden(A_698,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_58,c_10884])).

tff(c_50,plain,(
    ! [B_54,D_56,A_53,C_55] :
      ( r2_hidden(B_54,D_56)
      | ~ r2_hidden(k4_tarski(A_53,B_54),k2_zfmisc_1(C_55,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11745,plain,(
    ! [B_699,A_698] :
      ( r2_hidden(B_699,'#skF_13')
      | ~ r2_hidden(B_699,'#skF_11')
      | ~ r2_hidden(A_698,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_11700,c_50])).

tff(c_12110,plain,(
    ! [A_710] : ~ r2_hidden(A_710,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_11745])).

tff(c_12134,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_7520,c_12110])).

tff(c_12183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7480,c_12134])).

tff(c_12185,plain,(
    ! [B_711] :
      ( r2_hidden(B_711,'#skF_13')
      | ~ r2_hidden(B_711,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_11745])).

tff(c_13286,plain,(
    ! [B_748] :
      ( r2_hidden('#skF_1'('#skF_11',B_748),'#skF_13')
      | r1_tarski('#skF_11',B_748) ) ),
    inference(resolution,[status(thm)],[c_6,c_12185])).

tff(c_13298,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_13286,c_4])).

tff(c_13305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6722,c_6722,c_13298])).

tff(c_13307,plain,(
    ! [A_749] : ~ r1_xboole_0(A_749,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6738])).

tff(c_13311,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) != A_17 ),
    inference(resolution,[status(thm)],[c_22,c_13307])).

tff(c_13315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_13311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.36/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.87  
% 8.36/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 8.36/2.87  
% 8.36/2.87  %Foreground sorts:
% 8.36/2.87  
% 8.36/2.87  
% 8.36/2.87  %Background operators:
% 8.36/2.87  
% 8.36/2.87  
% 8.36/2.87  %Foreground operators:
% 8.36/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.36/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.36/2.87  tff('#skF_11', type, '#skF_11': $i).
% 8.36/2.87  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.36/2.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.36/2.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.36/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.36/2.87  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 8.36/2.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.36/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.36/2.87  tff('#skF_10', type, '#skF_10': $i).
% 8.36/2.87  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 8.36/2.87  tff('#skF_13', type, '#skF_13': $i).
% 8.36/2.87  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.36/2.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.36/2.87  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.36/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.36/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.36/2.87  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.36/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.36/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.36/2.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.36/2.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.36/2.87  tff('#skF_12', type, '#skF_12': $i).
% 8.36/2.87  
% 8.36/2.90  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.36/2.90  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.36/2.90  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 8.36/2.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.36/2.90  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.36/2.90  tff(f_76, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.36/2.90  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.36/2.90  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.36/2.90  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.36/2.90  tff(f_82, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.36/2.90  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.36/2.90  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.36/2.90  tff(c_54, plain, (~r1_tarski('#skF_11', '#skF_13') | ~r1_tarski('#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/2.90  tff(c_76, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_54])).
% 8.36/2.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.36/2.90  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.36/2.90  tff(c_393, plain, (![A_119, B_120, D_121]: (r2_hidden('#skF_9'(A_119, B_120, k2_zfmisc_1(A_119, B_120), D_121), B_120) | ~r2_hidden(D_121, k2_zfmisc_1(A_119, B_120)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.36/2.90  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.36/2.90  tff(c_91, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.36/2.90  tff(c_106, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_91])).
% 8.36/2.90  tff(c_109, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_106])).
% 8.36/2.90  tff(c_110, plain, (![A_71]: (k4_xboole_0(A_71, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_106])).
% 8.36/2.90  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.36/2.90  tff(c_115, plain, (![A_71]: (k4_xboole_0(A_71, k1_xboole_0)=k3_xboole_0(A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_110, c_18])).
% 8.36/2.90  tff(c_127, plain, (![A_71]: (k3_xboole_0(A_71, A_71)=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 8.36/2.90  tff(c_150, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.36/2.90  tff(c_188, plain, (![A_81, C_82]: (~r1_xboole_0(A_81, A_81) | ~r2_hidden(C_82, A_81))), inference(superposition, [status(thm), theory('equality')], [c_127, c_150])).
% 8.36/2.90  tff(c_191, plain, (![C_82, B_18]: (~r2_hidden(C_82, B_18) | k4_xboole_0(B_18, B_18)!=B_18)), inference(resolution, [status(thm)], [c_22, c_188])).
% 8.36/2.90  tff(c_193, plain, (![C_82, B_18]: (~r2_hidden(C_82, B_18) | k1_xboole_0!=B_18)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_191])).
% 8.36/2.90  tff(c_774, plain, (![B_143, D_144, A_145]: (k1_xboole_0!=B_143 | ~r2_hidden(D_144, k2_zfmisc_1(A_145, B_143)))), inference(resolution, [status(thm)], [c_393, c_193])).
% 8.36/2.90  tff(c_838, plain, (![B_146, A_147]: (k1_xboole_0!=B_146 | k2_zfmisc_1(A_147, B_146)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_774])).
% 8.36/2.90  tff(c_56, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/2.90  tff(c_889, plain, (k1_xboole_0!='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_838, c_56])).
% 8.36/2.90  tff(c_486, plain, (![A_126, B_127, D_128]: (r2_hidden('#skF_8'(A_126, B_127, k2_zfmisc_1(A_126, B_127), D_128), A_126) | ~r2_hidden(D_128, k2_zfmisc_1(A_126, B_127)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.36/2.90  tff(c_164, plain, (![A_13, C_75]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_150])).
% 8.36/2.90  tff(c_167, plain, (![C_75]: (~r2_hidden(C_75, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_164])).
% 8.36/2.90  tff(c_508, plain, (![D_129, B_130]: (~r2_hidden(D_129, k2_zfmisc_1(k1_xboole_0, B_130)))), inference(resolution, [status(thm)], [c_486, c_167])).
% 8.36/2.90  tff(c_546, plain, (![B_130]: (k2_zfmisc_1(k1_xboole_0, B_130)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_508])).
% 8.36/2.90  tff(c_584, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_5'(A_132, B_133, C_134), A_132) | r2_hidden('#skF_7'(A_132, B_133, C_134), C_134) | k2_zfmisc_1(A_132, B_133)=C_134)), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.36/2.90  tff(c_593, plain, (![B_133, C_134]: (r2_hidden('#skF_7'(k1_xboole_0, B_133, C_134), C_134) | k2_zfmisc_1(k1_xboole_0, B_133)=C_134)), inference(resolution, [status(thm)], [c_584, c_167])).
% 8.36/2.90  tff(c_612, plain, (![B_133, C_134]: (r2_hidden('#skF_7'(k1_xboole_0, B_133, C_134), C_134) | k1_xboole_0=C_134)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_593])).
% 8.36/2.90  tff(c_58, plain, (r1_tarski(k2_zfmisc_1('#skF_10', '#skF_11'), k2_zfmisc_1('#skF_12', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/2.90  tff(c_319, plain, (![A_111, B_112, C_113, D_114]: (r2_hidden(k4_tarski(A_111, B_112), k2_zfmisc_1(C_113, D_114)) | ~r2_hidden(B_112, D_114) | ~r2_hidden(A_111, C_113))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.36/2.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.36/2.90  tff(c_4801, plain, (![C_349, D_350, A_352, B_353, B_351]: (r2_hidden(k4_tarski(A_352, B_353), B_351) | ~r1_tarski(k2_zfmisc_1(C_349, D_350), B_351) | ~r2_hidden(B_353, D_350) | ~r2_hidden(A_352, C_349))), inference(resolution, [status(thm)], [c_319, c_2])).
% 8.36/2.90  tff(c_5035, plain, (![A_360, B_361]: (r2_hidden(k4_tarski(A_360, B_361), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_361, '#skF_11') | ~r2_hidden(A_360, '#skF_10'))), inference(resolution, [status(thm)], [c_58, c_4801])).
% 8.36/2.90  tff(c_52, plain, (![A_53, C_55, B_54, D_56]: (r2_hidden(A_53, C_55) | ~r2_hidden(k4_tarski(A_53, B_54), k2_zfmisc_1(C_55, D_56)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.36/2.90  tff(c_5075, plain, (![A_360, B_361]: (r2_hidden(A_360, '#skF_12') | ~r2_hidden(B_361, '#skF_11') | ~r2_hidden(A_360, '#skF_10'))), inference(resolution, [status(thm)], [c_5035, c_52])).
% 8.36/2.90  tff(c_5415, plain, (![B_373]: (~r2_hidden(B_373, '#skF_11'))), inference(splitLeft, [status(thm)], [c_5075])).
% 8.36/2.90  tff(c_5431, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_612, c_5415])).
% 8.36/2.90  tff(c_5478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_889, c_5431])).
% 8.36/2.90  tff(c_5480, plain, (![A_374]: (r2_hidden(A_374, '#skF_12') | ~r2_hidden(A_374, '#skF_10'))), inference(splitRight, [status(thm)], [c_5075])).
% 8.36/2.90  tff(c_6692, plain, (![B_411]: (r2_hidden('#skF_1'('#skF_10', B_411), '#skF_12') | r1_tarski('#skF_10', B_411))), inference(resolution, [status(thm)], [c_6, c_5480])).
% 8.36/2.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.36/2.90  tff(c_6704, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_6692, c_4])).
% 8.36/2.90  tff(c_6711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_76, c_6704])).
% 8.36/2.90  tff(c_6713, plain, (![A_412]: (~r1_xboole_0(A_412, k1_xboole_0))), inference(splitRight, [status(thm)], [c_164])).
% 8.36/2.90  tff(c_6717, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)!=A_17)), inference(resolution, [status(thm)], [c_22, c_6713])).
% 8.36/2.90  tff(c_6721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_6717])).
% 8.36/2.90  tff(c_6722, plain, (~r1_tarski('#skF_11', '#skF_13')), inference(splitRight, [status(thm)], [c_54])).
% 8.36/2.90  tff(c_7238, plain, (![A_486, B_487, D_488]: (r2_hidden('#skF_8'(A_486, B_487, k2_zfmisc_1(A_486, B_487), D_488), A_486) | ~r2_hidden(D_488, k2_zfmisc_1(A_486, B_487)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.36/2.90  tff(c_6753, plain, (![A_425, B_426]: (k4_xboole_0(A_425, k4_xboole_0(A_425, B_426))=k3_xboole_0(A_425, B_426))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.36/2.90  tff(c_6768, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6753])).
% 8.36/2.90  tff(c_6771, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6768])).
% 8.36/2.90  tff(c_6772, plain, (![A_427]: (k4_xboole_0(A_427, A_427)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6768])).
% 8.36/2.90  tff(c_6777, plain, (![A_427]: (k4_xboole_0(A_427, k1_xboole_0)=k3_xboole_0(A_427, A_427))), inference(superposition, [status(thm), theory('equality')], [c_6772, c_18])).
% 8.36/2.90  tff(c_6811, plain, (![A_432]: (k3_xboole_0(A_432, A_432)=A_432)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6777])).
% 8.36/2.90  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.36/2.90  tff(c_6840, plain, (![A_436, C_437]: (~r1_xboole_0(A_436, A_436) | ~r2_hidden(C_437, A_436))), inference(superposition, [status(thm), theory('equality')], [c_6811, c_10])).
% 8.36/2.90  tff(c_6843, plain, (![C_437, B_18]: (~r2_hidden(C_437, B_18) | k4_xboole_0(B_18, B_18)!=B_18)), inference(resolution, [status(thm)], [c_22, c_6840])).
% 8.36/2.90  tff(c_6845, plain, (![C_437, B_18]: (~r2_hidden(C_437, B_18) | k1_xboole_0!=B_18)), inference(demodulation, [status(thm), theory('equality')], [c_6771, c_6843])).
% 8.36/2.90  tff(c_7378, plain, (![A_498, D_499, B_500]: (k1_xboole_0!=A_498 | ~r2_hidden(D_499, k2_zfmisc_1(A_498, B_500)))), inference(resolution, [status(thm)], [c_7238, c_6845])).
% 8.36/2.90  tff(c_7432, plain, (![A_501, B_502]: (k1_xboole_0!=A_501 | k2_zfmisc_1(A_501, B_502)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_7378])).
% 8.36/2.90  tff(c_7480, plain, (k1_xboole_0!='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_7432, c_56])).
% 8.36/2.90  tff(c_7430, plain, (![B_500]: (k2_zfmisc_1(k1_xboole_0, B_500)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_7378])).
% 8.36/2.90  tff(c_7483, plain, (![A_503, B_504, C_505]: (r2_hidden('#skF_5'(A_503, B_504, C_505), A_503) | r2_hidden('#skF_7'(A_503, B_504, C_505), C_505) | k2_zfmisc_1(A_503, B_504)=C_505)), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.36/2.90  tff(c_6731, plain, (![A_419, B_420, C_421]: (~r1_xboole_0(A_419, B_420) | ~r2_hidden(C_421, k3_xboole_0(A_419, B_420)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.36/2.90  tff(c_6738, plain, (![A_13, C_421]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_421, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6731])).
% 8.36/2.90  tff(c_6740, plain, (![C_421]: (~r2_hidden(C_421, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_6738])).
% 8.36/2.90  tff(c_7496, plain, (![B_504, C_505]: (r2_hidden('#skF_7'(k1_xboole_0, B_504, C_505), C_505) | k2_zfmisc_1(k1_xboole_0, B_504)=C_505)), inference(resolution, [status(thm)], [c_7483, c_6740])).
% 8.36/2.90  tff(c_7520, plain, (![B_504, C_505]: (r2_hidden('#skF_7'(k1_xboole_0, B_504, C_505), C_505) | k1_xboole_0=C_505)), inference(demodulation, [status(thm), theory('equality')], [c_7430, c_7496])).
% 8.36/2.90  tff(c_7029, plain, (![A_468, B_469, C_470, D_471]: (r2_hidden(k4_tarski(A_468, B_469), k2_zfmisc_1(C_470, D_471)) | ~r2_hidden(B_469, D_471) | ~r2_hidden(A_468, C_470))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.36/2.90  tff(c_10884, plain, (![C_677, D_675, B_674, B_673, A_676]: (r2_hidden(k4_tarski(A_676, B_673), B_674) | ~r1_tarski(k2_zfmisc_1(C_677, D_675), B_674) | ~r2_hidden(B_673, D_675) | ~r2_hidden(A_676, C_677))), inference(resolution, [status(thm)], [c_7029, c_2])).
% 8.36/2.90  tff(c_11700, plain, (![A_698, B_699]: (r2_hidden(k4_tarski(A_698, B_699), k2_zfmisc_1('#skF_12', '#skF_13')) | ~r2_hidden(B_699, '#skF_11') | ~r2_hidden(A_698, '#skF_10'))), inference(resolution, [status(thm)], [c_58, c_10884])).
% 8.36/2.90  tff(c_50, plain, (![B_54, D_56, A_53, C_55]: (r2_hidden(B_54, D_56) | ~r2_hidden(k4_tarski(A_53, B_54), k2_zfmisc_1(C_55, D_56)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.36/2.90  tff(c_11745, plain, (![B_699, A_698]: (r2_hidden(B_699, '#skF_13') | ~r2_hidden(B_699, '#skF_11') | ~r2_hidden(A_698, '#skF_10'))), inference(resolution, [status(thm)], [c_11700, c_50])).
% 8.36/2.90  tff(c_12110, plain, (![A_710]: (~r2_hidden(A_710, '#skF_10'))), inference(splitLeft, [status(thm)], [c_11745])).
% 8.36/2.90  tff(c_12134, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_7520, c_12110])).
% 8.36/2.90  tff(c_12183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7480, c_12134])).
% 8.36/2.90  tff(c_12185, plain, (![B_711]: (r2_hidden(B_711, '#skF_13') | ~r2_hidden(B_711, '#skF_11'))), inference(splitRight, [status(thm)], [c_11745])).
% 8.36/2.90  tff(c_13286, plain, (![B_748]: (r2_hidden('#skF_1'('#skF_11', B_748), '#skF_13') | r1_tarski('#skF_11', B_748))), inference(resolution, [status(thm)], [c_6, c_12185])).
% 8.36/2.90  tff(c_13298, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_13286, c_4])).
% 8.36/2.90  tff(c_13305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6722, c_6722, c_13298])).
% 8.36/2.90  tff(c_13307, plain, (![A_749]: (~r1_xboole_0(A_749, k1_xboole_0))), inference(splitRight, [status(thm)], [c_6738])).
% 8.36/2.90  tff(c_13311, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)!=A_17)), inference(resolution, [status(thm)], [c_22, c_13307])).
% 8.36/2.90  tff(c_13315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_13311])).
% 8.36/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.90  
% 8.36/2.90  Inference rules
% 8.36/2.90  ----------------------
% 8.36/2.90  #Ref     : 0
% 8.36/2.90  #Sup     : 3148
% 8.36/2.90  #Fact    : 0
% 8.36/2.90  #Define  : 0
% 8.36/2.90  #Split   : 15
% 8.36/2.90  #Chain   : 0
% 8.36/2.90  #Close   : 0
% 8.36/2.90  
% 8.36/2.90  Ordering : KBO
% 8.36/2.90  
% 8.36/2.90  Simplification rules
% 8.36/2.90  ----------------------
% 8.36/2.90  #Subsume      : 1238
% 8.36/2.90  #Demod        : 885
% 8.36/2.90  #Tautology    : 868
% 8.36/2.90  #SimpNegUnit  : 71
% 8.36/2.90  #BackRed      : 4
% 8.36/2.90  
% 8.36/2.90  #Partial instantiations: 0
% 8.36/2.90  #Strategies tried      : 1
% 8.36/2.90  
% 8.36/2.90  Timing (in seconds)
% 8.36/2.90  ----------------------
% 8.36/2.90  Preprocessing        : 0.30
% 8.36/2.90  Parsing              : 0.16
% 8.36/2.90  CNF conversion       : 0.03
% 8.36/2.90  Main loop            : 1.74
% 8.36/2.90  Inferencing          : 0.58
% 8.36/2.90  Reduction            : 0.56
% 8.36/2.90  Demodulation         : 0.38
% 8.36/2.90  BG Simplification    : 0.06
% 8.36/2.90  Subsumption          : 0.43
% 8.36/2.90  Abstraction          : 0.08
% 8.36/2.90  MUC search           : 0.00
% 8.36/2.90  Cooper               : 0.00
% 8.36/2.90  Total                : 2.09
% 8.36/2.90  Index Insertion      : 0.00
% 8.36/2.90  Index Deletion       : 0.00
% 8.36/2.90  Index Matching       : 0.00
% 8.36/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
