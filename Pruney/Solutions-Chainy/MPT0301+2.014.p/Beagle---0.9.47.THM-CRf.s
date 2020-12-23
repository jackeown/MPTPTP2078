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
% DateTime   : Thu Dec  3 09:53:41 EST 2020

% Result     : Theorem 22.52s
% Output     : CNFRefutation 22.78s
% Verified   : 
% Statistics : Number of formulae       :  297 (7273 expanded)
%              Number of leaves         :   33 (2157 expanded)
%              Depth                    :   20
%              Number of atoms          :  438 (16365 expanded)
%              Number of equality atoms :  161 (8529 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_15 > #skF_12 > #skF_4 > #skF_8 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_56,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_10'(A_47,B_48),A_47)
      | r2_hidden('#skF_11'(A_47,B_48),B_48)
      | k3_tarski(A_47) = B_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [A_47,C_62] :
      ( r2_hidden('#skF_12'(A_47,k3_tarski(A_47),C_62),A_47)
      | ~ r2_hidden(C_62,k3_tarski(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94360,plain,(
    ! [A_8740,C_8741] :
      ( r2_hidden('#skF_12'(A_8740,k3_tarski(A_8740),C_8741),A_8740)
      | ~ r2_hidden(C_8741,k3_tarski(A_8740)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38320,plain,(
    ! [A_1735,C_1736] :
      ( r2_hidden('#skF_12'(A_1735,k3_tarski(A_1735),C_1736),A_1735)
      | ~ r2_hidden(C_1736,k3_tarski(A_1735)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4231,plain,(
    ! [A_381,C_382] :
      ( r2_hidden('#skF_12'(A_381,k3_tarski(A_381),C_382),A_381)
      | ~ r2_hidden(C_382,k3_tarski(A_381)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_221,plain,(
    ! [E_106,F_107,A_108,B_109] :
      ( r2_hidden(k4_tarski(E_106,F_107),k2_zfmisc_1(A_108,B_109))
      | ~ r2_hidden(F_107,B_109)
      | ~ r2_hidden(E_106,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_228,plain,(
    ! [E_106,F_107] :
      ( r2_hidden(k4_tarski(E_106,F_107),k1_xboole_0)
      | ~ r2_hidden(F_107,'#skF_16')
      | ~ r2_hidden(E_106,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_221])).

tff(c_231,plain,(
    ! [E_110,F_111] :
      ( r2_hidden(k4_tarski(E_110,F_111),k1_xboole_0)
      | ~ r2_hidden(F_111,'#skF_16')
      | ~ r2_hidden(E_110,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_221])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,B_81)
      | ~ r2_hidden(C_82,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    ! [C_82,A_12] :
      ( ~ r2_hidden(C_82,k1_xboole_0)
      | ~ r2_hidden(C_82,A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_380,plain,(
    ! [E_122,F_123,A_124] :
      ( ~ r2_hidden(k4_tarski(E_122,F_123),A_124)
      | ~ r2_hidden(F_123,'#skF_16')
      | ~ r2_hidden(E_122,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_231,c_104])).

tff(c_391,plain,(
    ! [F_107,E_106] :
      ( ~ r2_hidden(F_107,'#skF_16')
      | ~ r2_hidden(E_106,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_228,c_380])).

tff(c_400,plain,(
    ! [E_127] : ~ r2_hidden(E_127,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_2040,plain,(
    ! [A_232] :
      ( r2_hidden('#skF_10'(A_232,'#skF_15'),A_232)
      | k3_tarski(A_232) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_56,c_400])).

tff(c_399,plain,(
    ! [E_106] : ~ r2_hidden(E_106,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_2074,plain,(
    k3_tarski('#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_2040,c_399])).

tff(c_452,plain,(
    ! [A_129,B_130,D_131] :
      ( r2_hidden('#skF_7'(A_129,B_130,k2_zfmisc_1(A_129,B_130),D_131),A_129)
      | ~ r2_hidden(D_131,k2_zfmisc_1(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_474,plain,(
    ! [D_131] :
      ( r2_hidden('#skF_7'('#skF_15','#skF_16',k1_xboole_0,D_131),'#skF_15')
      | ~ r2_hidden(D_131,k2_zfmisc_1('#skF_15','#skF_16')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_452])).

tff(c_481,plain,(
    ! [D_131] :
      ( r2_hidden('#skF_7'('#skF_15','#skF_16',k1_xboole_0,D_131),'#skF_15')
      | ~ r2_hidden(D_131,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_474])).

tff(c_483,plain,(
    ! [D_132] : ~ r2_hidden(D_132,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_481])).

tff(c_1764,plain,(
    ! [A_225] :
      ( r2_hidden('#skF_10'(A_225,k1_xboole_0),A_225)
      | k3_tarski(A_225) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_483])).

tff(c_1836,plain,(
    k3_tarski('#skF_15') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1764,c_399])).

tff(c_2077,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_1836])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_2077])).

tff(c_2081,plain,(
    ! [F_233] : ~ r2_hidden(F_233,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_4105,plain,(
    ! [A_357] :
      ( r2_hidden('#skF_10'(A_357,'#skF_16'),A_357)
      | k3_tarski(A_357) = '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_56,c_2081])).

tff(c_2080,plain,(
    ! [F_107] : ~ r2_hidden(F_107,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_2365,plain,(
    ! [A_252,B_253,D_254] :
      ( r2_hidden('#skF_8'(A_252,B_253,k2_zfmisc_1(A_252,B_253),D_254),B_253)
      | ~ r2_hidden(D_254,k2_zfmisc_1(A_252,B_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2399,plain,(
    ! [D_254] :
      ( r2_hidden('#skF_8'('#skF_15','#skF_16',k1_xboole_0,D_254),'#skF_16')
      | ~ r2_hidden(D_254,k2_zfmisc_1('#skF_15','#skF_16')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2365])).

tff(c_2409,plain,(
    ! [D_254] :
      ( r2_hidden('#skF_8'('#skF_15','#skF_16',k1_xboole_0,D_254),'#skF_16')
      | ~ r2_hidden(D_254,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2399])).

tff(c_2410,plain,(
    ! [D_254] : ~ r2_hidden(D_254,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2080,c_2409])).

tff(c_4142,plain,(
    k3_tarski(k1_xboole_0) = '#skF_16' ),
    inference(resolution,[status(thm)],[c_4105,c_2410])).

tff(c_2411,plain,(
    ! [D_255] : ~ r2_hidden(D_255,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2080,c_2409])).

tff(c_3731,plain,(
    ! [A_350] :
      ( r2_hidden('#skF_10'(A_350,k1_xboole_0),A_350)
      | k3_tarski(A_350) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_2411])).

tff(c_3819,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3731,c_2410])).

tff(c_4147,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4142,c_3819])).

tff(c_4149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4147])).

tff(c_4150,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4152,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_4150])).

tff(c_4156,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4152,c_16])).

tff(c_4175,plain,(
    ! [A_367,B_368,C_369] :
      ( ~ r1_xboole_0(A_367,B_368)
      | ~ r2_hidden(C_369,B_368)
      | ~ r2_hidden(C_369,A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4178,plain,(
    ! [C_369,A_12] :
      ( ~ r2_hidden(C_369,'#skF_14')
      | ~ r2_hidden(C_369,A_12) ) ),
    inference(resolution,[status(thm)],[c_4156,c_4175])).

tff(c_4341,plain,(
    ! [C_403,A_404] :
      ( ~ r2_hidden('#skF_12'('#skF_14',k3_tarski('#skF_14'),C_403),A_404)
      | ~ r2_hidden(C_403,k3_tarski('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_4231,c_4178])).

tff(c_4351,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_44,c_4341])).

tff(c_4352,plain,(
    ! [C_405] : ~ r2_hidden(C_405,k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_44,c_4341])).

tff(c_18336,plain,(
    ! [B_1003] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_1003),B_1003)
      | k3_tarski(k3_tarski('#skF_14')) = B_1003 ) ),
    inference(resolution,[status(thm)],[c_56,c_4352])).

tff(c_18624,plain,(
    k3_tarski(k3_tarski('#skF_14')) = k3_tarski('#skF_14') ),
    inference(resolution,[status(thm)],[c_18336,c_4351])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4155,plain,(
    ! [A_11] : r1_tarski('#skF_14',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4152,c_14])).

tff(c_4287,plain,(
    ! [A_394,B_395] :
      ( r2_hidden('#skF_10'(A_394,B_395),A_394)
      | r2_hidden('#skF_11'(A_394,B_395),B_395)
      | k3_tarski(A_394) = B_395 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4303,plain,(
    ! [A_394,B_395,B_2] :
      ( r2_hidden('#skF_11'(A_394,B_395),B_2)
      | ~ r1_tarski(B_395,B_2)
      | r2_hidden('#skF_10'(A_394,B_395),A_394)
      | k3_tarski(A_394) = B_395 ) ),
    inference(resolution,[status(thm)],[c_4287,c_2])).

tff(c_4394,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_48),B_48)
      | k3_tarski(k3_tarski('#skF_14')) = B_48 ) ),
    inference(resolution,[status(thm)],[c_56,c_4352])).

tff(c_19665,plain,(
    ! [B_1011] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_1011),B_1011)
      | k3_tarski('#skF_14') = B_1011 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18624,c_4394])).

tff(c_19753,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_11'(k3_tarski('#skF_14'),'#skF_14'),A_12)
      | k3_tarski('#skF_14') = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_19665,c_4178])).

tff(c_19956,plain,(
    ! [A_1017] : ~ r2_hidden('#skF_11'(k3_tarski('#skF_14'),'#skF_14'),A_1017) ),
    inference(splitLeft,[status(thm)],[c_19753])).

tff(c_19974,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_14',B_2)
      | r2_hidden('#skF_10'(k3_tarski('#skF_14'),'#skF_14'),k3_tarski('#skF_14'))
      | k3_tarski(k3_tarski('#skF_14')) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_4303,c_19956])).

tff(c_19999,plain,
    ( r2_hidden('#skF_10'(k3_tarski('#skF_14'),'#skF_14'),k3_tarski('#skF_14'))
    | k3_tarski('#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18624,c_4155,c_19974])).

tff(c_20000,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_4351,c_19999])).

tff(c_4483,plain,(
    ! [A_416,B_417,D_418] :
      ( r2_hidden('#skF_8'(A_416,B_417,k2_zfmisc_1(A_416,B_417),D_418),B_417)
      | ~ r2_hidden(D_418,k2_zfmisc_1(A_416,B_417)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4500,plain,(
    ! [D_418,A_416] : ~ r2_hidden(D_418,k2_zfmisc_1(A_416,k3_tarski('#skF_14'))) ),
    inference(resolution,[status(thm)],[c_4483,c_4351])).

tff(c_18621,plain,(
    ! [A_416] : k2_zfmisc_1(A_416,k3_tarski('#skF_14')) = k3_tarski(k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_18336,c_4500])).

tff(c_19248,plain,(
    ! [A_416] : k2_zfmisc_1(A_416,k3_tarski('#skF_14')) = k3_tarski('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18624,c_18621])).

tff(c_20223,plain,(
    ! [A_416] : k2_zfmisc_1(A_416,'#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20000,c_20000,c_19248])).

tff(c_4151,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4163,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4152,c_4151])).

tff(c_68,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4165,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14'
    | k2_zfmisc_1('#skF_15','#skF_16') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4152,c_4152,c_68])).

tff(c_4166,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_4163,c_4165])).

tff(c_20437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20223,c_4166])).

tff(c_20438,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_19753])).

tff(c_20443,plain,(
    ! [A_416] : k2_zfmisc_1(A_416,'#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20438,c_20438,c_19248])).

tff(c_20851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20443,c_4166])).

tff(c_20852,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_4150])).

tff(c_38219,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20852,c_4151])).

tff(c_20940,plain,(
    ! [A_1053,C_1054] :
      ( r2_hidden('#skF_12'(A_1053,k3_tarski(A_1053),C_1054),A_1053)
      | ~ r2_hidden(C_1054,k3_tarski(A_1053)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20858,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20852,c_16])).

tff(c_20877,plain,(
    ! [A_1037,B_1038,C_1039] :
      ( ~ r1_xboole_0(A_1037,B_1038)
      | ~ r2_hidden(C_1039,B_1038)
      | ~ r2_hidden(C_1039,A_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20880,plain,(
    ! [C_1039,A_12] :
      ( ~ r2_hidden(C_1039,'#skF_13')
      | ~ r2_hidden(C_1039,A_12) ) ),
    inference(resolution,[status(thm)],[c_20858,c_20877])).

tff(c_21113,plain,(
    ! [C_1085,A_1086] :
      ( ~ r2_hidden('#skF_12'('#skF_13',k3_tarski('#skF_13'),C_1085),A_1086)
      | ~ r2_hidden(C_1085,k3_tarski('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_20940,c_20880])).

tff(c_21122,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_44,c_21113])).

tff(c_21124,plain,(
    ! [C_1087] : ~ r2_hidden(C_1087,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_44,c_21113])).

tff(c_36049,plain,(
    ! [B_1684] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_1684),B_1684)
      | k3_tarski(k3_tarski('#skF_13')) = B_1684 ) ),
    inference(resolution,[status(thm)],[c_56,c_21124])).

tff(c_36339,plain,(
    k3_tarski(k3_tarski('#skF_13')) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_36049,c_21122])).

tff(c_20857,plain,(
    ! [A_11] : r1_tarski('#skF_13',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20852,c_14])).

tff(c_21047,plain,(
    ! [A_1074,B_1075] :
      ( r2_hidden('#skF_10'(A_1074,B_1075),A_1074)
      | r2_hidden('#skF_11'(A_1074,B_1075),B_1075)
      | k3_tarski(A_1074) = B_1075 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_21063,plain,(
    ! [A_1074,B_1075,B_2] :
      ( r2_hidden('#skF_11'(A_1074,B_1075),B_2)
      | ~ r1_tarski(B_1075,B_2)
      | r2_hidden('#skF_10'(A_1074,B_1075),A_1074)
      | k3_tarski(A_1074) = B_1075 ) ),
    inference(resolution,[status(thm)],[c_21047,c_2])).

tff(c_21165,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_48),B_48)
      | k3_tarski(k3_tarski('#skF_13')) = B_48 ) ),
    inference(resolution,[status(thm)],[c_56,c_21124])).

tff(c_37238,plain,(
    ! [B_1692] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_1692),B_1692)
      | k3_tarski('#skF_13') = B_1692 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36339,c_21165])).

tff(c_37329,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_11'(k3_tarski('#skF_13'),'#skF_13'),A_12)
      | k3_tarski('#skF_13') = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_37238,c_20880])).

tff(c_37564,plain,(
    ! [A_1699] : ~ r2_hidden('#skF_11'(k3_tarski('#skF_13'),'#skF_13'),A_1699) ),
    inference(splitLeft,[status(thm)],[c_37329])).

tff(c_37586,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_13',B_2)
      | r2_hidden('#skF_10'(k3_tarski('#skF_13'),'#skF_13'),k3_tarski('#skF_13'))
      | k3_tarski(k3_tarski('#skF_13')) = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_21063,c_37564])).

tff(c_37610,plain,
    ( r2_hidden('#skF_10'(k3_tarski('#skF_13'),'#skF_13'),k3_tarski('#skF_13'))
    | k3_tarski('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36339,c_20857,c_37586])).

tff(c_37611,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_21122,c_37610])).

tff(c_21272,plain,(
    ! [A_1097,B_1098,D_1099] :
      ( r2_hidden('#skF_7'(A_1097,B_1098,k2_zfmisc_1(A_1097,B_1098),D_1099),A_1097)
      | ~ r2_hidden(D_1099,k2_zfmisc_1(A_1097,B_1098)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_21291,plain,(
    ! [D_1099,B_1098] : ~ r2_hidden(D_1099,k2_zfmisc_1(k3_tarski('#skF_13'),B_1098)) ),
    inference(resolution,[status(thm)],[c_21272,c_21122])).

tff(c_36335,plain,(
    ! [B_1098] : k2_zfmisc_1(k3_tarski('#skF_13'),B_1098) = k3_tarski(k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_36049,c_21291])).

tff(c_36590,plain,(
    ! [B_1098] : k2_zfmisc_1(k3_tarski('#skF_13'),B_1098) = k3_tarski('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36339,c_36335])).

tff(c_37623,plain,(
    ! [B_1098] : k2_zfmisc_1('#skF_13',B_1098) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37611,c_37611,c_36590])).

tff(c_20854,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_20866,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20852,c_20854])).

tff(c_37836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37623,c_20866])).

tff(c_37837,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_37329])).

tff(c_37843,plain,(
    ! [B_1098] : k2_zfmisc_1('#skF_13',B_1098) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37837,c_37837,c_36590])).

tff(c_38200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37843,c_20866])).

tff(c_38201,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_38220,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20852,c_38201])).

tff(c_38221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38219,c_38220])).

tff(c_38223,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_38222,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_38234,plain,
    ( '#skF_16' = '#skF_13'
    | '#skF_16' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38223,c_38223,c_38222])).

tff(c_38235,plain,(
    '#skF_16' = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_38234])).

tff(c_38226,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38223,c_16])).

tff(c_38236,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38235,c_38226])).

tff(c_38274,plain,(
    ! [A_1724,B_1725,C_1726] :
      ( ~ r1_xboole_0(A_1724,B_1725)
      | ~ r2_hidden(C_1726,B_1725)
      | ~ r2_hidden(C_1726,A_1724) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38277,plain,(
    ! [C_1726,A_12] :
      ( ~ r2_hidden(C_1726,'#skF_14')
      | ~ r2_hidden(C_1726,A_12) ) ),
    inference(resolution,[status(thm)],[c_38236,c_38274])).

tff(c_38394,plain,(
    ! [C_1754,A_1755] :
      ( ~ r2_hidden('#skF_12'('#skF_14',k3_tarski('#skF_14'),C_1754),A_1755)
      | ~ r2_hidden(C_1754,k3_tarski('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_38320,c_38277])).

tff(c_38404,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_44,c_38394])).

tff(c_38455,plain,(
    ! [A_1760,B_1761] :
      ( r2_hidden('#skF_10'(A_1760,B_1761),A_1760)
      | r2_hidden('#skF_11'(A_1760,B_1761),B_1761)
      | k3_tarski(A_1760) = B_1761 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52508,plain,(
    ! [B_2355] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_2355),B_2355)
      | k3_tarski(k3_tarski('#skF_14')) = B_2355 ) ),
    inference(resolution,[status(thm)],[c_38455,c_38404])).

tff(c_52796,plain,(
    k3_tarski(k3_tarski('#skF_14')) = k3_tarski('#skF_14') ),
    inference(resolution,[status(thm)],[c_52508,c_38404])).

tff(c_38225,plain,(
    ! [A_11] : r1_tarski('#skF_16',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38223,c_14])).

tff(c_38237,plain,(
    ! [A_11] : r1_tarski('#skF_14',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38235,c_38225])).

tff(c_38482,plain,(
    ! [A_1760,B_1761,B_2] :
      ( r2_hidden('#skF_11'(A_1760,B_1761),B_2)
      | ~ r1_tarski(B_1761,B_2)
      | r2_hidden('#skF_10'(A_1760,B_1761),A_1760)
      | k3_tarski(A_1760) = B_1761 ) ),
    inference(resolution,[status(thm)],[c_38455,c_2])).

tff(c_38476,plain,(
    ! [B_1761] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_1761),B_1761)
      | k3_tarski(k3_tarski('#skF_14')) = B_1761 ) ),
    inference(resolution,[status(thm)],[c_38455,c_38404])).

tff(c_53836,plain,(
    ! [B_2363] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_2363),B_2363)
      | k3_tarski('#skF_14') = B_2363 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52796,c_38476])).

tff(c_53923,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_11'(k3_tarski('#skF_14'),'#skF_14'),A_12)
      | k3_tarski('#skF_14') = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_53836,c_38277])).

tff(c_54159,plain,(
    ! [A_2370] : ~ r2_hidden('#skF_11'(k3_tarski('#skF_14'),'#skF_14'),A_2370) ),
    inference(splitLeft,[status(thm)],[c_53923])).

tff(c_54181,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_14',B_2)
      | r2_hidden('#skF_10'(k3_tarski('#skF_14'),'#skF_14'),k3_tarski('#skF_14'))
      | k3_tarski(k3_tarski('#skF_14')) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_38482,c_54159])).

tff(c_54205,plain,
    ( r2_hidden('#skF_10'(k3_tarski('#skF_14'),'#skF_14'),k3_tarski('#skF_14'))
    | k3_tarski('#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52796,c_38237,c_54181])).

tff(c_54206,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_38404,c_54205])).

tff(c_38686,plain,(
    ! [A_1776,B_1777,D_1778] :
      ( r2_hidden('#skF_8'(A_1776,B_1777,k2_zfmisc_1(A_1776,B_1777),D_1778),B_1777)
      | ~ r2_hidden(D_1778,k2_zfmisc_1(A_1776,B_1777)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38713,plain,(
    ! [D_1778,A_1776] : ~ r2_hidden(D_1778,k2_zfmisc_1(A_1776,k3_tarski('#skF_14'))) ),
    inference(resolution,[status(thm)],[c_38686,c_38404])).

tff(c_52791,plain,(
    ! [A_1776] : k2_zfmisc_1(A_1776,k3_tarski('#skF_14')) = k3_tarski(k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_52508,c_38713])).

tff(c_53046,plain,(
    ! [A_1776] : k2_zfmisc_1(A_1776,k3_tarski('#skF_14')) = k3_tarski('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52796,c_52791])).

tff(c_54427,plain,(
    ! [A_1776] : k2_zfmisc_1(A_1776,'#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54206,c_54206,c_53046])).

tff(c_38239,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38235,c_38223])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38251,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38239,c_38235,c_38239,c_60])).

tff(c_54690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54427,c_38251])).

tff(c_54691,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_53923])).

tff(c_54850,plain,(
    ! [A_1776] : k2_zfmisc_1(A_1776,'#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54691,c_54691,c_53046])).

tff(c_55302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54850,c_38251])).

tff(c_55303,plain,(
    '#skF_16' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_38234])).

tff(c_55304,plain,(
    '#skF_16' != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_38234])).

tff(c_55313,plain,(
    '#skF_14' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55303,c_55304])).

tff(c_55306,plain,(
    ! [A_11] : r1_tarski('#skF_13',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55303,c_38225])).

tff(c_55391,plain,(
    ! [A_2409,C_2410] :
      ( r2_hidden('#skF_12'(A_2409,k3_tarski(A_2409),C_2410),A_2409)
      | ~ r2_hidden(C_2410,k3_tarski(A_2409)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55305,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55303,c_38226])).

tff(c_55335,plain,(
    ! [A_2395,B_2396,C_2397] :
      ( ~ r1_xboole_0(A_2395,B_2396)
      | ~ r2_hidden(C_2397,B_2396)
      | ~ r2_hidden(C_2397,A_2395) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55338,plain,(
    ! [C_2397,A_12] :
      ( ~ r2_hidden(C_2397,'#skF_13')
      | ~ r2_hidden(C_2397,A_12) ) ),
    inference(resolution,[status(thm)],[c_55305,c_55335])).

tff(c_55625,plain,(
    ! [C_2449,A_2450] :
      ( ~ r2_hidden('#skF_12'('#skF_13',k3_tarski('#skF_13'),C_2449),A_2450)
      | ~ r2_hidden(C_2449,k3_tarski('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_55391,c_55338])).

tff(c_55636,plain,(
    ! [C_2451] : ~ r2_hidden(C_2451,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_44,c_55625])).

tff(c_71099,plain,(
    ! [A_3061] :
      ( r2_hidden('#skF_10'(A_3061,k3_tarski('#skF_13')),A_3061)
      | k3_tarski(A_3061) = k3_tarski('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_56,c_55636])).

tff(c_55635,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_44,c_55625])).

tff(c_71395,plain,(
    k3_tarski(k3_tarski('#skF_13')) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_71099,c_55635])).

tff(c_55682,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_48),B_48)
      | k3_tarski(k3_tarski('#skF_13')) = B_48 ) ),
    inference(resolution,[status(thm)],[c_56,c_55636])).

tff(c_72169,plain,(
    ! [B_3068] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_3068),B_3068)
      | k3_tarski('#skF_13') = B_3068 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71395,c_55682])).

tff(c_55608,plain,(
    ! [A_2446,B_2447,D_2448] :
      ( r2_hidden('#skF_7'(A_2446,B_2447,k2_zfmisc_1(A_2446,B_2447),D_2448),A_2446)
      | ~ r2_hidden(D_2448,k2_zfmisc_1(A_2446,B_2447)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65691,plain,(
    ! [A_2941,B_2942,D_2943,B_2944] :
      ( r2_hidden('#skF_7'(A_2941,B_2942,k2_zfmisc_1(A_2941,B_2942),D_2943),B_2944)
      | ~ r1_tarski(A_2941,B_2944)
      | ~ r2_hidden(D_2943,k2_zfmisc_1(A_2941,B_2942)) ) ),
    inference(resolution,[status(thm)],[c_55608,c_2])).

tff(c_65956,plain,(
    ! [A_2941,D_2943,B_2942] :
      ( ~ r1_tarski(A_2941,k3_tarski('#skF_13'))
      | ~ r2_hidden(D_2943,k2_zfmisc_1(A_2941,B_2942)) ) ),
    inference(resolution,[status(thm)],[c_65691,c_55635])).

tff(c_73158,plain,(
    ! [A_3080,B_3081] :
      ( ~ r1_tarski(A_3080,k3_tarski('#skF_13'))
      | k2_zfmisc_1(A_3080,B_3081) = k3_tarski('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_72169,c_65956])).

tff(c_73188,plain,(
    ! [B_3081] : k2_zfmisc_1('#skF_13',B_3081) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_55306,c_73158])).

tff(c_55308,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55303,c_38223])).

tff(c_55321,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55308,c_55303,c_55308,c_60])).

tff(c_73189,plain,(
    k3_tarski('#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73188,c_55321])).

tff(c_72168,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_48),B_48)
      | k3_tarski('#skF_13') = B_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71395,c_55682])).

tff(c_73190,plain,(
    ! [B_3082] : k2_zfmisc_1('#skF_13',B_3082) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_55306,c_73158])).

tff(c_18,plain,(
    ! [E_45,F_46,A_13,B_14] :
      ( r2_hidden(k4_tarski(E_45,F_46),k2_zfmisc_1(A_13,B_14))
      | ~ r2_hidden(F_46,B_14)
      | ~ r2_hidden(E_45,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73248,plain,(
    ! [E_45,F_46,B_3082] :
      ( r2_hidden(k4_tarski(E_45,F_46),k3_tarski('#skF_13'))
      | ~ r2_hidden(F_46,B_3082)
      | ~ r2_hidden(E_45,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73190,c_18])).

tff(c_73279,plain,(
    ! [F_46,B_3082,E_45] :
      ( ~ r2_hidden(F_46,B_3082)
      | ~ r2_hidden(E_45,'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55635,c_73248])).

tff(c_73308,plain,(
    ! [E_3086] : ~ r2_hidden(E_3086,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_73279])).

tff(c_73312,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_72168,c_73308])).

tff(c_73442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73189,c_73312])).

tff(c_73443,plain,(
    ! [F_46,B_3082] : ~ r2_hidden(F_46,B_3082) ),
    inference(splitRight,[status(thm)],[c_73279])).

tff(c_58,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_9'(A_47,B_48),'#skF_10'(A_47,B_48))
      | r2_hidden('#skF_11'(A_47,B_48),B_48)
      | k3_tarski(A_47) = B_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_73532,plain,(
    ! [A_3089] : k3_tarski(A_3089) = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_73443,c_73443,c_58])).

tff(c_73488,plain,(
    ! [A_47,B_48] : k3_tarski(A_47) = B_48 ),
    inference(negUnitSimplification,[status(thm)],[c_73443,c_73443,c_58])).

tff(c_74820,plain,(
    ! [B_4360] : B_4360 = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_73532,c_73488])).

tff(c_74871,plain,(
    '#skF_14' = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_74820,c_55308])).

tff(c_74881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55313,c_74871])).

tff(c_74883,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74897,plain,
    ( '#skF_15' = '#skF_14'
    | '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74883,c_74883,c_74883,c_66])).

tff(c_74898,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_74897])).

tff(c_74884,plain,(
    ! [A_11] : r1_tarski('#skF_15',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74883,c_14])).

tff(c_74903,plain,(
    ! [A_11] : r1_tarski('#skF_13',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74898,c_74884])).

tff(c_74982,plain,(
    ! [A_5680,C_5681] :
      ( r2_hidden('#skF_12'(A_5680,k3_tarski(A_5680),C_5681),A_5680)
      | ~ r2_hidden(C_5681,k3_tarski(A_5680)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74885,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74883,c_16])).

tff(c_74902,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74898,c_74885])).

tff(c_74926,plain,(
    ! [A_5666,B_5667,C_5668] :
      ( ~ r1_xboole_0(A_5666,B_5667)
      | ~ r2_hidden(C_5668,B_5667)
      | ~ r2_hidden(C_5668,A_5666) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74929,plain,(
    ! [C_5668,A_12] :
      ( ~ r2_hidden(C_5668,'#skF_13')
      | ~ r2_hidden(C_5668,A_12) ) ),
    inference(resolution,[status(thm)],[c_74902,c_74926])).

tff(c_75217,plain,(
    ! [C_5720,A_5721] :
      ( ~ r2_hidden('#skF_12'('#skF_13',k3_tarski('#skF_13'),C_5720),A_5721)
      | ~ r2_hidden(C_5720,k3_tarski('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_74982,c_74929])).

tff(c_75228,plain,(
    ! [C_5722] : ~ r2_hidden(C_5722,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_44,c_75217])).

tff(c_90176,plain,(
    ! [A_6324] :
      ( r2_hidden('#skF_10'(A_6324,k3_tarski('#skF_13')),A_6324)
      | k3_tarski(A_6324) = k3_tarski('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_56,c_75228])).

tff(c_75227,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_44,c_75217])).

tff(c_90464,plain,(
    k3_tarski(k3_tarski('#skF_13')) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_90176,c_75227])).

tff(c_75275,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_48),B_48)
      | k3_tarski(k3_tarski('#skF_13')) = B_48 ) ),
    inference(resolution,[status(thm)],[c_56,c_75228])).

tff(c_91238,plain,(
    ! [B_6331] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_6331),B_6331)
      | k3_tarski('#skF_13') = B_6331 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90464,c_75275])).

tff(c_75293,plain,(
    ! [A_5726,B_5727,D_5728] :
      ( r2_hidden('#skF_7'(A_5726,B_5727,k2_zfmisc_1(A_5726,B_5727),D_5728),A_5726)
      | ~ r2_hidden(D_5728,k2_zfmisc_1(A_5726,B_5727)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85337,plain,(
    ! [A_6226,B_6227,D_6228,B_6229] :
      ( r2_hidden('#skF_7'(A_6226,B_6227,k2_zfmisc_1(A_6226,B_6227),D_6228),B_6229)
      | ~ r1_tarski(A_6226,B_6229)
      | ~ r2_hidden(D_6228,k2_zfmisc_1(A_6226,B_6227)) ) ),
    inference(resolution,[status(thm)],[c_75293,c_2])).

tff(c_85601,plain,(
    ! [A_6226,D_6228,B_6227] :
      ( ~ r1_tarski(A_6226,k3_tarski('#skF_13'))
      | ~ r2_hidden(D_6228,k2_zfmisc_1(A_6226,B_6227)) ) ),
    inference(resolution,[status(thm)],[c_85337,c_75227])).

tff(c_92366,plain,(
    ! [A_6347,B_6348] :
      ( ~ r1_tarski(A_6347,k3_tarski('#skF_13'))
      | k2_zfmisc_1(A_6347,B_6348) = k3_tarski('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_91238,c_85601])).

tff(c_92396,plain,(
    ! [B_6348] : k2_zfmisc_1('#skF_13',B_6348) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_74903,c_92366])).

tff(c_74882,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_74892,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74883,c_74882])).

tff(c_74901,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74898,c_74892])).

tff(c_92397,plain,(
    k3_tarski('#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92396,c_74901])).

tff(c_91237,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_13'),B_48),B_48)
      | k3_tarski('#skF_13') = B_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90464,c_75275])).

tff(c_92398,plain,(
    ! [B_6349] : k2_zfmisc_1('#skF_13',B_6349) = k3_tarski('#skF_13') ),
    inference(resolution,[status(thm)],[c_74903,c_92366])).

tff(c_92459,plain,(
    ! [E_45,F_46,B_6349] :
      ( r2_hidden(k4_tarski(E_45,F_46),k3_tarski('#skF_13'))
      | ~ r2_hidden(F_46,B_6349)
      | ~ r2_hidden(E_45,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92398,c_18])).

tff(c_92491,plain,(
    ! [F_46,B_6349,E_45] :
      ( ~ r2_hidden(F_46,B_6349)
      | ~ r2_hidden(E_45,'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_75227,c_92459])).

tff(c_92707,plain,(
    ! [E_6353] : ~ r2_hidden(E_6353,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_92491])).

tff(c_92711,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_91237,c_92707])).

tff(c_92841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92397,c_92711])).

tff(c_92842,plain,(
    ! [F_46,B_6349] : ~ r2_hidden(F_46,B_6349) ),
    inference(splitRight,[status(thm)],[c_92491])).

tff(c_92925,plain,(
    ! [A_6356] : k3_tarski(A_6356) = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_92842,c_92842,c_58])).

tff(c_92885,plain,(
    ! [A_47,B_48] : k3_tarski(A_47) = B_48 ),
    inference(negUnitSimplification,[status(thm)],[c_92842,c_92842,c_58])).

tff(c_94217,plain,(
    ! [B_7536] : B_7536 = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_92925,c_92885])).

tff(c_94271,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_94217,c_92397])).

tff(c_94272,plain,(
    '#skF_15' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_74897])).

tff(c_94276,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94272,c_74885])).

tff(c_94314,plain,(
    ! [A_8729,B_8730,C_8731] :
      ( ~ r1_xboole_0(A_8729,B_8730)
      | ~ r2_hidden(C_8731,B_8730)
      | ~ r2_hidden(C_8731,A_8729) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94317,plain,(
    ! [C_8731,A_12] :
      ( ~ r2_hidden(C_8731,'#skF_14')
      | ~ r2_hidden(C_8731,A_12) ) ),
    inference(resolution,[status(thm)],[c_94276,c_94314])).

tff(c_94680,plain,(
    ! [C_8791,A_8792] :
      ( ~ r2_hidden('#skF_12'('#skF_14',k3_tarski('#skF_14'),C_8791),A_8792)
      | ~ r2_hidden(C_8791,k3_tarski('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_94360,c_94317])).

tff(c_94691,plain,(
    ! [C_8793] : ~ r2_hidden(C_8793,k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_44,c_94680])).

tff(c_110135,plain,(
    ! [A_9400] :
      ( r2_hidden('#skF_10'(A_9400,k3_tarski('#skF_14')),A_9400)
      | k3_tarski(A_9400) = k3_tarski('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_56,c_94691])).

tff(c_94690,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k3_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_44,c_94680])).

tff(c_110431,plain,(
    k3_tarski(k3_tarski('#skF_14')) = k3_tarski('#skF_14') ),
    inference(resolution,[status(thm)],[c_110135,c_94690])).

tff(c_94746,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_48),B_48)
      | k3_tarski(k3_tarski('#skF_14')) = B_48 ) ),
    inference(resolution,[status(thm)],[c_56,c_94691])).

tff(c_111204,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_48),B_48)
      | k3_tarski('#skF_14') = B_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110431,c_94746])).

tff(c_94277,plain,(
    ! [A_11] : r1_tarski('#skF_14',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94272,c_74884])).

tff(c_111205,plain,(
    ! [B_9407] :
      ( r2_hidden('#skF_11'(k3_tarski('#skF_14'),B_9407),B_9407)
      | k3_tarski('#skF_14') = B_9407 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110431,c_94746])).

tff(c_94577,plain,(
    ! [A_8777,B_8778,D_8779] :
      ( r2_hidden('#skF_7'(A_8777,B_8778,k2_zfmisc_1(A_8777,B_8778),D_8779),A_8777)
      | ~ r2_hidden(D_8779,k2_zfmisc_1(A_8777,B_8778)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104897,plain,(
    ! [A_9296,B_9297,D_9298,B_9299] :
      ( r2_hidden('#skF_7'(A_9296,B_9297,k2_zfmisc_1(A_9296,B_9297),D_9298),B_9299)
      | ~ r1_tarski(A_9296,B_9299)
      | ~ r2_hidden(D_9298,k2_zfmisc_1(A_9296,B_9297)) ) ),
    inference(resolution,[status(thm)],[c_94577,c_2])).

tff(c_105161,plain,(
    ! [A_9296,D_9298,B_9297] :
      ( ~ r1_tarski(A_9296,k3_tarski('#skF_14'))
      | ~ r2_hidden(D_9298,k2_zfmisc_1(A_9296,B_9297)) ) ),
    inference(resolution,[status(thm)],[c_104897,c_94690])).

tff(c_112194,plain,(
    ! [A_9419,B_9420] :
      ( ~ r1_tarski(A_9419,k3_tarski('#skF_14'))
      | k2_zfmisc_1(A_9419,B_9420) = k3_tarski('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_111205,c_105161])).

tff(c_112225,plain,(
    ! [B_9421] : k2_zfmisc_1('#skF_14',B_9421) = k3_tarski('#skF_14') ),
    inference(resolution,[status(thm)],[c_94277,c_112194])).

tff(c_112286,plain,(
    ! [E_45,F_46,B_9421] :
      ( r2_hidden(k4_tarski(E_45,F_46),k3_tarski('#skF_14'))
      | ~ r2_hidden(F_46,B_9421)
      | ~ r2_hidden(E_45,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112225,c_18])).

tff(c_112317,plain,(
    ! [F_46,B_9421,E_45] :
      ( ~ r2_hidden(F_46,B_9421)
      | ~ r2_hidden(E_45,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94690,c_112286])).

tff(c_112346,plain,(
    ! [E_9425] : ~ r2_hidden(E_9425,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_112317])).

tff(c_112477,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_111204,c_112346])).

tff(c_22,plain,(
    ! [A_13,B_14,D_40] :
      ( r2_hidden('#skF_8'(A_13,B_14,k2_zfmisc_1(A_13,B_14),D_40),B_14)
      | ~ r2_hidden(D_40,k2_zfmisc_1(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94740,plain,(
    ! [D_40,A_13] : ~ r2_hidden(D_40,k2_zfmisc_1(A_13,k3_tarski('#skF_14'))) ),
    inference(resolution,[status(thm)],[c_22,c_94691])).

tff(c_111358,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k3_tarski('#skF_14')) = k3_tarski('#skF_14') ),
    inference(resolution,[status(thm)],[c_111205,c_94740])).

tff(c_112514,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112477,c_112477,c_111358])).

tff(c_94275,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94272,c_74892])).

tff(c_112822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112514,c_94275])).

tff(c_112823,plain,(
    ! [F_46,B_9421] : ~ r2_hidden(F_46,B_9421) ),
    inference(splitRight,[status(thm)],[c_112317])).

tff(c_114109,plain,(
    ! [A_47] : k3_tarski(A_47) = '#skF_14' ),
    inference(negUnitSimplification,[status(thm)],[c_112823,c_112823,c_58])).

tff(c_112884,plain,(
    ! [A_9431,B_9432] : k3_tarski(A_9431) = B_9432 ),
    inference(negUnitSimplification,[status(thm)],[c_112823,c_112823,c_58])).

tff(c_114402,plain,(
    ! [B_14870] : B_14870 = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_114109,c_112884])).

tff(c_112891,plain,(
    ! [A_9431] : k3_tarski(A_9431) = '#skF_15' ),
    inference(negUnitSimplification,[status(thm)],[c_112823,c_112823,c_58])).

tff(c_112867,plain,(
    ! [A_47,B_48] : k3_tarski(A_47) = B_48 ),
    inference(negUnitSimplification,[status(thm)],[c_112823,c_112823,c_58])).

tff(c_114268,plain,(
    ! [B_11980] : B_11980 = '#skF_15' ),
    inference(superposition,[status(thm),theory(equality)],[c_112891,c_112867])).

tff(c_114325,plain,(
    '#skF_15' != '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_114268,c_94275])).

tff(c_114490,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_114402,c_114325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.52/12.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.78/13.01  
% 22.78/13.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.78/13.01  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_15 > #skF_12 > #skF_4 > #skF_8 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_9
% 22.78/13.01  
% 22.78/13.01  %Foreground sorts:
% 22.78/13.01  
% 22.78/13.01  
% 22.78/13.01  %Background operators:
% 22.78/13.01  
% 22.78/13.01  
% 22.78/13.01  %Foreground operators:
% 22.78/13.01  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 22.78/13.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.78/13.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.78/13.01  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 22.78/13.01  tff('#skF_15', type, '#skF_15': $i).
% 22.78/13.01  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.78/13.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.78/13.01  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 22.78/13.01  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 22.78/13.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.78/13.01  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 22.78/13.01  tff('#skF_16', type, '#skF_16': $i).
% 22.78/13.01  tff('#skF_14', type, '#skF_14': $i).
% 22.78/13.01  tff('#skF_13', type, '#skF_13': $i).
% 22.78/13.01  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 22.78/13.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.78/13.01  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 22.78/13.01  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 22.78/13.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.78/13.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.78/13.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.78/13.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 22.78/13.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.78/13.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.78/13.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.78/13.01  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 22.78/13.01  
% 22.78/13.05  tff(f_76, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 22.78/13.05  tff(f_83, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 22.78/13.05  tff(f_66, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 22.78/13.05  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 22.78/13.05  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 22.78/13.05  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 22.78/13.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 22.78/13.05  tff(c_56, plain, (![A_47, B_48]: (r2_hidden('#skF_10'(A_47, B_48), A_47) | r2_hidden('#skF_11'(A_47, B_48), B_48) | k3_tarski(A_47)=B_48)), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_44, plain, (![A_47, C_62]: (r2_hidden('#skF_12'(A_47, k3_tarski(A_47), C_62), A_47) | ~r2_hidden(C_62, k3_tarski(A_47)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_94360, plain, (![A_8740, C_8741]: (r2_hidden('#skF_12'(A_8740, k3_tarski(A_8740), C_8741), A_8740) | ~r2_hidden(C_8741, k3_tarski(A_8740)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_38320, plain, (![A_1735, C_1736]: (r2_hidden('#skF_12'(A_1735, k3_tarski(A_1735), C_1736), A_1735) | ~r2_hidden(C_1736, k3_tarski(A_1735)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_4231, plain, (![A_381, C_382]: (r2_hidden('#skF_12'(A_381, k3_tarski(A_381), C_382), A_381) | ~r2_hidden(C_382, k3_tarski(A_381)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_62, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.78/13.05  tff(c_74, plain, (k1_xboole_0!='#skF_16'), inference(splitLeft, [status(thm)], [c_62])).
% 22.78/13.05  tff(c_64, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.78/13.05  tff(c_73, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_64])).
% 22.78/13.05  tff(c_70, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.78/13.05  tff(c_76, plain, (k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 22.78/13.05  tff(c_221, plain, (![E_106, F_107, A_108, B_109]: (r2_hidden(k4_tarski(E_106, F_107), k2_zfmisc_1(A_108, B_109)) | ~r2_hidden(F_107, B_109) | ~r2_hidden(E_106, A_108))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_228, plain, (![E_106, F_107]: (r2_hidden(k4_tarski(E_106, F_107), k1_xboole_0) | ~r2_hidden(F_107, '#skF_16') | ~r2_hidden(E_106, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_221])).
% 22.78/13.05  tff(c_231, plain, (![E_110, F_111]: (r2_hidden(k4_tarski(E_110, F_111), k1_xboole_0) | ~r2_hidden(F_111, '#skF_16') | ~r2_hidden(E_110, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_221])).
% 22.78/13.05  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 22.78/13.05  tff(c_101, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, B_81) | ~r2_hidden(C_82, A_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_104, plain, (![C_82, A_12]: (~r2_hidden(C_82, k1_xboole_0) | ~r2_hidden(C_82, A_12))), inference(resolution, [status(thm)], [c_16, c_101])).
% 22.78/13.05  tff(c_380, plain, (![E_122, F_123, A_124]: (~r2_hidden(k4_tarski(E_122, F_123), A_124) | ~r2_hidden(F_123, '#skF_16') | ~r2_hidden(E_122, '#skF_15'))), inference(resolution, [status(thm)], [c_231, c_104])).
% 22.78/13.05  tff(c_391, plain, (![F_107, E_106]: (~r2_hidden(F_107, '#skF_16') | ~r2_hidden(E_106, '#skF_15'))), inference(resolution, [status(thm)], [c_228, c_380])).
% 22.78/13.05  tff(c_400, plain, (![E_127]: (~r2_hidden(E_127, '#skF_15'))), inference(splitLeft, [status(thm)], [c_391])).
% 22.78/13.05  tff(c_2040, plain, (![A_232]: (r2_hidden('#skF_10'(A_232, '#skF_15'), A_232) | k3_tarski(A_232)='#skF_15')), inference(resolution, [status(thm)], [c_56, c_400])).
% 22.78/13.05  tff(c_399, plain, (![E_106]: (~r2_hidden(E_106, '#skF_15'))), inference(splitLeft, [status(thm)], [c_391])).
% 22.78/13.05  tff(c_2074, plain, (k3_tarski('#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_2040, c_399])).
% 22.78/13.05  tff(c_452, plain, (![A_129, B_130, D_131]: (r2_hidden('#skF_7'(A_129, B_130, k2_zfmisc_1(A_129, B_130), D_131), A_129) | ~r2_hidden(D_131, k2_zfmisc_1(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_474, plain, (![D_131]: (r2_hidden('#skF_7'('#skF_15', '#skF_16', k1_xboole_0, D_131), '#skF_15') | ~r2_hidden(D_131, k2_zfmisc_1('#skF_15', '#skF_16')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_452])).
% 22.78/13.05  tff(c_481, plain, (![D_131]: (r2_hidden('#skF_7'('#skF_15', '#skF_16', k1_xboole_0, D_131), '#skF_15') | ~r2_hidden(D_131, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_474])).
% 22.78/13.05  tff(c_483, plain, (![D_132]: (~r2_hidden(D_132, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_399, c_481])).
% 22.78/13.05  tff(c_1764, plain, (![A_225]: (r2_hidden('#skF_10'(A_225, k1_xboole_0), A_225) | k3_tarski(A_225)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_483])).
% 22.78/13.05  tff(c_1836, plain, (k3_tarski('#skF_15')=k1_xboole_0), inference(resolution, [status(thm)], [c_1764, c_399])).
% 22.78/13.05  tff(c_2077, plain, (k1_xboole_0='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_1836])).
% 22.78/13.05  tff(c_2079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_2077])).
% 22.78/13.05  tff(c_2081, plain, (![F_233]: (~r2_hidden(F_233, '#skF_16'))), inference(splitRight, [status(thm)], [c_391])).
% 22.78/13.05  tff(c_4105, plain, (![A_357]: (r2_hidden('#skF_10'(A_357, '#skF_16'), A_357) | k3_tarski(A_357)='#skF_16')), inference(resolution, [status(thm)], [c_56, c_2081])).
% 22.78/13.05  tff(c_2080, plain, (![F_107]: (~r2_hidden(F_107, '#skF_16'))), inference(splitRight, [status(thm)], [c_391])).
% 22.78/13.05  tff(c_2365, plain, (![A_252, B_253, D_254]: (r2_hidden('#skF_8'(A_252, B_253, k2_zfmisc_1(A_252, B_253), D_254), B_253) | ~r2_hidden(D_254, k2_zfmisc_1(A_252, B_253)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_2399, plain, (![D_254]: (r2_hidden('#skF_8'('#skF_15', '#skF_16', k1_xboole_0, D_254), '#skF_16') | ~r2_hidden(D_254, k2_zfmisc_1('#skF_15', '#skF_16')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_2365])).
% 22.78/13.05  tff(c_2409, plain, (![D_254]: (r2_hidden('#skF_8'('#skF_15', '#skF_16', k1_xboole_0, D_254), '#skF_16') | ~r2_hidden(D_254, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2399])).
% 22.78/13.05  tff(c_2410, plain, (![D_254]: (~r2_hidden(D_254, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2080, c_2409])).
% 22.78/13.05  tff(c_4142, plain, (k3_tarski(k1_xboole_0)='#skF_16'), inference(resolution, [status(thm)], [c_4105, c_2410])).
% 22.78/13.05  tff(c_2411, plain, (![D_255]: (~r2_hidden(D_255, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2080, c_2409])).
% 22.78/13.05  tff(c_3731, plain, (![A_350]: (r2_hidden('#skF_10'(A_350, k1_xboole_0), A_350) | k3_tarski(A_350)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_2411])).
% 22.78/13.05  tff(c_3819, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3731, c_2410])).
% 22.78/13.05  tff(c_4147, plain, (k1_xboole_0='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_4142, c_3819])).
% 22.78/13.05  tff(c_4149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4147])).
% 22.78/13.05  tff(c_4150, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_70])).
% 22.78/13.05  tff(c_4152, plain, (k1_xboole_0='#skF_14'), inference(splitLeft, [status(thm)], [c_4150])).
% 22.78/13.05  tff(c_4156, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_4152, c_16])).
% 22.78/13.05  tff(c_4175, plain, (![A_367, B_368, C_369]: (~r1_xboole_0(A_367, B_368) | ~r2_hidden(C_369, B_368) | ~r2_hidden(C_369, A_367))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_4178, plain, (![C_369, A_12]: (~r2_hidden(C_369, '#skF_14') | ~r2_hidden(C_369, A_12))), inference(resolution, [status(thm)], [c_4156, c_4175])).
% 22.78/13.05  tff(c_4341, plain, (![C_403, A_404]: (~r2_hidden('#skF_12'('#skF_14', k3_tarski('#skF_14'), C_403), A_404) | ~r2_hidden(C_403, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_4231, c_4178])).
% 22.78/13.05  tff(c_4351, plain, (![C_62]: (~r2_hidden(C_62, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_44, c_4341])).
% 22.78/13.05  tff(c_4352, plain, (![C_405]: (~r2_hidden(C_405, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_44, c_4341])).
% 22.78/13.05  tff(c_18336, plain, (![B_1003]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_1003), B_1003) | k3_tarski(k3_tarski('#skF_14'))=B_1003)), inference(resolution, [status(thm)], [c_56, c_4352])).
% 22.78/13.05  tff(c_18624, plain, (k3_tarski(k3_tarski('#skF_14'))=k3_tarski('#skF_14')), inference(resolution, [status(thm)], [c_18336, c_4351])).
% 22.78/13.05  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 22.78/13.05  tff(c_4155, plain, (![A_11]: (r1_tarski('#skF_14', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_4152, c_14])).
% 22.78/13.05  tff(c_4287, plain, (![A_394, B_395]: (r2_hidden('#skF_10'(A_394, B_395), A_394) | r2_hidden('#skF_11'(A_394, B_395), B_395) | k3_tarski(A_394)=B_395)), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.78/13.05  tff(c_4303, plain, (![A_394, B_395, B_2]: (r2_hidden('#skF_11'(A_394, B_395), B_2) | ~r1_tarski(B_395, B_2) | r2_hidden('#skF_10'(A_394, B_395), A_394) | k3_tarski(A_394)=B_395)), inference(resolution, [status(thm)], [c_4287, c_2])).
% 22.78/13.05  tff(c_4394, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_48), B_48) | k3_tarski(k3_tarski('#skF_14'))=B_48)), inference(resolution, [status(thm)], [c_56, c_4352])).
% 22.78/13.05  tff(c_19665, plain, (![B_1011]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_1011), B_1011) | k3_tarski('#skF_14')=B_1011)), inference(demodulation, [status(thm), theory('equality')], [c_18624, c_4394])).
% 22.78/13.05  tff(c_19753, plain, (![A_12]: (~r2_hidden('#skF_11'(k3_tarski('#skF_14'), '#skF_14'), A_12) | k3_tarski('#skF_14')='#skF_14')), inference(resolution, [status(thm)], [c_19665, c_4178])).
% 22.78/13.05  tff(c_19956, plain, (![A_1017]: (~r2_hidden('#skF_11'(k3_tarski('#skF_14'), '#skF_14'), A_1017))), inference(splitLeft, [status(thm)], [c_19753])).
% 22.78/13.05  tff(c_19974, plain, (![B_2]: (~r1_tarski('#skF_14', B_2) | r2_hidden('#skF_10'(k3_tarski('#skF_14'), '#skF_14'), k3_tarski('#skF_14')) | k3_tarski(k3_tarski('#skF_14'))='#skF_14')), inference(resolution, [status(thm)], [c_4303, c_19956])).
% 22.78/13.05  tff(c_19999, plain, (r2_hidden('#skF_10'(k3_tarski('#skF_14'), '#skF_14'), k3_tarski('#skF_14')) | k3_tarski('#skF_14')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_18624, c_4155, c_19974])).
% 22.78/13.05  tff(c_20000, plain, (k3_tarski('#skF_14')='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_4351, c_19999])).
% 22.78/13.05  tff(c_4483, plain, (![A_416, B_417, D_418]: (r2_hidden('#skF_8'(A_416, B_417, k2_zfmisc_1(A_416, B_417), D_418), B_417) | ~r2_hidden(D_418, k2_zfmisc_1(A_416, B_417)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_4500, plain, (![D_418, A_416]: (~r2_hidden(D_418, k2_zfmisc_1(A_416, k3_tarski('#skF_14'))))), inference(resolution, [status(thm)], [c_4483, c_4351])).
% 22.78/13.05  tff(c_18621, plain, (![A_416]: (k2_zfmisc_1(A_416, k3_tarski('#skF_14'))=k3_tarski(k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_18336, c_4500])).
% 22.78/13.05  tff(c_19248, plain, (![A_416]: (k2_zfmisc_1(A_416, k3_tarski('#skF_14'))=k3_tarski('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_18624, c_18621])).
% 22.78/13.05  tff(c_20223, plain, (![A_416]: (k2_zfmisc_1(A_416, '#skF_14')='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_20000, c_20000, c_19248])).
% 22.78/13.05  tff(c_4151, plain, (k2_zfmisc_1('#skF_15', '#skF_16')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 22.78/13.05  tff(c_4163, plain, (k2_zfmisc_1('#skF_15', '#skF_16')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_4152, c_4151])).
% 22.78/13.05  tff(c_68, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.78/13.05  tff(c_4165, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14' | k2_zfmisc_1('#skF_15', '#skF_16')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_4152, c_4152, c_68])).
% 22.78/13.05  tff(c_4166, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_4163, c_4165])).
% 22.78/13.05  tff(c_20437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20223, c_4166])).
% 22.78/13.05  tff(c_20438, plain, (k3_tarski('#skF_14')='#skF_14'), inference(splitRight, [status(thm)], [c_19753])).
% 22.78/13.05  tff(c_20443, plain, (![A_416]: (k2_zfmisc_1(A_416, '#skF_14')='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_20438, c_20438, c_19248])).
% 22.78/13.05  tff(c_20851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20443, c_4166])).
% 22.78/13.05  tff(c_20852, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_4150])).
% 22.78/13.05  tff(c_38219, plain, (k2_zfmisc_1('#skF_15', '#skF_16')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_20852, c_4151])).
% 22.78/13.05  tff(c_20940, plain, (![A_1053, C_1054]: (r2_hidden('#skF_12'(A_1053, k3_tarski(A_1053), C_1054), A_1053) | ~r2_hidden(C_1054, k3_tarski(A_1053)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_20858, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_20852, c_16])).
% 22.78/13.05  tff(c_20877, plain, (![A_1037, B_1038, C_1039]: (~r1_xboole_0(A_1037, B_1038) | ~r2_hidden(C_1039, B_1038) | ~r2_hidden(C_1039, A_1037))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_20880, plain, (![C_1039, A_12]: (~r2_hidden(C_1039, '#skF_13') | ~r2_hidden(C_1039, A_12))), inference(resolution, [status(thm)], [c_20858, c_20877])).
% 22.78/13.05  tff(c_21113, plain, (![C_1085, A_1086]: (~r2_hidden('#skF_12'('#skF_13', k3_tarski('#skF_13'), C_1085), A_1086) | ~r2_hidden(C_1085, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_20940, c_20880])).
% 22.78/13.05  tff(c_21122, plain, (![C_62]: (~r2_hidden(C_62, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_44, c_21113])).
% 22.78/13.05  tff(c_21124, plain, (![C_1087]: (~r2_hidden(C_1087, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_44, c_21113])).
% 22.78/13.05  tff(c_36049, plain, (![B_1684]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_1684), B_1684) | k3_tarski(k3_tarski('#skF_13'))=B_1684)), inference(resolution, [status(thm)], [c_56, c_21124])).
% 22.78/13.05  tff(c_36339, plain, (k3_tarski(k3_tarski('#skF_13'))=k3_tarski('#skF_13')), inference(resolution, [status(thm)], [c_36049, c_21122])).
% 22.78/13.05  tff(c_20857, plain, (![A_11]: (r1_tarski('#skF_13', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_20852, c_14])).
% 22.78/13.05  tff(c_21047, plain, (![A_1074, B_1075]: (r2_hidden('#skF_10'(A_1074, B_1075), A_1074) | r2_hidden('#skF_11'(A_1074, B_1075), B_1075) | k3_tarski(A_1074)=B_1075)), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_21063, plain, (![A_1074, B_1075, B_2]: (r2_hidden('#skF_11'(A_1074, B_1075), B_2) | ~r1_tarski(B_1075, B_2) | r2_hidden('#skF_10'(A_1074, B_1075), A_1074) | k3_tarski(A_1074)=B_1075)), inference(resolution, [status(thm)], [c_21047, c_2])).
% 22.78/13.05  tff(c_21165, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_48), B_48) | k3_tarski(k3_tarski('#skF_13'))=B_48)), inference(resolution, [status(thm)], [c_56, c_21124])).
% 22.78/13.05  tff(c_37238, plain, (![B_1692]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_1692), B_1692) | k3_tarski('#skF_13')=B_1692)), inference(demodulation, [status(thm), theory('equality')], [c_36339, c_21165])).
% 22.78/13.05  tff(c_37329, plain, (![A_12]: (~r2_hidden('#skF_11'(k3_tarski('#skF_13'), '#skF_13'), A_12) | k3_tarski('#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_37238, c_20880])).
% 22.78/13.05  tff(c_37564, plain, (![A_1699]: (~r2_hidden('#skF_11'(k3_tarski('#skF_13'), '#skF_13'), A_1699))), inference(splitLeft, [status(thm)], [c_37329])).
% 22.78/13.05  tff(c_37586, plain, (![B_2]: (~r1_tarski('#skF_13', B_2) | r2_hidden('#skF_10'(k3_tarski('#skF_13'), '#skF_13'), k3_tarski('#skF_13')) | k3_tarski(k3_tarski('#skF_13'))='#skF_13')), inference(resolution, [status(thm)], [c_21063, c_37564])).
% 22.78/13.05  tff(c_37610, plain, (r2_hidden('#skF_10'(k3_tarski('#skF_13'), '#skF_13'), k3_tarski('#skF_13')) | k3_tarski('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_36339, c_20857, c_37586])).
% 22.78/13.05  tff(c_37611, plain, (k3_tarski('#skF_13')='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_21122, c_37610])).
% 22.78/13.05  tff(c_21272, plain, (![A_1097, B_1098, D_1099]: (r2_hidden('#skF_7'(A_1097, B_1098, k2_zfmisc_1(A_1097, B_1098), D_1099), A_1097) | ~r2_hidden(D_1099, k2_zfmisc_1(A_1097, B_1098)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_21291, plain, (![D_1099, B_1098]: (~r2_hidden(D_1099, k2_zfmisc_1(k3_tarski('#skF_13'), B_1098)))), inference(resolution, [status(thm)], [c_21272, c_21122])).
% 22.78/13.05  tff(c_36335, plain, (![B_1098]: (k2_zfmisc_1(k3_tarski('#skF_13'), B_1098)=k3_tarski(k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_36049, c_21291])).
% 22.78/13.05  tff(c_36590, plain, (![B_1098]: (k2_zfmisc_1(k3_tarski('#skF_13'), B_1098)=k3_tarski('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_36339, c_36335])).
% 22.78/13.05  tff(c_37623, plain, (![B_1098]: (k2_zfmisc_1('#skF_13', B_1098)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_37611, c_37611, c_36590])).
% 22.78/13.05  tff(c_20854, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 22.78/13.05  tff(c_20866, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_20852, c_20854])).
% 22.78/13.05  tff(c_37836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37623, c_20866])).
% 22.78/13.05  tff(c_37837, plain, (k3_tarski('#skF_13')='#skF_13'), inference(splitRight, [status(thm)], [c_37329])).
% 22.78/13.05  tff(c_37843, plain, (![B_1098]: (k2_zfmisc_1('#skF_13', B_1098)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_37837, c_37837, c_36590])).
% 22.78/13.05  tff(c_38200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37843, c_20866])).
% 22.78/13.05  tff(c_38201, plain, (k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 22.78/13.05  tff(c_38220, plain, (k2_zfmisc_1('#skF_15', '#skF_16')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_20852, c_38201])).
% 22.78/13.05  tff(c_38221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38219, c_38220])).
% 22.78/13.05  tff(c_38223, plain, (k1_xboole_0='#skF_16'), inference(splitRight, [status(thm)], [c_62])).
% 22.78/13.05  tff(c_38222, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_62])).
% 22.78/13.05  tff(c_38234, plain, ('#skF_16'='#skF_13' | '#skF_16'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_38223, c_38223, c_38222])).
% 22.78/13.05  tff(c_38235, plain, ('#skF_16'='#skF_14'), inference(splitLeft, [status(thm)], [c_38234])).
% 22.78/13.05  tff(c_38226, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_16'))), inference(demodulation, [status(thm), theory('equality')], [c_38223, c_16])).
% 22.78/13.05  tff(c_38236, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_38235, c_38226])).
% 22.78/13.05  tff(c_38274, plain, (![A_1724, B_1725, C_1726]: (~r1_xboole_0(A_1724, B_1725) | ~r2_hidden(C_1726, B_1725) | ~r2_hidden(C_1726, A_1724))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_38277, plain, (![C_1726, A_12]: (~r2_hidden(C_1726, '#skF_14') | ~r2_hidden(C_1726, A_12))), inference(resolution, [status(thm)], [c_38236, c_38274])).
% 22.78/13.05  tff(c_38394, plain, (![C_1754, A_1755]: (~r2_hidden('#skF_12'('#skF_14', k3_tarski('#skF_14'), C_1754), A_1755) | ~r2_hidden(C_1754, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_38320, c_38277])).
% 22.78/13.05  tff(c_38404, plain, (![C_62]: (~r2_hidden(C_62, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_44, c_38394])).
% 22.78/13.05  tff(c_38455, plain, (![A_1760, B_1761]: (r2_hidden('#skF_10'(A_1760, B_1761), A_1760) | r2_hidden('#skF_11'(A_1760, B_1761), B_1761) | k3_tarski(A_1760)=B_1761)), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_52508, plain, (![B_2355]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_2355), B_2355) | k3_tarski(k3_tarski('#skF_14'))=B_2355)), inference(resolution, [status(thm)], [c_38455, c_38404])).
% 22.78/13.05  tff(c_52796, plain, (k3_tarski(k3_tarski('#skF_14'))=k3_tarski('#skF_14')), inference(resolution, [status(thm)], [c_52508, c_38404])).
% 22.78/13.05  tff(c_38225, plain, (![A_11]: (r1_tarski('#skF_16', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_38223, c_14])).
% 22.78/13.05  tff(c_38237, plain, (![A_11]: (r1_tarski('#skF_14', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_38235, c_38225])).
% 22.78/13.05  tff(c_38482, plain, (![A_1760, B_1761, B_2]: (r2_hidden('#skF_11'(A_1760, B_1761), B_2) | ~r1_tarski(B_1761, B_2) | r2_hidden('#skF_10'(A_1760, B_1761), A_1760) | k3_tarski(A_1760)=B_1761)), inference(resolution, [status(thm)], [c_38455, c_2])).
% 22.78/13.05  tff(c_38476, plain, (![B_1761]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_1761), B_1761) | k3_tarski(k3_tarski('#skF_14'))=B_1761)), inference(resolution, [status(thm)], [c_38455, c_38404])).
% 22.78/13.05  tff(c_53836, plain, (![B_2363]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_2363), B_2363) | k3_tarski('#skF_14')=B_2363)), inference(demodulation, [status(thm), theory('equality')], [c_52796, c_38476])).
% 22.78/13.05  tff(c_53923, plain, (![A_12]: (~r2_hidden('#skF_11'(k3_tarski('#skF_14'), '#skF_14'), A_12) | k3_tarski('#skF_14')='#skF_14')), inference(resolution, [status(thm)], [c_53836, c_38277])).
% 22.78/13.05  tff(c_54159, plain, (![A_2370]: (~r2_hidden('#skF_11'(k3_tarski('#skF_14'), '#skF_14'), A_2370))), inference(splitLeft, [status(thm)], [c_53923])).
% 22.78/13.05  tff(c_54181, plain, (![B_2]: (~r1_tarski('#skF_14', B_2) | r2_hidden('#skF_10'(k3_tarski('#skF_14'), '#skF_14'), k3_tarski('#skF_14')) | k3_tarski(k3_tarski('#skF_14'))='#skF_14')), inference(resolution, [status(thm)], [c_38482, c_54159])).
% 22.78/13.05  tff(c_54205, plain, (r2_hidden('#skF_10'(k3_tarski('#skF_14'), '#skF_14'), k3_tarski('#skF_14')) | k3_tarski('#skF_14')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_52796, c_38237, c_54181])).
% 22.78/13.05  tff(c_54206, plain, (k3_tarski('#skF_14')='#skF_14'), inference(negUnitSimplification, [status(thm)], [c_38404, c_54205])).
% 22.78/13.05  tff(c_38686, plain, (![A_1776, B_1777, D_1778]: (r2_hidden('#skF_8'(A_1776, B_1777, k2_zfmisc_1(A_1776, B_1777), D_1778), B_1777) | ~r2_hidden(D_1778, k2_zfmisc_1(A_1776, B_1777)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_38713, plain, (![D_1778, A_1776]: (~r2_hidden(D_1778, k2_zfmisc_1(A_1776, k3_tarski('#skF_14'))))), inference(resolution, [status(thm)], [c_38686, c_38404])).
% 22.78/13.05  tff(c_52791, plain, (![A_1776]: (k2_zfmisc_1(A_1776, k3_tarski('#skF_14'))=k3_tarski(k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_52508, c_38713])).
% 22.78/13.05  tff(c_53046, plain, (![A_1776]: (k2_zfmisc_1(A_1776, k3_tarski('#skF_14'))=k3_tarski('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_52796, c_52791])).
% 22.78/13.05  tff(c_54427, plain, (![A_1776]: (k2_zfmisc_1(A_1776, '#skF_14')='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_54206, c_54206, c_53046])).
% 22.78/13.05  tff(c_38239, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_38235, c_38223])).
% 22.78/13.05  tff(c_60, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.78/13.05  tff(c_38251, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_38239, c_38235, c_38239, c_60])).
% 22.78/13.05  tff(c_54690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54427, c_38251])).
% 22.78/13.05  tff(c_54691, plain, (k3_tarski('#skF_14')='#skF_14'), inference(splitRight, [status(thm)], [c_53923])).
% 22.78/13.05  tff(c_54850, plain, (![A_1776]: (k2_zfmisc_1(A_1776, '#skF_14')='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_54691, c_54691, c_53046])).
% 22.78/13.05  tff(c_55302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54850, c_38251])).
% 22.78/13.05  tff(c_55303, plain, ('#skF_16'='#skF_13'), inference(splitRight, [status(thm)], [c_38234])).
% 22.78/13.05  tff(c_55304, plain, ('#skF_16'!='#skF_14'), inference(splitRight, [status(thm)], [c_38234])).
% 22.78/13.05  tff(c_55313, plain, ('#skF_14'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_55303, c_55304])).
% 22.78/13.05  tff(c_55306, plain, (![A_11]: (r1_tarski('#skF_13', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_55303, c_38225])).
% 22.78/13.05  tff(c_55391, plain, (![A_2409, C_2410]: (r2_hidden('#skF_12'(A_2409, k3_tarski(A_2409), C_2410), A_2409) | ~r2_hidden(C_2410, k3_tarski(A_2409)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_55305, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_55303, c_38226])).
% 22.78/13.05  tff(c_55335, plain, (![A_2395, B_2396, C_2397]: (~r1_xboole_0(A_2395, B_2396) | ~r2_hidden(C_2397, B_2396) | ~r2_hidden(C_2397, A_2395))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_55338, plain, (![C_2397, A_12]: (~r2_hidden(C_2397, '#skF_13') | ~r2_hidden(C_2397, A_12))), inference(resolution, [status(thm)], [c_55305, c_55335])).
% 22.78/13.05  tff(c_55625, plain, (![C_2449, A_2450]: (~r2_hidden('#skF_12'('#skF_13', k3_tarski('#skF_13'), C_2449), A_2450) | ~r2_hidden(C_2449, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_55391, c_55338])).
% 22.78/13.05  tff(c_55636, plain, (![C_2451]: (~r2_hidden(C_2451, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_44, c_55625])).
% 22.78/13.05  tff(c_71099, plain, (![A_3061]: (r2_hidden('#skF_10'(A_3061, k3_tarski('#skF_13')), A_3061) | k3_tarski(A_3061)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_56, c_55636])).
% 22.78/13.05  tff(c_55635, plain, (![C_62]: (~r2_hidden(C_62, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_44, c_55625])).
% 22.78/13.05  tff(c_71395, plain, (k3_tarski(k3_tarski('#skF_13'))=k3_tarski('#skF_13')), inference(resolution, [status(thm)], [c_71099, c_55635])).
% 22.78/13.05  tff(c_55682, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_48), B_48) | k3_tarski(k3_tarski('#skF_13'))=B_48)), inference(resolution, [status(thm)], [c_56, c_55636])).
% 22.78/13.05  tff(c_72169, plain, (![B_3068]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_3068), B_3068) | k3_tarski('#skF_13')=B_3068)), inference(demodulation, [status(thm), theory('equality')], [c_71395, c_55682])).
% 22.78/13.05  tff(c_55608, plain, (![A_2446, B_2447, D_2448]: (r2_hidden('#skF_7'(A_2446, B_2447, k2_zfmisc_1(A_2446, B_2447), D_2448), A_2446) | ~r2_hidden(D_2448, k2_zfmisc_1(A_2446, B_2447)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_65691, plain, (![A_2941, B_2942, D_2943, B_2944]: (r2_hidden('#skF_7'(A_2941, B_2942, k2_zfmisc_1(A_2941, B_2942), D_2943), B_2944) | ~r1_tarski(A_2941, B_2944) | ~r2_hidden(D_2943, k2_zfmisc_1(A_2941, B_2942)))), inference(resolution, [status(thm)], [c_55608, c_2])).
% 22.78/13.05  tff(c_65956, plain, (![A_2941, D_2943, B_2942]: (~r1_tarski(A_2941, k3_tarski('#skF_13')) | ~r2_hidden(D_2943, k2_zfmisc_1(A_2941, B_2942)))), inference(resolution, [status(thm)], [c_65691, c_55635])).
% 22.78/13.05  tff(c_73158, plain, (![A_3080, B_3081]: (~r1_tarski(A_3080, k3_tarski('#skF_13')) | k2_zfmisc_1(A_3080, B_3081)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_72169, c_65956])).
% 22.78/13.05  tff(c_73188, plain, (![B_3081]: (k2_zfmisc_1('#skF_13', B_3081)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_55306, c_73158])).
% 22.78/13.05  tff(c_55308, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_55303, c_38223])).
% 22.78/13.05  tff(c_55321, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_55308, c_55303, c_55308, c_60])).
% 22.78/13.05  tff(c_73189, plain, (k3_tarski('#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_73188, c_55321])).
% 22.78/13.05  tff(c_72168, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_48), B_48) | k3_tarski('#skF_13')=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_71395, c_55682])).
% 22.78/13.05  tff(c_73190, plain, (![B_3082]: (k2_zfmisc_1('#skF_13', B_3082)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_55306, c_73158])).
% 22.78/13.05  tff(c_18, plain, (![E_45, F_46, A_13, B_14]: (r2_hidden(k4_tarski(E_45, F_46), k2_zfmisc_1(A_13, B_14)) | ~r2_hidden(F_46, B_14) | ~r2_hidden(E_45, A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_73248, plain, (![E_45, F_46, B_3082]: (r2_hidden(k4_tarski(E_45, F_46), k3_tarski('#skF_13')) | ~r2_hidden(F_46, B_3082) | ~r2_hidden(E_45, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_73190, c_18])).
% 22.78/13.05  tff(c_73279, plain, (![F_46, B_3082, E_45]: (~r2_hidden(F_46, B_3082) | ~r2_hidden(E_45, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_55635, c_73248])).
% 22.78/13.05  tff(c_73308, plain, (![E_3086]: (~r2_hidden(E_3086, '#skF_13'))), inference(splitLeft, [status(thm)], [c_73279])).
% 22.78/13.05  tff(c_73312, plain, (k3_tarski('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_72168, c_73308])).
% 22.78/13.05  tff(c_73442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73189, c_73312])).
% 22.78/13.05  tff(c_73443, plain, (![F_46, B_3082]: (~r2_hidden(F_46, B_3082))), inference(splitRight, [status(thm)], [c_73279])).
% 22.78/13.05  tff(c_58, plain, (![A_47, B_48]: (r2_hidden('#skF_9'(A_47, B_48), '#skF_10'(A_47, B_48)) | r2_hidden('#skF_11'(A_47, B_48), B_48) | k3_tarski(A_47)=B_48)), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_73532, plain, (![A_3089]: (k3_tarski(A_3089)='#skF_14')), inference(negUnitSimplification, [status(thm)], [c_73443, c_73443, c_58])).
% 22.78/13.05  tff(c_73488, plain, (![A_47, B_48]: (k3_tarski(A_47)=B_48)), inference(negUnitSimplification, [status(thm)], [c_73443, c_73443, c_58])).
% 22.78/13.05  tff(c_74820, plain, (![B_4360]: (B_4360='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_73532, c_73488])).
% 22.78/13.05  tff(c_74871, plain, ('#skF_14'='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_74820, c_55308])).
% 22.78/13.05  tff(c_74881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55313, c_74871])).
% 22.78/13.05  tff(c_74883, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_64])).
% 22.78/13.05  tff(c_66, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_83])).
% 22.78/13.05  tff(c_74897, plain, ('#skF_15'='#skF_14' | '#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_74883, c_74883, c_74883, c_66])).
% 22.78/13.05  tff(c_74898, plain, ('#skF_15'='#skF_13'), inference(splitLeft, [status(thm)], [c_74897])).
% 22.78/13.05  tff(c_74884, plain, (![A_11]: (r1_tarski('#skF_15', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_74883, c_14])).
% 22.78/13.05  tff(c_74903, plain, (![A_11]: (r1_tarski('#skF_13', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_74898, c_74884])).
% 22.78/13.05  tff(c_74982, plain, (![A_5680, C_5681]: (r2_hidden('#skF_12'(A_5680, k3_tarski(A_5680), C_5681), A_5680) | ~r2_hidden(C_5681, k3_tarski(A_5680)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.78/13.05  tff(c_74885, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_74883, c_16])).
% 22.78/13.05  tff(c_74902, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_74898, c_74885])).
% 22.78/13.05  tff(c_74926, plain, (![A_5666, B_5667, C_5668]: (~r1_xboole_0(A_5666, B_5667) | ~r2_hidden(C_5668, B_5667) | ~r2_hidden(C_5668, A_5666))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_74929, plain, (![C_5668, A_12]: (~r2_hidden(C_5668, '#skF_13') | ~r2_hidden(C_5668, A_12))), inference(resolution, [status(thm)], [c_74902, c_74926])).
% 22.78/13.05  tff(c_75217, plain, (![C_5720, A_5721]: (~r2_hidden('#skF_12'('#skF_13', k3_tarski('#skF_13'), C_5720), A_5721) | ~r2_hidden(C_5720, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_74982, c_74929])).
% 22.78/13.05  tff(c_75228, plain, (![C_5722]: (~r2_hidden(C_5722, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_44, c_75217])).
% 22.78/13.05  tff(c_90176, plain, (![A_6324]: (r2_hidden('#skF_10'(A_6324, k3_tarski('#skF_13')), A_6324) | k3_tarski(A_6324)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_56, c_75228])).
% 22.78/13.05  tff(c_75227, plain, (![C_62]: (~r2_hidden(C_62, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_44, c_75217])).
% 22.78/13.05  tff(c_90464, plain, (k3_tarski(k3_tarski('#skF_13'))=k3_tarski('#skF_13')), inference(resolution, [status(thm)], [c_90176, c_75227])).
% 22.78/13.05  tff(c_75275, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_48), B_48) | k3_tarski(k3_tarski('#skF_13'))=B_48)), inference(resolution, [status(thm)], [c_56, c_75228])).
% 22.78/13.05  tff(c_91238, plain, (![B_6331]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_6331), B_6331) | k3_tarski('#skF_13')=B_6331)), inference(demodulation, [status(thm), theory('equality')], [c_90464, c_75275])).
% 22.78/13.05  tff(c_75293, plain, (![A_5726, B_5727, D_5728]: (r2_hidden('#skF_7'(A_5726, B_5727, k2_zfmisc_1(A_5726, B_5727), D_5728), A_5726) | ~r2_hidden(D_5728, k2_zfmisc_1(A_5726, B_5727)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_85337, plain, (![A_6226, B_6227, D_6228, B_6229]: (r2_hidden('#skF_7'(A_6226, B_6227, k2_zfmisc_1(A_6226, B_6227), D_6228), B_6229) | ~r1_tarski(A_6226, B_6229) | ~r2_hidden(D_6228, k2_zfmisc_1(A_6226, B_6227)))), inference(resolution, [status(thm)], [c_75293, c_2])).
% 22.78/13.05  tff(c_85601, plain, (![A_6226, D_6228, B_6227]: (~r1_tarski(A_6226, k3_tarski('#skF_13')) | ~r2_hidden(D_6228, k2_zfmisc_1(A_6226, B_6227)))), inference(resolution, [status(thm)], [c_85337, c_75227])).
% 22.78/13.05  tff(c_92366, plain, (![A_6347, B_6348]: (~r1_tarski(A_6347, k3_tarski('#skF_13')) | k2_zfmisc_1(A_6347, B_6348)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_91238, c_85601])).
% 22.78/13.05  tff(c_92396, plain, (![B_6348]: (k2_zfmisc_1('#skF_13', B_6348)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_74903, c_92366])).
% 22.78/13.05  tff(c_74882, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 22.78/13.05  tff(c_74892, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_74883, c_74882])).
% 22.78/13.05  tff(c_74901, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_74898, c_74892])).
% 22.78/13.05  tff(c_92397, plain, (k3_tarski('#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_92396, c_74901])).
% 22.78/13.05  tff(c_91237, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_13'), B_48), B_48) | k3_tarski('#skF_13')=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_90464, c_75275])).
% 22.78/13.05  tff(c_92398, plain, (![B_6349]: (k2_zfmisc_1('#skF_13', B_6349)=k3_tarski('#skF_13'))), inference(resolution, [status(thm)], [c_74903, c_92366])).
% 22.78/13.05  tff(c_92459, plain, (![E_45, F_46, B_6349]: (r2_hidden(k4_tarski(E_45, F_46), k3_tarski('#skF_13')) | ~r2_hidden(F_46, B_6349) | ~r2_hidden(E_45, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_92398, c_18])).
% 22.78/13.05  tff(c_92491, plain, (![F_46, B_6349, E_45]: (~r2_hidden(F_46, B_6349) | ~r2_hidden(E_45, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_75227, c_92459])).
% 22.78/13.05  tff(c_92707, plain, (![E_6353]: (~r2_hidden(E_6353, '#skF_13'))), inference(splitLeft, [status(thm)], [c_92491])).
% 22.78/13.05  tff(c_92711, plain, (k3_tarski('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_91237, c_92707])).
% 22.78/13.05  tff(c_92841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92397, c_92711])).
% 22.78/13.05  tff(c_92842, plain, (![F_46, B_6349]: (~r2_hidden(F_46, B_6349))), inference(splitRight, [status(thm)], [c_92491])).
% 22.78/13.05  tff(c_92925, plain, (![A_6356]: (k3_tarski(A_6356)='#skF_13')), inference(negUnitSimplification, [status(thm)], [c_92842, c_92842, c_58])).
% 22.78/13.05  tff(c_92885, plain, (![A_47, B_48]: (k3_tarski(A_47)=B_48)), inference(negUnitSimplification, [status(thm)], [c_92842, c_92842, c_58])).
% 22.78/13.05  tff(c_94217, plain, (![B_7536]: (B_7536='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_92925, c_92885])).
% 22.78/13.05  tff(c_94271, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_94217, c_92397])).
% 22.78/13.05  tff(c_94272, plain, ('#skF_15'='#skF_14'), inference(splitRight, [status(thm)], [c_74897])).
% 22.78/13.05  tff(c_94276, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_94272, c_74885])).
% 22.78/13.05  tff(c_94314, plain, (![A_8729, B_8730, C_8731]: (~r1_xboole_0(A_8729, B_8730) | ~r2_hidden(C_8731, B_8730) | ~r2_hidden(C_8731, A_8729))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.78/13.05  tff(c_94317, plain, (![C_8731, A_12]: (~r2_hidden(C_8731, '#skF_14') | ~r2_hidden(C_8731, A_12))), inference(resolution, [status(thm)], [c_94276, c_94314])).
% 22.78/13.05  tff(c_94680, plain, (![C_8791, A_8792]: (~r2_hidden('#skF_12'('#skF_14', k3_tarski('#skF_14'), C_8791), A_8792) | ~r2_hidden(C_8791, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_94360, c_94317])).
% 22.78/13.05  tff(c_94691, plain, (![C_8793]: (~r2_hidden(C_8793, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_44, c_94680])).
% 22.78/13.05  tff(c_110135, plain, (![A_9400]: (r2_hidden('#skF_10'(A_9400, k3_tarski('#skF_14')), A_9400) | k3_tarski(A_9400)=k3_tarski('#skF_14'))), inference(resolution, [status(thm)], [c_56, c_94691])).
% 22.78/13.05  tff(c_94690, plain, (![C_62]: (~r2_hidden(C_62, k3_tarski('#skF_14')))), inference(resolution, [status(thm)], [c_44, c_94680])).
% 22.78/13.05  tff(c_110431, plain, (k3_tarski(k3_tarski('#skF_14'))=k3_tarski('#skF_14')), inference(resolution, [status(thm)], [c_110135, c_94690])).
% 22.78/13.05  tff(c_94746, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_48), B_48) | k3_tarski(k3_tarski('#skF_14'))=B_48)), inference(resolution, [status(thm)], [c_56, c_94691])).
% 22.78/13.05  tff(c_111204, plain, (![B_48]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_48), B_48) | k3_tarski('#skF_14')=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_110431, c_94746])).
% 22.78/13.05  tff(c_94277, plain, (![A_11]: (r1_tarski('#skF_14', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_94272, c_74884])).
% 22.78/13.05  tff(c_111205, plain, (![B_9407]: (r2_hidden('#skF_11'(k3_tarski('#skF_14'), B_9407), B_9407) | k3_tarski('#skF_14')=B_9407)), inference(demodulation, [status(thm), theory('equality')], [c_110431, c_94746])).
% 22.78/13.05  tff(c_94577, plain, (![A_8777, B_8778, D_8779]: (r2_hidden('#skF_7'(A_8777, B_8778, k2_zfmisc_1(A_8777, B_8778), D_8779), A_8777) | ~r2_hidden(D_8779, k2_zfmisc_1(A_8777, B_8778)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_104897, plain, (![A_9296, B_9297, D_9298, B_9299]: (r2_hidden('#skF_7'(A_9296, B_9297, k2_zfmisc_1(A_9296, B_9297), D_9298), B_9299) | ~r1_tarski(A_9296, B_9299) | ~r2_hidden(D_9298, k2_zfmisc_1(A_9296, B_9297)))), inference(resolution, [status(thm)], [c_94577, c_2])).
% 22.78/13.05  tff(c_105161, plain, (![A_9296, D_9298, B_9297]: (~r1_tarski(A_9296, k3_tarski('#skF_14')) | ~r2_hidden(D_9298, k2_zfmisc_1(A_9296, B_9297)))), inference(resolution, [status(thm)], [c_104897, c_94690])).
% 22.78/13.05  tff(c_112194, plain, (![A_9419, B_9420]: (~r1_tarski(A_9419, k3_tarski('#skF_14')) | k2_zfmisc_1(A_9419, B_9420)=k3_tarski('#skF_14'))), inference(resolution, [status(thm)], [c_111205, c_105161])).
% 22.78/13.05  tff(c_112225, plain, (![B_9421]: (k2_zfmisc_1('#skF_14', B_9421)=k3_tarski('#skF_14'))), inference(resolution, [status(thm)], [c_94277, c_112194])).
% 22.78/13.05  tff(c_112286, plain, (![E_45, F_46, B_9421]: (r2_hidden(k4_tarski(E_45, F_46), k3_tarski('#skF_14')) | ~r2_hidden(F_46, B_9421) | ~r2_hidden(E_45, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_112225, c_18])).
% 22.78/13.05  tff(c_112317, plain, (![F_46, B_9421, E_45]: (~r2_hidden(F_46, B_9421) | ~r2_hidden(E_45, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_94690, c_112286])).
% 22.78/13.05  tff(c_112346, plain, (![E_9425]: (~r2_hidden(E_9425, '#skF_14'))), inference(splitLeft, [status(thm)], [c_112317])).
% 22.78/13.05  tff(c_112477, plain, (k3_tarski('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_111204, c_112346])).
% 22.78/13.05  tff(c_22, plain, (![A_13, B_14, D_40]: (r2_hidden('#skF_8'(A_13, B_14, k2_zfmisc_1(A_13, B_14), D_40), B_14) | ~r2_hidden(D_40, k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.78/13.05  tff(c_94740, plain, (![D_40, A_13]: (~r2_hidden(D_40, k2_zfmisc_1(A_13, k3_tarski('#skF_14'))))), inference(resolution, [status(thm)], [c_22, c_94691])).
% 22.78/13.05  tff(c_111358, plain, (![A_13]: (k2_zfmisc_1(A_13, k3_tarski('#skF_14'))=k3_tarski('#skF_14'))), inference(resolution, [status(thm)], [c_111205, c_94740])).
% 22.78/13.05  tff(c_112514, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_14')='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_112477, c_112477, c_111358])).
% 22.78/13.05  tff(c_94275, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_94272, c_74892])).
% 22.78/13.05  tff(c_112822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112514, c_94275])).
% 22.78/13.05  tff(c_112823, plain, (![F_46, B_9421]: (~r2_hidden(F_46, B_9421))), inference(splitRight, [status(thm)], [c_112317])).
% 22.78/13.05  tff(c_114109, plain, (![A_47]: (k3_tarski(A_47)='#skF_14')), inference(negUnitSimplification, [status(thm)], [c_112823, c_112823, c_58])).
% 22.78/13.05  tff(c_112884, plain, (![A_9431, B_9432]: (k3_tarski(A_9431)=B_9432)), inference(negUnitSimplification, [status(thm)], [c_112823, c_112823, c_58])).
% 22.78/13.05  tff(c_114402, plain, (![B_14870]: (B_14870='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_114109, c_112884])).
% 22.78/13.05  tff(c_112891, plain, (![A_9431]: (k3_tarski(A_9431)='#skF_15')), inference(negUnitSimplification, [status(thm)], [c_112823, c_112823, c_58])).
% 22.78/13.05  tff(c_112867, plain, (![A_47, B_48]: (k3_tarski(A_47)=B_48)), inference(negUnitSimplification, [status(thm)], [c_112823, c_112823, c_58])).
% 22.78/13.05  tff(c_114268, plain, (![B_11980]: (B_11980='#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_112891, c_112867])).
% 22.78/13.05  tff(c_114325, plain, ('#skF_15'!='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_114268, c_94275])).
% 22.78/13.05  tff(c_114490, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_114402, c_114325])).
% 22.78/13.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.78/13.05  
% 22.78/13.05  Inference rules
% 22.78/13.05  ----------------------
% 22.78/13.05  #Ref     : 0
% 22.78/13.05  #Sup     : 23821
% 22.78/13.05  #Fact    : 0
% 22.78/13.05  #Define  : 0
% 22.78/13.05  #Split   : 17
% 22.78/13.05  #Chain   : 0
% 22.78/13.05  #Close   : 0
% 22.78/13.05  
% 22.78/13.05  Ordering : KBO
% 22.78/13.05  
% 22.78/13.05  Simplification rules
% 22.78/13.05  ----------------------
% 22.78/13.05  #Subsume      : 3562
% 22.78/13.05  #Demod        : 9150
% 22.78/13.05  #Tautology    : 5725
% 22.78/13.05  #SimpNegUnit  : 292
% 22.78/13.05  #BackRed      : 1453
% 22.78/13.05  
% 22.78/13.05  #Partial instantiations: 2457
% 22.78/13.05  #Strategies tried      : 1
% 22.78/13.05  
% 22.78/13.05  Timing (in seconds)
% 22.78/13.05  ----------------------
% 22.78/13.05  Preprocessing        : 0.32
% 22.78/13.05  Parsing              : 0.16
% 22.78/13.05  CNF conversion       : 0.03
% 22.78/13.05  Main loop            : 11.86
% 22.78/13.05  Inferencing          : 2.17
% 22.78/13.05  Reduction            : 4.41
% 22.78/13.05  Demodulation         : 2.91
% 22.78/13.05  BG Simplification    : 0.29
% 22.78/13.05  Subsumption          : 4.07
% 22.78/13.05  Abstraction          : 0.39
% 22.78/13.05  MUC search           : 0.00
% 22.78/13.05  Cooper               : 0.00
% 22.78/13.05  Total                : 12.27
% 22.78/13.05  Index Insertion      : 0.00
% 22.78/13.05  Index Deletion       : 0.00
% 22.78/13.05  Index Matching       : 0.00
% 22.78/13.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
