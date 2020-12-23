%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:39 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :  400 (4369 expanded)
%              Number of leaves         :   30 (1314 expanded)
%              Depth                    :   16
%              Number of atoms          :  545 (8852 expanded)
%              Number of equality atoms :  254 (6619 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_12080,plain,(
    ! [A_2830,B_2831,C_2832] :
      ( r2_hidden('#skF_1'(A_2830,B_2831,C_2832),A_2830)
      | r2_hidden('#skF_2'(A_2830,B_2831,C_2832),C_2832)
      | k4_xboole_0(A_2830,B_2831) = C_2832 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_9757,plain,(
    ! [A_2732,B_2733,C_2734] :
      ( r2_hidden('#skF_5'(A_2732,B_2733,C_2734),B_2733)
      | r2_hidden('#skF_6'(A_2732,B_2733,C_2734),C_2734)
      | k2_zfmisc_1(A_2732,B_2733) = C_2734 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4602,plain,(
    ! [A_1089,B_1090,C_1091] :
      ( r2_hidden('#skF_4'(A_1089,B_1090,C_1091),A_1089)
      | r2_hidden('#skF_6'(A_1089,B_1090,C_1091),C_1091)
      | k2_zfmisc_1(A_1089,B_1090) = C_1091 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [E_47,F_48,A_15,B_16] :
      ( r2_hidden(k4_tarski(E_47,F_48),k2_zfmisc_1(A_15,B_16))
      | ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_15,B_16,D_42] :
      ( r2_hidden('#skF_7'(A_15,B_16,k2_zfmisc_1(A_15,B_16),D_42),A_15)
      | ~ r2_hidden(D_42,k2_zfmisc_1(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4144,plain,(
    ! [A_1036,B_1037,D_1038] :
      ( r2_hidden('#skF_7'(A_1036,B_1037,k2_zfmisc_1(A_1036,B_1037),D_1038),A_1036)
      | ~ r2_hidden(D_1038,k2_zfmisc_1(A_1036,B_1037)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_5'(A_15,B_16,C_17),B_16)
      | r2_hidden('#skF_6'(A_15,B_16,C_17),C_17)
      | k2_zfmisc_1(A_15,B_16) = C_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2694,plain,(
    ! [A_239,B_240,D_241] :
      ( r2_hidden('#skF_7'(A_239,B_240,k2_zfmisc_1(A_239,B_240),D_241),A_239)
      | ~ r2_hidden(D_241,k2_zfmisc_1(A_239,B_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1752,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden('#skF_5'(A_190,B_191,C_192),B_191)
      | r2_hidden('#skF_6'(A_190,B_191,C_192),C_192)
      | k2_zfmisc_1(A_190,B_191) = C_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1209,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_4'(A_144,B_145,C_146),A_144)
      | r2_hidden('#skF_6'(A_144,B_145,C_146),C_146)
      | k2_zfmisc_1(A_144,B_145) = C_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_255,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_396,plain,(
    ! [E_74,F_75,A_76,B_77] :
      ( r2_hidden(k4_tarski(E_74,F_75),k2_zfmisc_1(A_76,B_77))
      | ~ r2_hidden(F_75,B_77)
      | ~ r2_hidden(E_74,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_399,plain,(
    ! [E_74,F_75] :
      ( r2_hidden(k4_tarski(E_74,F_75),k1_xboole_0)
      | ~ r2_hidden(F_75,'#skF_12')
      | ~ r2_hidden(E_74,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_396])).

tff(c_420,plain,(
    ! [E_82,F_83] :
      ( r2_hidden(k4_tarski(E_82,F_83),k1_xboole_0)
      | ~ r2_hidden(F_83,'#skF_12')
      | ~ r2_hidden(E_82,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_396])).

tff(c_28,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_260,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_286,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_260])).

tff(c_292,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_286])).

tff(c_305,plain,(
    ! [D_63,B_64,A_65] :
      ( ~ r2_hidden(D_63,B_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_308,plain,(
    ! [D_63,A_13] :
      ( ~ r2_hidden(D_63,k1_xboole_0)
      | ~ r2_hidden(D_63,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_305])).

tff(c_424,plain,(
    ! [E_84,F_85,A_86] :
      ( ~ r2_hidden(k4_tarski(E_84,F_85),A_86)
      | ~ r2_hidden(F_85,'#skF_12')
      | ~ r2_hidden(E_84,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_420,c_308])).

tff(c_435,plain,(
    ! [F_75,E_74] :
      ( ~ r2_hidden(F_75,'#skF_12')
      | ~ r2_hidden(E_74,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_399,c_424])).

tff(c_438,plain,(
    ! [E_74] : ~ r2_hidden(E_74,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_1525,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_4'(A_157,B_158,'#skF_11'),A_157)
      | k2_zfmisc_1(A_157,B_158) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_1209,c_438])).

tff(c_1543,plain,(
    ! [B_158] : k2_zfmisc_1('#skF_11',B_158) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_1525,c_438])).

tff(c_489,plain,(
    ! [A_102,B_103,D_104] :
      ( r2_hidden('#skF_7'(A_102,B_103,k2_zfmisc_1(A_102,B_103),D_104),A_102)
      | ~ r2_hidden(D_104,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_523,plain,(
    ! [D_104] :
      ( r2_hidden('#skF_7'('#skF_11','#skF_12',k1_xboole_0,D_104),'#skF_11')
      | ~ r2_hidden(D_104,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_489])).

tff(c_532,plain,(
    ! [D_104] :
      ( r2_hidden('#skF_7'('#skF_11','#skF_12',k1_xboole_0,D_104),'#skF_11')
      | ~ r2_hidden(D_104,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_523])).

tff(c_533,plain,(
    ! [D_104] : ~ r2_hidden(D_104,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_532])).

tff(c_1380,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_4'(A_150,B_151,k1_xboole_0),A_150)
      | k2_zfmisc_1(A_150,B_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1209,c_533])).

tff(c_1418,plain,(
    ! [B_151] : k2_zfmisc_1('#skF_11',B_151) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1380,c_438])).

tff(c_1546,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_1418])).

tff(c_1548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1546])).

tff(c_1549,plain,(
    ! [F_75] : ~ r2_hidden(F_75,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_2422,plain,(
    ! [A_217,B_218] :
      ( r2_hidden('#skF_5'(A_217,B_218,'#skF_12'),B_218)
      | k2_zfmisc_1(A_217,B_218) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1752,c_1549])).

tff(c_400,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_hidden('#skF_8'(A_78,B_79,k2_zfmisc_1(A_78,B_79),D_80),B_79)
      | ~ r2_hidden(D_80,k2_zfmisc_1(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_414,plain,(
    ! [D_80] :
      ( r2_hidden('#skF_8'('#skF_11','#skF_12',k1_xboole_0,D_80),'#skF_12')
      | ~ r2_hidden(D_80,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_400])).

tff(c_418,plain,(
    ! [D_80] :
      ( r2_hidden('#skF_8'('#skF_11','#skF_12',k1_xboole_0,D_80),'#skF_12')
      | ~ r2_hidden(D_80,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_414])).

tff(c_1550,plain,(
    ! [D_80] : ~ r2_hidden(D_80,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1549,c_418])).

tff(c_2459,plain,(
    ! [A_217] : k2_zfmisc_1(A_217,k1_xboole_0) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2422,c_1550])).

tff(c_1967,plain,(
    ! [A_203,B_204] :
      ( r2_hidden('#skF_5'(A_203,B_204,k1_xboole_0),B_204)
      | k2_zfmisc_1(A_203,B_204) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1752,c_1550])).

tff(c_2049,plain,(
    ! [A_203] : k2_zfmisc_1(A_203,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1967,c_1550])).

tff(c_2463,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2049])).

tff(c_2465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2463])).

tff(c_2466,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2468,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_2466])).

tff(c_2475,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_10') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_28])).

tff(c_2474,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_2468,c_26])).

tff(c_2599,plain,(
    ! [A_226,B_227] : k5_xboole_0(A_226,k3_xboole_0(A_226,B_227)) = k4_xboole_0(A_226,B_227) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2619,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_10') = k4_xboole_0(A_13,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2474,c_2599])).

tff(c_2645,plain,(
    ! [A_231] : k4_xboole_0(A_231,'#skF_10') = A_231 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2475,c_2619])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2654,plain,(
    ! [D_10,A_231] :
      ( ~ r2_hidden(D_10,'#skF_10')
      | ~ r2_hidden(D_10,A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2645,c_8])).

tff(c_2770,plain,(
    ! [B_247,D_248,A_249] :
      ( ~ r2_hidden('#skF_7'('#skF_10',B_247,k2_zfmisc_1('#skF_10',B_247),D_248),A_249)
      | ~ r2_hidden(D_248,k2_zfmisc_1('#skF_10',B_247)) ) ),
    inference(resolution,[status(thm)],[c_2694,c_2654])).

tff(c_2781,plain,(
    ! [D_250,B_251] : ~ r2_hidden(D_250,k2_zfmisc_1('#skF_10',B_251)) ),
    inference(resolution,[status(thm)],[c_36,c_2770])).

tff(c_2796,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_2781])).

tff(c_2834,plain,(
    ! [E_255] : ~ r2_hidden(E_255,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2796])).

tff(c_3449,plain,(
    ! [A_311,B_312] :
      ( r2_hidden('#skF_5'(A_311,B_312,'#skF_10'),B_312)
      | k2_zfmisc_1(A_311,B_312) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_50,c_2834])).

tff(c_2833,plain,(
    ! [E_47] : ~ r2_hidden(E_47,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2796])).

tff(c_3531,plain,(
    ! [A_311] : k2_zfmisc_1(A_311,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_3449,c_2833])).

tff(c_62,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_254,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2469,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_254])).

tff(c_3717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3531,c_2469])).

tff(c_3718,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_2796])).

tff(c_3726,plain,(
    ! [A_318,B_319,C_320] : k2_zfmisc_1(A_318,B_319) = C_320 ),
    inference(negUnitSimplification,[status(thm)],[c_3718,c_3718,c_50])).

tff(c_3820,plain,(
    ! [C_320] : C_320 != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_3726,c_2469])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2480,plain,(
    ! [A_219] : k3_xboole_0(A_219,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_2468,c_26])).

tff(c_2498,plain,(
    ! [B_2] : k3_xboole_0('#skF_10',B_2) = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2480])).

tff(c_2501,plain,(
    ! [A_220] : k5_xboole_0(A_220,'#skF_10') = A_220 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_28])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2510,plain,(
    ! [A_220] : k5_xboole_0('#skF_10',A_220) = A_220 ),
    inference(superposition,[status(thm),theory(equality)],[c_2501,c_4])).

tff(c_2616,plain,(
    ! [B_227] : k4_xboole_0('#skF_10',B_227) = k3_xboole_0('#skF_10',B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_2510,c_2599])).

tff(c_2630,plain,(
    ! [B_227] : k4_xboole_0('#skF_10',B_227) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_2616])).

tff(c_3915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3820,c_2630])).

tff(c_3916,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2466])).

tff(c_3925,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_9') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_28])).

tff(c_3924,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_3916,c_26])).

tff(c_4049,plain,(
    ! [A_1023,B_1024] : k5_xboole_0(A_1023,k3_xboole_0(A_1023,B_1024)) = k4_xboole_0(A_1023,B_1024) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4069,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_9') = k4_xboole_0(A_13,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3924,c_4049])).

tff(c_4095,plain,(
    ! [A_1028] : k4_xboole_0(A_1028,'#skF_9') = A_1028 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3925,c_4069])).

tff(c_4104,plain,(
    ! [D_10,A_1028] :
      ( ~ r2_hidden(D_10,'#skF_9')
      | ~ r2_hidden(D_10,A_1028) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4095,c_8])).

tff(c_4220,plain,(
    ! [B_1044,D_1045,A_1046] :
      ( ~ r2_hidden('#skF_7'('#skF_9',B_1044,k2_zfmisc_1('#skF_9',B_1044),D_1045),A_1046)
      | ~ r2_hidden(D_1045,k2_zfmisc_1('#skF_9',B_1044)) ) ),
    inference(resolution,[status(thm)],[c_4144,c_4104])).

tff(c_4231,plain,(
    ! [D_1047,B_1048] : ~ r2_hidden(D_1047,k2_zfmisc_1('#skF_9',B_1048)) ),
    inference(resolution,[status(thm)],[c_36,c_4220])).

tff(c_4246,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_4231])).

tff(c_4252,plain,(
    ! [E_47] : ~ r2_hidden(E_47,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4246])).

tff(c_4894,plain,(
    ! [A_1108,B_1109] :
      ( r2_hidden('#skF_4'(A_1108,B_1109,'#skF_9'),A_1108)
      | k2_zfmisc_1(A_1108,B_1109) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_4602,c_4252])).

tff(c_4976,plain,(
    ! [B_1109] : k2_zfmisc_1('#skF_9',B_1109) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4894,c_4252])).

tff(c_3919,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_254])).

tff(c_4995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4976,c_3919])).

tff(c_4996,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_4246])).

tff(c_5008,plain,(
    ! [A_1115,B_1116] : k2_zfmisc_1(A_1115,B_1116) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_4996,c_4996,c_50])).

tff(c_5004,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(A_15,B_16) = C_17 ),
    inference(negUnitSimplification,[status(thm)],[c_4996,c_4996,c_50])).

tff(c_5190,plain,(
    ! [C_1802] : C_1802 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_5008,c_5004])).

tff(c_5247,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5190,c_3919])).

tff(c_5248,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5395,plain,(
    ! [E_2429,F_2430,A_2431,B_2432] :
      ( r2_hidden(k4_tarski(E_2429,F_2430),k2_zfmisc_1(A_2431,B_2432))
      | ~ r2_hidden(F_2430,B_2432)
      | ~ r2_hidden(E_2429,A_2431) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5401,plain,(
    ! [E_2429,F_2430] :
      ( r2_hidden(k4_tarski(E_2429,F_2430),k1_xboole_0)
      | ~ r2_hidden(F_2430,'#skF_12')
      | ~ r2_hidden(E_2429,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5248,c_5395])).

tff(c_5406,plain,(
    ! [E_2435,F_2436] :
      ( r2_hidden(k4_tarski(E_2435,F_2436),k1_xboole_0)
      | ~ r2_hidden(F_2436,'#skF_12')
      | ~ r2_hidden(E_2435,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5248,c_5395])).

tff(c_5259,plain,(
    ! [A_2415,B_2416] : k5_xboole_0(A_2415,k3_xboole_0(A_2415,B_2416)) = k4_xboole_0(A_2415,B_2416) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5285,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5259])).

tff(c_5293,plain,(
    ! [A_2420] : k4_xboole_0(A_2420,k1_xboole_0) = A_2420 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5285])).

tff(c_5299,plain,(
    ! [D_10,A_2420] :
      ( ~ r2_hidden(D_10,k1_xboole_0)
      | ~ r2_hidden(D_10,A_2420) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5293,c_8])).

tff(c_8137,plain,(
    ! [E_2620,F_2621,A_2622] :
      ( ~ r2_hidden(k4_tarski(E_2620,F_2621),A_2622)
      | ~ r2_hidden(F_2621,'#skF_12')
      | ~ r2_hidden(E_2620,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_5406,c_5299])).

tff(c_8148,plain,(
    ! [F_2430,E_2429] :
      ( ~ r2_hidden(F_2430,'#skF_12')
      | ~ r2_hidden(E_2429,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_5401,c_8137])).

tff(c_8151,plain,(
    ! [E_2429] : ~ r2_hidden(E_2429,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_8148])).

tff(c_10362,plain,(
    ! [A_2747,B_2748] :
      ( r2_hidden('#skF_5'(A_2747,B_2748,'#skF_11'),B_2748)
      | k2_zfmisc_1(A_2747,B_2748) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_9757,c_8151])).

tff(c_10384,plain,(
    ! [A_2747] : k2_zfmisc_1(A_2747,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_10362,c_8151])).

tff(c_8153,plain,(
    ! [A_2624,B_2625,D_2626] :
      ( r2_hidden('#skF_7'(A_2624,B_2625,k2_zfmisc_1(A_2624,B_2625),D_2626),A_2624)
      | ~ r2_hidden(D_2626,k2_zfmisc_1(A_2624,B_2625)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8178,plain,(
    ! [D_2626] :
      ( r2_hidden('#skF_7'('#skF_11','#skF_12',k1_xboole_0,D_2626),'#skF_11')
      | ~ r2_hidden(D_2626,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5248,c_8153])).

tff(c_8185,plain,(
    ! [D_2626] :
      ( r2_hidden('#skF_7'('#skF_11','#skF_12',k1_xboole_0,D_2626),'#skF_11')
      | ~ r2_hidden(D_2626,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5248,c_8178])).

tff(c_8186,plain,(
    ! [D_2626] : ~ r2_hidden(D_2626,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_8151,c_8185])).

tff(c_10112,plain,(
    ! [A_2739,B_2740] :
      ( r2_hidden('#skF_5'(A_2739,B_2740,k1_xboole_0),B_2740)
      | k2_zfmisc_1(A_2739,B_2740) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9757,c_8186])).

tff(c_10174,plain,(
    ! [A_2739] : k2_zfmisc_1(A_2739,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10112,c_8151])).

tff(c_10388,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10384,c_10174])).

tff(c_10390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_10388])).

tff(c_10391,plain,(
    ! [F_2430] : ~ r2_hidden(F_2430,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_8148])).

tff(c_12126,plain,(
    ! [B_2833,C_2834] :
      ( r2_hidden('#skF_2'('#skF_12',B_2833,C_2834),C_2834)
      | k4_xboole_0('#skF_12',B_2833) = C_2834 ) ),
    inference(resolution,[status(thm)],[c_12080,c_10391])).

tff(c_170,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,A_55) = k3_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_186,plain,(
    ! [A_55] : k3_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_26])).

tff(c_83,plain,(
    ! [B_51,A_52] : k5_xboole_0(B_51,A_52) = k5_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_52] : k5_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_28])).

tff(c_5282,plain,(
    ! [B_2416] : k4_xboole_0(k1_xboole_0,B_2416) = k3_xboole_0(k1_xboole_0,B_2416) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_5259])).

tff(c_5290,plain,(
    ! [B_2416] : k4_xboole_0(k1_xboole_0,B_2416) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_5282])).

tff(c_7774,plain,(
    ! [A_2611,B_2612,C_2613] :
      ( r2_hidden('#skF_1'(A_2611,B_2612,C_2613),A_2611)
      | r2_hidden('#skF_2'(A_2611,B_2612,C_2613),C_2613)
      | k4_xboole_0(A_2611,B_2612) = C_2613 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5249,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5398,plain,(
    ! [E_2429,F_2430] :
      ( r2_hidden(k4_tarski(E_2429,F_2430),k1_xboole_0)
      | ~ r2_hidden(F_2430,'#skF_10')
      | ~ r2_hidden(E_2429,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5249,c_5395])).

tff(c_5402,plain,(
    ! [E_2433,F_2434] :
      ( r2_hidden(k4_tarski(E_2433,F_2434),k1_xboole_0)
      | ~ r2_hidden(F_2434,'#skF_10')
      | ~ r2_hidden(E_2433,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5249,c_5395])).

tff(c_5410,plain,(
    ! [E_2437,F_2438,A_2439] :
      ( ~ r2_hidden(k4_tarski(E_2437,F_2438),A_2439)
      | ~ r2_hidden(F_2438,'#skF_10')
      | ~ r2_hidden(E_2437,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5402,c_5299])).

tff(c_5425,plain,(
    ! [F_2430,E_2429] :
      ( ~ r2_hidden(F_2430,'#skF_10')
      | ~ r2_hidden(E_2429,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5398,c_5410])).

tff(c_5428,plain,(
    ! [E_2429] : ~ r2_hidden(E_2429,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5425])).

tff(c_7409,plain,(
    ! [A_2556,B_2557,D_2558] :
      ( r2_hidden('#skF_7'(A_2556,B_2557,k2_zfmisc_1(A_2556,B_2557),D_2558),A_2556)
      | ~ r2_hidden(D_2558,k2_zfmisc_1(A_2556,B_2557)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7431,plain,(
    ! [D_2558] :
      ( r2_hidden('#skF_7'('#skF_9','#skF_10',k1_xboole_0,D_2558),'#skF_9')
      | ~ r2_hidden(D_2558,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5249,c_7409])).

tff(c_7440,plain,(
    ! [D_2558] :
      ( r2_hidden('#skF_7'('#skF_9','#skF_10',k1_xboole_0,D_2558),'#skF_9')
      | ~ r2_hidden(D_2558,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5249,c_7431])).

tff(c_7441,plain,(
    ! [D_2558] : ~ r2_hidden(D_2558,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_5428,c_7440])).

tff(c_7850,plain,(
    ! [B_2612,C_2613] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2612,C_2613),C_2613)
      | k4_xboole_0(k1_xboole_0,B_2612) = C_2613 ) ),
    inference(resolution,[status(thm)],[c_7774,c_7441])).

tff(c_8018,plain,(
    ! [B_2617,C_2618] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2617,C_2618),C_2618)
      | k1_xboole_0 = C_2618 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_7850])).

tff(c_7330,plain,(
    ! [A_2550,B_2551,C_2552] :
      ( r2_hidden('#skF_1'(A_2550,B_2551,C_2552),A_2550)
      | r2_hidden('#skF_2'(A_2550,B_2551,C_2552),C_2552)
      | k4_xboole_0(A_2550,B_2551) = C_2552 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5558,plain,(
    ! [A_2473,B_2474,D_2475] :
      ( r2_hidden('#skF_7'(A_2473,B_2474,k2_zfmisc_1(A_2473,B_2474),D_2475),A_2473)
      | ~ r2_hidden(D_2475,k2_zfmisc_1(A_2473,B_2474)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5608,plain,(
    ! [D_2475] :
      ( r2_hidden('#skF_7'('#skF_9','#skF_10',k1_xboole_0,D_2475),'#skF_9')
      | ~ r2_hidden(D_2475,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5249,c_5558])).

tff(c_5624,plain,(
    ! [D_2475] :
      ( r2_hidden('#skF_7'('#skF_9','#skF_10',k1_xboole_0,D_2475),'#skF_9')
      | ~ r2_hidden(D_2475,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5249,c_5608])).

tff(c_5625,plain,(
    ! [D_2475] : ~ r2_hidden(D_2475,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_5428,c_5624])).

tff(c_7338,plain,(
    ! [B_2551,C_2552] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2551,C_2552),C_2552)
      | k4_xboole_0(k1_xboole_0,B_2551) = C_2552 ) ),
    inference(resolution,[status(thm)],[c_7330,c_5625])).

tff(c_7380,plain,(
    ! [B_2553,C_2554] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_2553,C_2554),C_2554)
      | k1_xboole_0 = C_2554 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_7338])).

tff(c_5430,plain,(
    ! [E_2441,F_2442,A_2443] :
      ( ~ r2_hidden(k4_tarski(E_2441,F_2442),A_2443)
      | ~ r2_hidden(F_2442,'#skF_12')
      | ~ r2_hidden(E_2441,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_5406,c_5299])).

tff(c_5441,plain,(
    ! [F_2430,E_2429] :
      ( ~ r2_hidden(F_2430,'#skF_12')
      | ~ r2_hidden(E_2429,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_5401,c_5430])).

tff(c_5444,plain,(
    ! [E_2429] : ~ r2_hidden(E_2429,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_5441])).

tff(c_7388,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_7380,c_5444])).

tff(c_7406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_7388])).

tff(c_7407,plain,(
    ! [F_2430] : ~ r2_hidden(F_2430,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_5441])).

tff(c_8098,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8018,c_7407])).

tff(c_8134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_8098])).

tff(c_8135,plain,(
    ! [F_2430] : ~ r2_hidden(F_2430,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_5425])).

tff(c_10505,plain,(
    ! [A_2778,B_2779,D_2780] :
      ( r2_hidden('#skF_8'(A_2778,B_2779,k2_zfmisc_1(A_2778,B_2779),D_2780),B_2779)
      | ~ r2_hidden(D_2780,k2_zfmisc_1(A_2778,B_2779)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10555,plain,(
    ! [D_2780] :
      ( r2_hidden('#skF_8'('#skF_9','#skF_10',k1_xboole_0,D_2780),'#skF_10')
      | ~ r2_hidden(D_2780,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5249,c_10505])).

tff(c_10571,plain,(
    ! [D_2780] :
      ( r2_hidden('#skF_8'('#skF_9','#skF_10',k1_xboole_0,D_2780),'#skF_10')
      | ~ r2_hidden(D_2780,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5249,c_10555])).

tff(c_10572,plain,(
    ! [D_2780] : ~ r2_hidden(D_2780,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_8135,c_10571])).

tff(c_12153,plain,(
    ! [B_2835] : k4_xboole_0('#skF_12',B_2835) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12126,c_10572])).

tff(c_5291,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5285])).

tff(c_12162,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_12153,c_5291])).

tff(c_12178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_12162])).

tff(c_12180,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12181,plain,(
    '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12180,c_81])).

tff(c_13280,plain,(
    ! [B_4462,A_4463] : k3_xboole_0(B_4462,A_4463) = k3_xboole_0(A_4463,B_4462) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12182,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12180,c_12180,c_26])).

tff(c_13296,plain,(
    ! [A_4463] : k3_xboole_0('#skF_12',A_4463) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_13280,c_12182])).

tff(c_13365,plain,(
    ! [B_4465,A_4466] : k5_xboole_0(B_4465,A_4466) = k5_xboole_0(A_4466,B_4465) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12183,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_12') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12180,c_28])).

tff(c_13435,plain,(
    ! [A_4469] : k5_xboole_0('#skF_12',A_4469) = A_4469 ),
    inference(superposition,[status(thm),theory(equality)],[c_13365,c_12183])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13442,plain,(
    ! [B_12] : k4_xboole_0('#skF_12',B_12) = k3_xboole_0('#skF_12',B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_13435,c_24])).

tff(c_13473,plain,(
    ! [B_12] : k4_xboole_0('#skF_12',B_12) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13296,c_13442])).

tff(c_14600,plain,(
    ! [A_4570,B_4571,C_4572] :
      ( r2_hidden('#skF_1'(A_4570,B_4571,C_4572),A_4570)
      | r2_hidden('#skF_2'(A_4570,B_4571,C_4572),C_4572)
      | k4_xboole_0(A_4570,B_4571) = C_4572 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13593,plain,(
    ! [A_4489,B_4490,D_4491] :
      ( r2_hidden('#skF_7'(A_4489,B_4490,k2_zfmisc_1(A_4489,B_4490),D_4491),A_4489)
      | ~ r2_hidden(D_4491,k2_zfmisc_1(A_4489,B_4490)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13412,plain,(
    ! [A_4467,B_4468] : k5_xboole_0(A_4467,k3_xboole_0(A_4467,B_4468)) = k4_xboole_0(A_4467,B_4468) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13430,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_12') = k4_xboole_0(A_13,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_12182,c_13412])).

tff(c_13434,plain,(
    ! [A_13] : k4_xboole_0(A_13,'#skF_12') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12183,c_13430])).

tff(c_13523,plain,(
    ! [D_4475,B_4476,A_4477] :
      ( ~ r2_hidden(D_4475,B_4476)
      | ~ r2_hidden(D_4475,k4_xboole_0(A_4477,B_4476)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13529,plain,(
    ! [D_4475,A_13] :
      ( ~ r2_hidden(D_4475,'#skF_12')
      | ~ r2_hidden(D_4475,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13434,c_13523])).

tff(c_13623,plain,(
    ! [B_4495,D_4496,A_4497] :
      ( ~ r2_hidden('#skF_7'('#skF_12',B_4495,k2_zfmisc_1('#skF_12',B_4495),D_4496),A_4497)
      | ~ r2_hidden(D_4496,k2_zfmisc_1('#skF_12',B_4495)) ) ),
    inference(resolution,[status(thm)],[c_13593,c_13529])).

tff(c_13634,plain,(
    ! [D_4498,B_4499] : ~ r2_hidden(D_4498,k2_zfmisc_1('#skF_12',B_4499)) ),
    inference(resolution,[status(thm)],[c_36,c_13623])).

tff(c_13649,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_30,c_13634])).

tff(c_13650,plain,(
    ! [E_47] : ~ r2_hidden(E_47,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_13649])).

tff(c_14619,plain,(
    ! [B_4571,C_4572] :
      ( r2_hidden('#skF_2'('#skF_12',B_4571,C_4572),C_4572)
      | k4_xboole_0('#skF_12',B_4571) = C_4572 ) ),
    inference(resolution,[status(thm)],[c_14600,c_13650])).

tff(c_14668,plain,(
    ! [B_4573,C_4574] :
      ( r2_hidden('#skF_2'('#skF_12',B_4573,C_4574),C_4574)
      | C_4574 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13473,c_14619])).

tff(c_13632,plain,(
    ! [D_42,B_16] : ~ r2_hidden(D_42,k2_zfmisc_1('#skF_12',B_16)) ),
    inference(resolution,[status(thm)],[c_36,c_13623])).

tff(c_14697,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_12',B_16) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_14668,c_13632])).

tff(c_12299,plain,(
    ! [B_2841,A_2842] : k3_xboole_0(B_2841,A_2842) = k3_xboole_0(A_2842,B_2841) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12315,plain,(
    ! [A_2842] : k3_xboole_0('#skF_12',A_2842) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_12299,c_12182])).

tff(c_12210,plain,(
    ! [B_2838,A_2839] : k5_xboole_0(B_2838,A_2839) = k5_xboole_0(A_2839,B_2838) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12226,plain,(
    ! [A_2839] : k5_xboole_0('#skF_12',A_2839) = A_2839 ),
    inference(superposition,[status(thm),theory(equality)],[c_12210,c_12183])).

tff(c_12379,plain,(
    ! [A_2844,B_2845] : k5_xboole_0(A_2844,k3_xboole_0(A_2844,B_2845)) = k4_xboole_0(A_2844,B_2845) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12402,plain,(
    ! [B_2845] : k4_xboole_0('#skF_12',B_2845) = k3_xboole_0('#skF_12',B_2845) ),
    inference(superposition,[status(thm),theory(equality)],[c_12226,c_12379])).

tff(c_12410,plain,(
    ! [B_2845] : k4_xboole_0('#skF_12',B_2845) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12315,c_12402])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12522,plain,(
    ! [A_2865,B_2866,D_2867] :
      ( r2_hidden('#skF_7'(A_2865,B_2866,k2_zfmisc_1(A_2865,B_2866),D_2867),A_2865)
      | ~ r2_hidden(D_2867,k2_zfmisc_1(A_2865,B_2866)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12405,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_12') = k4_xboole_0(A_13,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_12182,c_12379])).

tff(c_12411,plain,(
    ! [A_13] : k4_xboole_0(A_13,'#skF_12') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12183,c_12405])).

tff(c_12451,plain,(
    ! [D_2851,B_2852,A_2853] :
      ( ~ r2_hidden(D_2851,B_2852)
      | ~ r2_hidden(D_2851,k4_xboole_0(A_2853,B_2852)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12457,plain,(
    ! [D_2851,A_13] :
      ( ~ r2_hidden(D_2851,'#skF_12')
      | ~ r2_hidden(D_2851,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12411,c_12451])).

tff(c_12578,plain,(
    ! [B_2874,D_2875,A_2876] :
      ( ~ r2_hidden('#skF_7'('#skF_12',B_2874,k2_zfmisc_1('#skF_12',B_2874),D_2875),A_2876)
      | ~ r2_hidden(D_2875,k2_zfmisc_1('#skF_12',B_2874)) ) ),
    inference(resolution,[status(thm)],[c_12522,c_12457])).

tff(c_12589,plain,(
    ! [D_2877,B_2878] : ~ r2_hidden(D_2877,k2_zfmisc_1('#skF_12',B_2878)) ),
    inference(resolution,[status(thm)],[c_36,c_12578])).

tff(c_12614,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_30,c_12589])).

tff(c_12653,plain,(
    ! [E_2882] : ~ r2_hidden(E_2882,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_12614])).

tff(c_12657,plain,(
    ! [B_6,C_7] :
      ( r2_hidden('#skF_2'('#skF_12',B_6,C_7),C_7)
      | k4_xboole_0('#skF_12',B_6) = C_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_12653])).

tff(c_12905,plain,(
    ! [B_2900,C_2901] :
      ( r2_hidden('#skF_2'('#skF_12',B_2900,C_2901),C_2901)
      | C_2901 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12410,c_12657])).

tff(c_34,plain,(
    ! [A_15,B_16,D_42] :
      ( r2_hidden('#skF_8'(A_15,B_16,k2_zfmisc_1(A_15,B_16),D_42),B_16)
      | ~ r2_hidden(D_42,k2_zfmisc_1(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12677,plain,(
    ! [D_42,A_15] : ~ r2_hidden(D_42,k2_zfmisc_1(A_15,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_34,c_12653])).

tff(c_12946,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_12905,c_12677])).

tff(c_12179,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12188,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12180,c_12180,c_12179])).

tff(c_12189,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_12188])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12295,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12180,c_12189,c_12180,c_54])).

tff(c_12957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12946,c_12295])).

tff(c_12958,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_12614])).

tff(c_13039,plain,(
    ! [A_2907,B_2908] : k4_xboole_0(A_2907,B_2908) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_12958,c_12958,c_22])).

tff(c_12996,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(A_5,B_6) = C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_12958,c_12958,c_22])).

tff(c_13214,plain,(
    ! [C_3883] : C_3883 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_13039,c_12996])).

tff(c_13229,plain,(
    '#skF_11' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_13214,c_12315])).

tff(c_13257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12181,c_13229])).

tff(c_13258,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_12188])).

tff(c_13328,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12180,c_13258,c_12180,c_54])).

tff(c_14709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14697,c_13328])).

tff(c_14710,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_13649])).

tff(c_14730,plain,(
    ! [A_4577,B_4578] : k2_zfmisc_1(A_4577,B_4578) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_14710,c_14710,c_50])).

tff(c_14718,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(A_15,B_16) = C_17 ),
    inference(negUnitSimplification,[status(thm)],[c_14710,c_14710,c_50])).

tff(c_14900,plain,(
    ! [C_5228] : C_5228 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_14730,c_14718])).

tff(c_14917,plain,(
    '#skF_11' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_14900,c_13473])).

tff(c_14955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12181,c_14917])).

tff(c_14957,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_15066,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14957,c_14957,c_14957,c_60])).

tff(c_15067,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_15066])).

tff(c_14958,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14957,c_14957,c_26])).

tff(c_14983,plain,(
    ! [B_5951,A_5952] : k3_xboole_0(B_5951,A_5952) = k3_xboole_0(A_5952,B_5951) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_15021,plain,(
    ! [A_13] : k3_xboole_0('#skF_11',A_13) = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_14958,c_14983])).

tff(c_15113,plain,(
    ! [A_13] : k3_xboole_0('#skF_9',A_13) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15067,c_15067,c_15021])).

tff(c_14959,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_11') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14957,c_28])).

tff(c_15071,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_9') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15067,c_14959])).

tff(c_15148,plain,(
    ! [B_5957,A_5958] : k5_xboole_0(B_5957,A_5958) = k5_xboole_0(A_5958,B_5957) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15186,plain,(
    ! [A_14] : k5_xboole_0('#skF_9',A_14) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_15071,c_15148])).

tff(c_15242,plain,(
    ! [A_5963,B_5964] : k5_xboole_0(A_5963,k3_xboole_0(A_5963,B_5964)) = k4_xboole_0(A_5963,B_5964) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15256,plain,(
    ! [B_5964] : k4_xboole_0('#skF_9',B_5964) = k3_xboole_0('#skF_9',B_5964) ),
    inference(superposition,[status(thm),theory(equality)],[c_15186,c_15242])).

tff(c_15272,plain,(
    ! [B_5964] : k4_xboole_0('#skF_9',B_5964) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15113,c_15256])).

tff(c_15564,plain,(
    ! [A_6004,B_6005,C_6006] :
      ( r2_hidden('#skF_1'(A_6004,B_6005,C_6006),A_6004)
      | r2_hidden('#skF_2'(A_6004,B_6005,C_6006),C_6006)
      | k4_xboole_0(A_6004,B_6005) = C_6006 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15379,plain,(
    ! [A_5981,B_5982,D_5983] :
      ( r2_hidden('#skF_7'(A_5981,B_5982,k2_zfmisc_1(A_5981,B_5982),D_5983),A_5981)
      | ~ r2_hidden(D_5983,k2_zfmisc_1(A_5981,B_5982)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_15070,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15067,c_15067,c_14958])).

tff(c_15262,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_9') = k4_xboole_0(A_13,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_15070,c_15242])).

tff(c_15275,plain,(
    ! [A_5965] : k4_xboole_0(A_5965,'#skF_9') = A_5965 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15071,c_15262])).

tff(c_15281,plain,(
    ! [D_10,A_5965] :
      ( ~ r2_hidden(D_10,'#skF_9')
      | ~ r2_hidden(D_10,A_5965) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15275,c_8])).

tff(c_15409,plain,(
    ! [B_5987,D_5988,A_5989] :
      ( ~ r2_hidden('#skF_7'('#skF_9',B_5987,k2_zfmisc_1('#skF_9',B_5987),D_5988),A_5989)
      | ~ r2_hidden(D_5988,k2_zfmisc_1('#skF_9',B_5987)) ) ),
    inference(resolution,[status(thm)],[c_15379,c_15281])).

tff(c_15420,plain,(
    ! [D_5990,B_5991] : ~ r2_hidden(D_5990,k2_zfmisc_1('#skF_9',B_5991)) ),
    inference(resolution,[status(thm)],[c_36,c_15409])).

tff(c_15435,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_15420])).

tff(c_15436,plain,(
    ! [E_47] : ~ r2_hidden(E_47,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_15435])).

tff(c_15580,plain,(
    ! [B_6005,C_6006] :
      ( r2_hidden('#skF_2'('#skF_9',B_6005,C_6006),C_6006)
      | k4_xboole_0('#skF_9',B_6005) = C_6006 ) ),
    inference(resolution,[status(thm)],[c_15564,c_15436])).

tff(c_15705,plain,(
    ! [B_6013,C_6014] :
      ( r2_hidden('#skF_2'('#skF_9',B_6013,C_6014),C_6014)
      | C_6014 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15272,c_15580])).

tff(c_15418,plain,(
    ! [D_42,B_16] : ~ r2_hidden(D_42,k2_zfmisc_1('#skF_9',B_16)) ),
    inference(resolution,[status(thm)],[c_36,c_15409])).

tff(c_15749,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_9',B_16) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_15705,c_15418])).

tff(c_14956,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_14964,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14957,c_14956])).

tff(c_15072,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15067,c_14964])).

tff(c_15794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15749,c_15072])).

tff(c_15795,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_15435])).

tff(c_15839,plain,(
    ! [A_6021,B_6022,C_6023] : k2_zfmisc_1(A_6021,B_6022) = C_6023 ),
    inference(negUnitSimplification,[status(thm)],[c_15795,c_15795,c_50])).

tff(c_15941,plain,(
    ! [C_6023] : C_6023 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_15839,c_15072])).

tff(c_16077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15941,c_15272])).

tff(c_16078,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_15066])).

tff(c_14981,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9'
    | '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14957,c_14957,c_14957,c_56])).

tff(c_14982,plain,(
    '#skF_11' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_14981])).

tff(c_16081,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16078,c_14982])).

tff(c_16083,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_10') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16078,c_14959])).

tff(c_14999,plain,(
    ! [A_5952] : k3_xboole_0('#skF_11',A_5952) = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_14983,c_14958])).

tff(c_16080,plain,(
    ! [A_5952] : k3_xboole_0('#skF_10',A_5952) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16078,c_16078,c_14999])).

tff(c_16211,plain,(
    ! [A_7290,B_7291] : k5_xboole_0(A_7290,k3_xboole_0(A_7290,B_7291)) = k4_xboole_0(A_7290,B_7291) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16220,plain,(
    ! [A_5952] : k5_xboole_0('#skF_10','#skF_10') = k4_xboole_0('#skF_10',A_5952) ),
    inference(superposition,[status(thm),theory(equality)],[c_16080,c_16211])).

tff(c_16232,plain,(
    ! [A_5952] : k4_xboole_0('#skF_10',A_5952) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16083,c_16220])).

tff(c_16392,plain,(
    ! [A_7312,B_7313,D_7314] :
      ( r2_hidden('#skF_7'(A_7312,B_7313,k2_zfmisc_1(A_7312,B_7313),D_7314),A_7312)
      | ~ r2_hidden(D_7314,k2_zfmisc_1(A_7312,B_7313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16082,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16078,c_16078,c_14958])).

tff(c_16223,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_10') = k4_xboole_0(A_13,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_16082,c_16211])).

tff(c_16233,plain,(
    ! [A_13] : k4_xboole_0(A_13,'#skF_10') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16083,c_16223])).

tff(c_16320,plain,(
    ! [D_7298,B_7299,A_7300] :
      ( ~ r2_hidden(D_7298,B_7299)
      | ~ r2_hidden(D_7298,k4_xboole_0(A_7300,B_7299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16326,plain,(
    ! [D_7298,A_13] :
      ( ~ r2_hidden(D_7298,'#skF_10')
      | ~ r2_hidden(D_7298,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16233,c_16320])).

tff(c_16422,plain,(
    ! [B_7318,D_7319,A_7320] :
      ( ~ r2_hidden('#skF_7'('#skF_10',B_7318,k2_zfmisc_1('#skF_10',B_7318),D_7319),A_7320)
      | ~ r2_hidden(D_7319,k2_zfmisc_1('#skF_10',B_7318)) ) ),
    inference(resolution,[status(thm)],[c_16392,c_16326])).

tff(c_16433,plain,(
    ! [D_7321,B_7322] : ~ r2_hidden(D_7321,k2_zfmisc_1('#skF_10',B_7322)) ),
    inference(resolution,[status(thm)],[c_36,c_16422])).

tff(c_16448,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_16433])).

tff(c_16487,plain,(
    ! [E_7326] : ~ r2_hidden(E_7326,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_16448])).

tff(c_16491,plain,(
    ! [B_6,C_7] :
      ( r2_hidden('#skF_2'('#skF_10',B_6,C_7),C_7)
      | k4_xboole_0('#skF_10',B_6) = C_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_16487])).

tff(c_16647,plain,(
    ! [B_7344,C_7345] :
      ( r2_hidden('#skF_2'('#skF_10',B_7344,C_7345),C_7345)
      | C_7345 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16232,c_16491])).

tff(c_16504,plain,(
    ! [D_42,A_15] : ~ r2_hidden(D_42,k2_zfmisc_1(A_15,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_34,c_16487])).

tff(c_16688,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_16647,c_16504])).

tff(c_16084,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16078,c_14964])).

tff(c_16699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16688,c_16084])).

tff(c_16700,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_16448])).

tff(c_16768,plain,(
    ! [A_7351,B_7352] : k4_xboole_0(A_7351,B_7352) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_16700,c_16700,c_22])).

tff(c_16738,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(A_5,B_6) = C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_16700,c_16700,c_22])).

tff(c_16910,plain,(
    ! [C_7858] : C_7858 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_16768,c_16738])).

tff(c_16924,plain,(
    '#skF_10' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_16910,c_16080])).

tff(c_16952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16081,c_16924])).

tff(c_16954,plain,(
    '#skF_11' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_14981])).

tff(c_16956,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_12') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16954,c_14959])).

tff(c_17079,plain,(
    ! [B_8440,A_8441] : k3_xboole_0(B_8440,A_8441) = k3_xboole_0(A_8441,B_8440) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16955,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16954,c_16954,c_14958])).

tff(c_17095,plain,(
    ! [A_8441] : k3_xboole_0('#skF_12',A_8441) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_17079,c_16955])).

tff(c_17167,plain,(
    ! [A_8449,B_8450] : k5_xboole_0(A_8449,k3_xboole_0(A_8449,B_8450)) = k4_xboole_0(A_8449,B_8450) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17180,plain,(
    ! [A_8441] : k5_xboole_0('#skF_12','#skF_12') = k4_xboole_0('#skF_12',A_8441) ),
    inference(superposition,[status(thm),theory(equality)],[c_17095,c_17167])).

tff(c_17197,plain,(
    ! [A_8441] : k4_xboole_0('#skF_12',A_8441) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16956,c_17180])).

tff(c_17304,plain,(
    ! [A_8464,B_8465,D_8466] :
      ( r2_hidden('#skF_7'(A_8464,B_8465,k2_zfmisc_1(A_8464,B_8465),D_8466),A_8464)
      | ~ r2_hidden(D_8466,k2_zfmisc_1(A_8464,B_8465)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_17193,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_12') = k4_xboole_0(A_13,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_16955,c_17167])).

tff(c_17200,plain,(
    ! [A_8451] : k4_xboole_0(A_8451,'#skF_12') = A_8451 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16956,c_17193])).

tff(c_17209,plain,(
    ! [D_10,A_8451] :
      ( ~ r2_hidden(D_10,'#skF_12')
      | ~ r2_hidden(D_10,A_8451) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17200,c_8])).

tff(c_17361,plain,(
    ! [B_8473,D_8474,A_8475] :
      ( ~ r2_hidden('#skF_7'('#skF_12',B_8473,k2_zfmisc_1('#skF_12',B_8473),D_8474),A_8475)
      | ~ r2_hidden(D_8474,k2_zfmisc_1('#skF_12',B_8473)) ) ),
    inference(resolution,[status(thm)],[c_17304,c_17209])).

tff(c_17372,plain,(
    ! [D_8476,B_8477] : ~ r2_hidden(D_8476,k2_zfmisc_1('#skF_12',B_8477)) ),
    inference(resolution,[status(thm)],[c_36,c_17361])).

tff(c_17397,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_30,c_17372])).

tff(c_17399,plain,(
    ! [E_8478] : ~ r2_hidden(E_8478,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_17397])).

tff(c_17403,plain,(
    ! [B_6,C_7] :
      ( r2_hidden('#skF_2'('#skF_12',B_6,C_7),C_7)
      | k4_xboole_0('#skF_12',B_6) = C_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_17399])).

tff(c_17605,plain,(
    ! [B_8499,C_8500] :
      ( r2_hidden('#skF_2'('#skF_12',B_8499,C_8500),C_8500)
      | C_8500 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17197,c_17403])).

tff(c_17416,plain,(
    ! [D_42,A_15] : ~ r2_hidden(D_42,k2_zfmisc_1(A_15,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_34,c_17399])).

tff(c_17646,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_17605,c_17416])).

tff(c_16953,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_14981])).

tff(c_16967,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16954,c_16954,c_16953])).

tff(c_16968,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_16967])).

tff(c_16957,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16954,c_14964])).

tff(c_16991,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16968,c_16957])).

tff(c_17657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17646,c_16991])).

tff(c_17658,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_17397])).

tff(c_17807,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,B_6) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_17658,c_17658,c_22])).

tff(c_17666,plain,(
    ! [A_8503,B_8504,C_8505] : k4_xboole_0(A_8503,B_8504) = C_8505 ),
    inference(negUnitSimplification,[status(thm)],[c_17658,c_17658,c_22])).

tff(c_17912,plain,(
    ! [C_10200] : C_10200 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_17807,c_17666])).

tff(c_17815,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,B_6) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_17658,c_17658,c_22])).

tff(c_17866,plain,(
    ! [C_9515] : C_9515 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_17815,c_17666])).

tff(c_17891,plain,(
    '#skF_11' != '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_17866,c_16991])).

tff(c_17939,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_17912,c_17891])).

tff(c_17941,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_16967])).

tff(c_18057,plain,(
    ! [B_10746,A_10747] : k3_xboole_0(B_10746,A_10747) = k3_xboole_0(A_10747,B_10746) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18131,plain,(
    ! [A_10750] : k3_xboole_0('#skF_12',A_10750) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_18057,c_16955])).

tff(c_18136,plain,(
    ! [A_10750] : k5_xboole_0('#skF_12','#skF_12') = k4_xboole_0('#skF_12',A_10750) ),
    inference(superposition,[status(thm),theory(equality)],[c_18131,c_24])).

tff(c_18160,plain,(
    ! [A_10750] : k4_xboole_0('#skF_12',A_10750) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16956,c_18136])).

tff(c_18499,plain,(
    ! [A_10799,B_10800,C_10801] :
      ( r2_hidden('#skF_1'(A_10799,B_10800,C_10801),A_10799)
      | r2_hidden('#skF_2'(A_10799,B_10800,C_10801),C_10801)
      | k4_xboole_0(A_10799,B_10800) = C_10801 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18277,plain,(
    ! [A_10770,B_10771,D_10772] :
      ( r2_hidden('#skF_7'(A_10770,B_10771,k2_zfmisc_1(A_10770,B_10771),D_10772),A_10770)
      | ~ r2_hidden(D_10772,k2_zfmisc_1(A_10770,B_10771)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18104,plain,(
    ! [A_10748,B_10749] : k5_xboole_0(A_10748,k3_xboole_0(A_10748,B_10749)) = k4_xboole_0(A_10748,B_10749) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18127,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_12') = k4_xboole_0(A_13,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_16955,c_18104])).

tff(c_18130,plain,(
    ! [A_13] : k4_xboole_0(A_13,'#skF_12') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16956,c_18127])).

tff(c_18200,plain,(
    ! [D_10753,B_10754,A_10755] :
      ( ~ r2_hidden(D_10753,B_10754)
      | ~ r2_hidden(D_10753,k4_xboole_0(A_10755,B_10754)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18206,plain,(
    ! [D_10753,A_13] :
      ( ~ r2_hidden(D_10753,'#skF_12')
      | ~ r2_hidden(D_10753,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18130,c_18200])).

tff(c_18333,plain,(
    ! [B_10779,D_10780,A_10781] :
      ( ~ r2_hidden('#skF_7'('#skF_12',B_10779,k2_zfmisc_1('#skF_12',B_10779),D_10780),A_10781)
      | ~ r2_hidden(D_10780,k2_zfmisc_1('#skF_12',B_10779)) ) ),
    inference(resolution,[status(thm)],[c_18277,c_18206])).

tff(c_18344,plain,(
    ! [D_10782,B_10783] : ~ r2_hidden(D_10782,k2_zfmisc_1('#skF_12',B_10783)) ),
    inference(resolution,[status(thm)],[c_36,c_18333])).

tff(c_18369,plain,(
    ! [F_48,B_16,E_47] :
      ( ~ r2_hidden(F_48,B_16)
      | ~ r2_hidden(E_47,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_30,c_18344])).

tff(c_18370,plain,(
    ! [E_47] : ~ r2_hidden(E_47,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_18369])).

tff(c_18519,plain,(
    ! [B_10800,C_10801] :
      ( r2_hidden('#skF_2'('#skF_12',B_10800,C_10801),C_10801)
      | k4_xboole_0('#skF_12',B_10800) = C_10801 ) ),
    inference(resolution,[status(thm)],[c_18499,c_18370])).

tff(c_18619,plain,(
    ! [B_10805,C_10806] :
      ( r2_hidden('#skF_2'('#skF_12',B_10805,C_10806),C_10806)
      | C_10806 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18160,c_18519])).

tff(c_18342,plain,(
    ! [D_42,B_16] : ~ r2_hidden(D_42,k2_zfmisc_1('#skF_12',B_16)) ),
    inference(resolution,[status(thm)],[c_36,c_18333])).

tff(c_18663,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_12',B_16) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_18619,c_18342])).

tff(c_17940,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_16967])).

tff(c_17962,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17940,c_16957])).

tff(c_18717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18663,c_17962])).

tff(c_18718,plain,(
    ! [F_48,B_16] : ~ r2_hidden(F_48,B_16) ),
    inference(splitRight,[status(thm)],[c_18369])).

tff(c_52,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden('#skF_4'(A_15,B_16,C_17),A_15)
      | r2_hidden('#skF_6'(A_15,B_16,C_17),C_17)
      | k2_zfmisc_1(A_15,B_16) = C_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18737,plain,(
    ! [A_10813,B_10814] : k2_zfmisc_1(A_10813,B_10814) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_18718,c_18718,c_52])).

tff(c_18719,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(A_15,B_16) = C_17 ),
    inference(negUnitSimplification,[status(thm)],[c_18718,c_18718,c_52])).

tff(c_18907,plain,(
    ! [C_11464] : C_11464 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_18737,c_18719])).

tff(c_18921,plain,(
    '#skF_10' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_18907,c_18160])).

tff(c_18959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17941,c_18921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.64/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.74  
% 8.22/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.74  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 8.22/2.74  
% 8.22/2.74  %Foreground sorts:
% 8.22/2.74  
% 8.22/2.74  
% 8.22/2.74  %Background operators:
% 8.22/2.74  
% 8.22/2.74  
% 8.22/2.74  %Foreground operators:
% 8.22/2.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.22/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.22/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.22/2.74  tff('#skF_11', type, '#skF_11': $i).
% 8.22/2.74  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.22/2.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.22/2.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.22/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.22/2.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.22/2.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.22/2.74  tff('#skF_10', type, '#skF_10': $i).
% 8.22/2.74  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 8.22/2.74  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.22/2.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.22/2.74  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 8.22/2.74  tff('#skF_9', type, '#skF_9': $i).
% 8.22/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.22/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.22/2.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.22/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.22/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.22/2.74  tff('#skF_12', type, '#skF_12': $i).
% 8.22/2.74  
% 8.22/2.79  tff(f_64, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.22/2.79  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.22/2.79  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.22/2.79  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.22/2.79  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.22/2.79  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.22/2.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.22/2.79  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.22/2.79  tff(c_56, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/2.79  tff(c_82, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_56])).
% 8.22/2.79  tff(c_12080, plain, (![A_2830, B_2831, C_2832]: (r2_hidden('#skF_1'(A_2830, B_2831, C_2832), A_2830) | r2_hidden('#skF_2'(A_2830, B_2831, C_2832), C_2832) | k4_xboole_0(A_2830, B_2831)=C_2832)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_58, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/2.79  tff(c_81, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_58])).
% 8.22/2.79  tff(c_9757, plain, (![A_2732, B_2733, C_2734]: (r2_hidden('#skF_5'(A_2732, B_2733, C_2734), B_2733) | r2_hidden('#skF_6'(A_2732, B_2733, C_2734), C_2734) | k2_zfmisc_1(A_2732, B_2733)=C_2734)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_4602, plain, (![A_1089, B_1090, C_1091]: (r2_hidden('#skF_4'(A_1089, B_1090, C_1091), A_1089) | r2_hidden('#skF_6'(A_1089, B_1090, C_1091), C_1091) | k2_zfmisc_1(A_1089, B_1090)=C_1091)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_30, plain, (![E_47, F_48, A_15, B_16]: (r2_hidden(k4_tarski(E_47, F_48), k2_zfmisc_1(A_15, B_16)) | ~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_36, plain, (![A_15, B_16, D_42]: (r2_hidden('#skF_7'(A_15, B_16, k2_zfmisc_1(A_15, B_16), D_42), A_15) | ~r2_hidden(D_42, k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_4144, plain, (![A_1036, B_1037, D_1038]: (r2_hidden('#skF_7'(A_1036, B_1037, k2_zfmisc_1(A_1036, B_1037), D_1038), A_1036) | ~r2_hidden(D_1038, k2_zfmisc_1(A_1036, B_1037)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_50, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_5'(A_15, B_16, C_17), B_16) | r2_hidden('#skF_6'(A_15, B_16, C_17), C_17) | k2_zfmisc_1(A_15, B_16)=C_17)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_2694, plain, (![A_239, B_240, D_241]: (r2_hidden('#skF_7'(A_239, B_240, k2_zfmisc_1(A_239, B_240), D_241), A_239) | ~r2_hidden(D_241, k2_zfmisc_1(A_239, B_240)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_1752, plain, (![A_190, B_191, C_192]: (r2_hidden('#skF_5'(A_190, B_191, C_192), B_191) | r2_hidden('#skF_6'(A_190, B_191, C_192), C_192) | k2_zfmisc_1(A_190, B_191)=C_192)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_1209, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_4'(A_144, B_145, C_146), A_144) | r2_hidden('#skF_6'(A_144, B_145, C_146), C_146) | k2_zfmisc_1(A_144, B_145)=C_146)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_64, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/2.79  tff(c_255, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 8.22/2.79  tff(c_396, plain, (![E_74, F_75, A_76, B_77]: (r2_hidden(k4_tarski(E_74, F_75), k2_zfmisc_1(A_76, B_77)) | ~r2_hidden(F_75, B_77) | ~r2_hidden(E_74, A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_399, plain, (![E_74, F_75]: (r2_hidden(k4_tarski(E_74, F_75), k1_xboole_0) | ~r2_hidden(F_75, '#skF_12') | ~r2_hidden(E_74, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_396])).
% 8.22/2.79  tff(c_420, plain, (![E_82, F_83]: (r2_hidden(k4_tarski(E_82, F_83), k1_xboole_0) | ~r2_hidden(F_83, '#skF_12') | ~r2_hidden(E_82, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_396])).
% 8.22/2.79  tff(c_28, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.22/2.79  tff(c_26, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/2.79  tff(c_260, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_286, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_260])).
% 8.22/2.79  tff(c_292, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_286])).
% 8.22/2.79  tff(c_305, plain, (![D_63, B_64, A_65]: (~r2_hidden(D_63, B_64) | ~r2_hidden(D_63, k4_xboole_0(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_308, plain, (![D_63, A_13]: (~r2_hidden(D_63, k1_xboole_0) | ~r2_hidden(D_63, A_13))), inference(superposition, [status(thm), theory('equality')], [c_292, c_305])).
% 8.22/2.79  tff(c_424, plain, (![E_84, F_85, A_86]: (~r2_hidden(k4_tarski(E_84, F_85), A_86) | ~r2_hidden(F_85, '#skF_12') | ~r2_hidden(E_84, '#skF_11'))), inference(resolution, [status(thm)], [c_420, c_308])).
% 8.22/2.79  tff(c_435, plain, (![F_75, E_74]: (~r2_hidden(F_75, '#skF_12') | ~r2_hidden(E_74, '#skF_11'))), inference(resolution, [status(thm)], [c_399, c_424])).
% 8.22/2.79  tff(c_438, plain, (![E_74]: (~r2_hidden(E_74, '#skF_11'))), inference(splitLeft, [status(thm)], [c_435])).
% 8.22/2.79  tff(c_1525, plain, (![A_157, B_158]: (r2_hidden('#skF_4'(A_157, B_158, '#skF_11'), A_157) | k2_zfmisc_1(A_157, B_158)='#skF_11')), inference(resolution, [status(thm)], [c_1209, c_438])).
% 8.22/2.79  tff(c_1543, plain, (![B_158]: (k2_zfmisc_1('#skF_11', B_158)='#skF_11')), inference(resolution, [status(thm)], [c_1525, c_438])).
% 8.22/2.79  tff(c_489, plain, (![A_102, B_103, D_104]: (r2_hidden('#skF_7'(A_102, B_103, k2_zfmisc_1(A_102, B_103), D_104), A_102) | ~r2_hidden(D_104, k2_zfmisc_1(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_523, plain, (![D_104]: (r2_hidden('#skF_7'('#skF_11', '#skF_12', k1_xboole_0, D_104), '#skF_11') | ~r2_hidden(D_104, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_255, c_489])).
% 8.22/2.79  tff(c_532, plain, (![D_104]: (r2_hidden('#skF_7'('#skF_11', '#skF_12', k1_xboole_0, D_104), '#skF_11') | ~r2_hidden(D_104, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_523])).
% 8.22/2.79  tff(c_533, plain, (![D_104]: (~r2_hidden(D_104, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_438, c_532])).
% 8.22/2.79  tff(c_1380, plain, (![A_150, B_151]: (r2_hidden('#skF_4'(A_150, B_151, k1_xboole_0), A_150) | k2_zfmisc_1(A_150, B_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1209, c_533])).
% 8.22/2.79  tff(c_1418, plain, (![B_151]: (k2_zfmisc_1('#skF_11', B_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1380, c_438])).
% 8.22/2.79  tff(c_1546, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_1418])).
% 8.22/2.79  tff(c_1548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_1546])).
% 8.22/2.79  tff(c_1549, plain, (![F_75]: (~r2_hidden(F_75, '#skF_12'))), inference(splitRight, [status(thm)], [c_435])).
% 8.22/2.79  tff(c_2422, plain, (![A_217, B_218]: (r2_hidden('#skF_5'(A_217, B_218, '#skF_12'), B_218) | k2_zfmisc_1(A_217, B_218)='#skF_12')), inference(resolution, [status(thm)], [c_1752, c_1549])).
% 8.22/2.79  tff(c_400, plain, (![A_78, B_79, D_80]: (r2_hidden('#skF_8'(A_78, B_79, k2_zfmisc_1(A_78, B_79), D_80), B_79) | ~r2_hidden(D_80, k2_zfmisc_1(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_414, plain, (![D_80]: (r2_hidden('#skF_8'('#skF_11', '#skF_12', k1_xboole_0, D_80), '#skF_12') | ~r2_hidden(D_80, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_255, c_400])).
% 8.22/2.79  tff(c_418, plain, (![D_80]: (r2_hidden('#skF_8'('#skF_11', '#skF_12', k1_xboole_0, D_80), '#skF_12') | ~r2_hidden(D_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_414])).
% 8.22/2.79  tff(c_1550, plain, (![D_80]: (~r2_hidden(D_80, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1549, c_418])).
% 8.22/2.79  tff(c_2459, plain, (![A_217]: (k2_zfmisc_1(A_217, k1_xboole_0)='#skF_12')), inference(resolution, [status(thm)], [c_2422, c_1550])).
% 8.22/2.79  tff(c_1967, plain, (![A_203, B_204]: (r2_hidden('#skF_5'(A_203, B_204, k1_xboole_0), B_204) | k2_zfmisc_1(A_203, B_204)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1752, c_1550])).
% 8.22/2.79  tff(c_2049, plain, (![A_203]: (k2_zfmisc_1(A_203, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1967, c_1550])).
% 8.22/2.79  tff(c_2463, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2049])).
% 8.22/2.79  tff(c_2465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2463])).
% 8.22/2.79  tff(c_2466, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_64])).
% 8.22/2.79  tff(c_2468, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_2466])).
% 8.22/2.79  tff(c_2475, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_10')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_28])).
% 8.22/2.79  tff(c_2474, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_2468, c_26])).
% 8.22/2.79  tff(c_2599, plain, (![A_226, B_227]: (k5_xboole_0(A_226, k3_xboole_0(A_226, B_227))=k4_xboole_0(A_226, B_227))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_2619, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_10')=k4_xboole_0(A_13, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2474, c_2599])).
% 8.22/2.79  tff(c_2645, plain, (![A_231]: (k4_xboole_0(A_231, '#skF_10')=A_231)), inference(demodulation, [status(thm), theory('equality')], [c_2475, c_2619])).
% 8.22/2.79  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_2654, plain, (![D_10, A_231]: (~r2_hidden(D_10, '#skF_10') | ~r2_hidden(D_10, A_231))), inference(superposition, [status(thm), theory('equality')], [c_2645, c_8])).
% 8.22/2.79  tff(c_2770, plain, (![B_247, D_248, A_249]: (~r2_hidden('#skF_7'('#skF_10', B_247, k2_zfmisc_1('#skF_10', B_247), D_248), A_249) | ~r2_hidden(D_248, k2_zfmisc_1('#skF_10', B_247)))), inference(resolution, [status(thm)], [c_2694, c_2654])).
% 8.22/2.79  tff(c_2781, plain, (![D_250, B_251]: (~r2_hidden(D_250, k2_zfmisc_1('#skF_10', B_251)))), inference(resolution, [status(thm)], [c_36, c_2770])).
% 8.22/2.79  tff(c_2796, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_10'))), inference(resolution, [status(thm)], [c_30, c_2781])).
% 8.22/2.79  tff(c_2834, plain, (![E_255]: (~r2_hidden(E_255, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2796])).
% 8.22/2.79  tff(c_3449, plain, (![A_311, B_312]: (r2_hidden('#skF_5'(A_311, B_312, '#skF_10'), B_312) | k2_zfmisc_1(A_311, B_312)='#skF_10')), inference(resolution, [status(thm)], [c_50, c_2834])).
% 8.22/2.79  tff(c_2833, plain, (![E_47]: (~r2_hidden(E_47, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2796])).
% 8.22/2.79  tff(c_3531, plain, (![A_311]: (k2_zfmisc_1(A_311, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_3449, c_2833])).
% 8.22/2.79  tff(c_62, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/2.79  tff(c_254, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 8.22/2.79  tff(c_2469, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_254])).
% 8.22/2.79  tff(c_3717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3531, c_2469])).
% 8.22/2.79  tff(c_3718, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_2796])).
% 8.22/2.79  tff(c_3726, plain, (![A_318, B_319, C_320]: (k2_zfmisc_1(A_318, B_319)=C_320)), inference(negUnitSimplification, [status(thm)], [c_3718, c_3718, c_50])).
% 8.22/2.79  tff(c_3820, plain, (![C_320]: (C_320!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3726, c_2469])).
% 8.22/2.79  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_2480, plain, (![A_219]: (k3_xboole_0(A_219, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_2468, c_26])).
% 8.22/2.79  tff(c_2498, plain, (![B_2]: (k3_xboole_0('#skF_10', B_2)='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2, c_2480])).
% 8.22/2.79  tff(c_2501, plain, (![A_220]: (k5_xboole_0(A_220, '#skF_10')=A_220)), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_28])).
% 8.22/2.79  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/2.79  tff(c_2510, plain, (![A_220]: (k5_xboole_0('#skF_10', A_220)=A_220)), inference(superposition, [status(thm), theory('equality')], [c_2501, c_4])).
% 8.22/2.79  tff(c_2616, plain, (![B_227]: (k4_xboole_0('#skF_10', B_227)=k3_xboole_0('#skF_10', B_227))), inference(superposition, [status(thm), theory('equality')], [c_2510, c_2599])).
% 8.22/2.79  tff(c_2630, plain, (![B_227]: (k4_xboole_0('#skF_10', B_227)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_2616])).
% 8.22/2.79  tff(c_3915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3820, c_2630])).
% 8.22/2.79  tff(c_3916, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_2466])).
% 8.22/2.79  tff(c_3925, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_9')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_28])).
% 8.22/2.79  tff(c_3924, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_3916, c_26])).
% 8.22/2.79  tff(c_4049, plain, (![A_1023, B_1024]: (k5_xboole_0(A_1023, k3_xboole_0(A_1023, B_1024))=k4_xboole_0(A_1023, B_1024))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_4069, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_9')=k4_xboole_0(A_13, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3924, c_4049])).
% 8.22/2.79  tff(c_4095, plain, (![A_1028]: (k4_xboole_0(A_1028, '#skF_9')=A_1028)), inference(demodulation, [status(thm), theory('equality')], [c_3925, c_4069])).
% 8.22/2.79  tff(c_4104, plain, (![D_10, A_1028]: (~r2_hidden(D_10, '#skF_9') | ~r2_hidden(D_10, A_1028))), inference(superposition, [status(thm), theory('equality')], [c_4095, c_8])).
% 8.22/2.79  tff(c_4220, plain, (![B_1044, D_1045, A_1046]: (~r2_hidden('#skF_7'('#skF_9', B_1044, k2_zfmisc_1('#skF_9', B_1044), D_1045), A_1046) | ~r2_hidden(D_1045, k2_zfmisc_1('#skF_9', B_1044)))), inference(resolution, [status(thm)], [c_4144, c_4104])).
% 8.22/2.79  tff(c_4231, plain, (![D_1047, B_1048]: (~r2_hidden(D_1047, k2_zfmisc_1('#skF_9', B_1048)))), inference(resolution, [status(thm)], [c_36, c_4220])).
% 8.22/2.79  tff(c_4246, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_9'))), inference(resolution, [status(thm)], [c_30, c_4231])).
% 8.22/2.79  tff(c_4252, plain, (![E_47]: (~r2_hidden(E_47, '#skF_9'))), inference(splitLeft, [status(thm)], [c_4246])).
% 8.22/2.79  tff(c_4894, plain, (![A_1108, B_1109]: (r2_hidden('#skF_4'(A_1108, B_1109, '#skF_9'), A_1108) | k2_zfmisc_1(A_1108, B_1109)='#skF_9')), inference(resolution, [status(thm)], [c_4602, c_4252])).
% 8.22/2.79  tff(c_4976, plain, (![B_1109]: (k2_zfmisc_1('#skF_9', B_1109)='#skF_9')), inference(resolution, [status(thm)], [c_4894, c_4252])).
% 8.22/2.79  tff(c_3919, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_254])).
% 8.22/2.79  tff(c_4995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4976, c_3919])).
% 8.22/2.79  tff(c_4996, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_4246])).
% 8.22/2.79  tff(c_5008, plain, (![A_1115, B_1116]: (k2_zfmisc_1(A_1115, B_1116)='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_4996, c_4996, c_50])).
% 8.22/2.79  tff(c_5004, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(A_15, B_16)=C_17)), inference(negUnitSimplification, [status(thm)], [c_4996, c_4996, c_50])).
% 8.22/2.79  tff(c_5190, plain, (![C_1802]: (C_1802='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5008, c_5004])).
% 8.22/2.79  tff(c_5247, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5190, c_3919])).
% 8.22/2.79  tff(c_5248, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 8.22/2.79  tff(c_5395, plain, (![E_2429, F_2430, A_2431, B_2432]: (r2_hidden(k4_tarski(E_2429, F_2430), k2_zfmisc_1(A_2431, B_2432)) | ~r2_hidden(F_2430, B_2432) | ~r2_hidden(E_2429, A_2431))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_5401, plain, (![E_2429, F_2430]: (r2_hidden(k4_tarski(E_2429, F_2430), k1_xboole_0) | ~r2_hidden(F_2430, '#skF_12') | ~r2_hidden(E_2429, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_5248, c_5395])).
% 8.22/2.79  tff(c_5406, plain, (![E_2435, F_2436]: (r2_hidden(k4_tarski(E_2435, F_2436), k1_xboole_0) | ~r2_hidden(F_2436, '#skF_12') | ~r2_hidden(E_2435, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_5248, c_5395])).
% 8.22/2.79  tff(c_5259, plain, (![A_2415, B_2416]: (k5_xboole_0(A_2415, k3_xboole_0(A_2415, B_2416))=k4_xboole_0(A_2415, B_2416))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_5285, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5259])).
% 8.22/2.79  tff(c_5293, plain, (![A_2420]: (k4_xboole_0(A_2420, k1_xboole_0)=A_2420)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5285])).
% 8.22/2.79  tff(c_5299, plain, (![D_10, A_2420]: (~r2_hidden(D_10, k1_xboole_0) | ~r2_hidden(D_10, A_2420))), inference(superposition, [status(thm), theory('equality')], [c_5293, c_8])).
% 8.22/2.79  tff(c_8137, plain, (![E_2620, F_2621, A_2622]: (~r2_hidden(k4_tarski(E_2620, F_2621), A_2622) | ~r2_hidden(F_2621, '#skF_12') | ~r2_hidden(E_2620, '#skF_11'))), inference(resolution, [status(thm)], [c_5406, c_5299])).
% 8.22/2.79  tff(c_8148, plain, (![F_2430, E_2429]: (~r2_hidden(F_2430, '#skF_12') | ~r2_hidden(E_2429, '#skF_11'))), inference(resolution, [status(thm)], [c_5401, c_8137])).
% 8.22/2.79  tff(c_8151, plain, (![E_2429]: (~r2_hidden(E_2429, '#skF_11'))), inference(splitLeft, [status(thm)], [c_8148])).
% 8.22/2.79  tff(c_10362, plain, (![A_2747, B_2748]: (r2_hidden('#skF_5'(A_2747, B_2748, '#skF_11'), B_2748) | k2_zfmisc_1(A_2747, B_2748)='#skF_11')), inference(resolution, [status(thm)], [c_9757, c_8151])).
% 8.22/2.79  tff(c_10384, plain, (![A_2747]: (k2_zfmisc_1(A_2747, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_10362, c_8151])).
% 8.22/2.79  tff(c_8153, plain, (![A_2624, B_2625, D_2626]: (r2_hidden('#skF_7'(A_2624, B_2625, k2_zfmisc_1(A_2624, B_2625), D_2626), A_2624) | ~r2_hidden(D_2626, k2_zfmisc_1(A_2624, B_2625)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_8178, plain, (![D_2626]: (r2_hidden('#skF_7'('#skF_11', '#skF_12', k1_xboole_0, D_2626), '#skF_11') | ~r2_hidden(D_2626, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_5248, c_8153])).
% 8.22/2.79  tff(c_8185, plain, (![D_2626]: (r2_hidden('#skF_7'('#skF_11', '#skF_12', k1_xboole_0, D_2626), '#skF_11') | ~r2_hidden(D_2626, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5248, c_8178])).
% 8.22/2.79  tff(c_8186, plain, (![D_2626]: (~r2_hidden(D_2626, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_8151, c_8185])).
% 8.22/2.79  tff(c_10112, plain, (![A_2739, B_2740]: (r2_hidden('#skF_5'(A_2739, B_2740, k1_xboole_0), B_2740) | k2_zfmisc_1(A_2739, B_2740)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9757, c_8186])).
% 8.22/2.79  tff(c_10174, plain, (![A_2739]: (k2_zfmisc_1(A_2739, '#skF_11')=k1_xboole_0)), inference(resolution, [status(thm)], [c_10112, c_8151])).
% 8.22/2.79  tff(c_10388, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_10384, c_10174])).
% 8.22/2.79  tff(c_10390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_10388])).
% 8.22/2.79  tff(c_10391, plain, (![F_2430]: (~r2_hidden(F_2430, '#skF_12'))), inference(splitRight, [status(thm)], [c_8148])).
% 8.22/2.79  tff(c_12126, plain, (![B_2833, C_2834]: (r2_hidden('#skF_2'('#skF_12', B_2833, C_2834), C_2834) | k4_xboole_0('#skF_12', B_2833)=C_2834)), inference(resolution, [status(thm)], [c_12080, c_10391])).
% 8.22/2.79  tff(c_170, plain, (![B_54, A_55]: (k3_xboole_0(B_54, A_55)=k3_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_186, plain, (![A_55]: (k3_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_170, c_26])).
% 8.22/2.79  tff(c_83, plain, (![B_51, A_52]: (k5_xboole_0(B_51, A_52)=k5_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/2.79  tff(c_99, plain, (![A_52]: (k5_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_83, c_28])).
% 8.22/2.79  tff(c_5282, plain, (![B_2416]: (k4_xboole_0(k1_xboole_0, B_2416)=k3_xboole_0(k1_xboole_0, B_2416))), inference(superposition, [status(thm), theory('equality')], [c_99, c_5259])).
% 8.22/2.79  tff(c_5290, plain, (![B_2416]: (k4_xboole_0(k1_xboole_0, B_2416)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_5282])).
% 8.22/2.79  tff(c_7774, plain, (![A_2611, B_2612, C_2613]: (r2_hidden('#skF_1'(A_2611, B_2612, C_2613), A_2611) | r2_hidden('#skF_2'(A_2611, B_2612, C_2613), C_2613) | k4_xboole_0(A_2611, B_2612)=C_2613)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_5249, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 8.22/2.79  tff(c_5398, plain, (![E_2429, F_2430]: (r2_hidden(k4_tarski(E_2429, F_2430), k1_xboole_0) | ~r2_hidden(F_2430, '#skF_10') | ~r2_hidden(E_2429, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5249, c_5395])).
% 8.22/2.79  tff(c_5402, plain, (![E_2433, F_2434]: (r2_hidden(k4_tarski(E_2433, F_2434), k1_xboole_0) | ~r2_hidden(F_2434, '#skF_10') | ~r2_hidden(E_2433, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5249, c_5395])).
% 8.22/2.79  tff(c_5410, plain, (![E_2437, F_2438, A_2439]: (~r2_hidden(k4_tarski(E_2437, F_2438), A_2439) | ~r2_hidden(F_2438, '#skF_10') | ~r2_hidden(E_2437, '#skF_9'))), inference(resolution, [status(thm)], [c_5402, c_5299])).
% 8.22/2.79  tff(c_5425, plain, (![F_2430, E_2429]: (~r2_hidden(F_2430, '#skF_10') | ~r2_hidden(E_2429, '#skF_9'))), inference(resolution, [status(thm)], [c_5398, c_5410])).
% 8.22/2.79  tff(c_5428, plain, (![E_2429]: (~r2_hidden(E_2429, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5425])).
% 8.22/2.79  tff(c_7409, plain, (![A_2556, B_2557, D_2558]: (r2_hidden('#skF_7'(A_2556, B_2557, k2_zfmisc_1(A_2556, B_2557), D_2558), A_2556) | ~r2_hidden(D_2558, k2_zfmisc_1(A_2556, B_2557)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_7431, plain, (![D_2558]: (r2_hidden('#skF_7'('#skF_9', '#skF_10', k1_xboole_0, D_2558), '#skF_9') | ~r2_hidden(D_2558, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_5249, c_7409])).
% 8.22/2.79  tff(c_7440, plain, (![D_2558]: (r2_hidden('#skF_7'('#skF_9', '#skF_10', k1_xboole_0, D_2558), '#skF_9') | ~r2_hidden(D_2558, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5249, c_7431])).
% 8.22/2.79  tff(c_7441, plain, (![D_2558]: (~r2_hidden(D_2558, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_5428, c_7440])).
% 8.22/2.79  tff(c_7850, plain, (![B_2612, C_2613]: (r2_hidden('#skF_2'(k1_xboole_0, B_2612, C_2613), C_2613) | k4_xboole_0(k1_xboole_0, B_2612)=C_2613)), inference(resolution, [status(thm)], [c_7774, c_7441])).
% 8.22/2.79  tff(c_8018, plain, (![B_2617, C_2618]: (r2_hidden('#skF_2'(k1_xboole_0, B_2617, C_2618), C_2618) | k1_xboole_0=C_2618)), inference(demodulation, [status(thm), theory('equality')], [c_5290, c_7850])).
% 8.22/2.79  tff(c_7330, plain, (![A_2550, B_2551, C_2552]: (r2_hidden('#skF_1'(A_2550, B_2551, C_2552), A_2550) | r2_hidden('#skF_2'(A_2550, B_2551, C_2552), C_2552) | k4_xboole_0(A_2550, B_2551)=C_2552)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_5558, plain, (![A_2473, B_2474, D_2475]: (r2_hidden('#skF_7'(A_2473, B_2474, k2_zfmisc_1(A_2473, B_2474), D_2475), A_2473) | ~r2_hidden(D_2475, k2_zfmisc_1(A_2473, B_2474)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_5608, plain, (![D_2475]: (r2_hidden('#skF_7'('#skF_9', '#skF_10', k1_xboole_0, D_2475), '#skF_9') | ~r2_hidden(D_2475, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_5249, c_5558])).
% 8.22/2.79  tff(c_5624, plain, (![D_2475]: (r2_hidden('#skF_7'('#skF_9', '#skF_10', k1_xboole_0, D_2475), '#skF_9') | ~r2_hidden(D_2475, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5249, c_5608])).
% 8.22/2.79  tff(c_5625, plain, (![D_2475]: (~r2_hidden(D_2475, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_5428, c_5624])).
% 8.22/2.79  tff(c_7338, plain, (![B_2551, C_2552]: (r2_hidden('#skF_2'(k1_xboole_0, B_2551, C_2552), C_2552) | k4_xboole_0(k1_xboole_0, B_2551)=C_2552)), inference(resolution, [status(thm)], [c_7330, c_5625])).
% 8.22/2.79  tff(c_7380, plain, (![B_2553, C_2554]: (r2_hidden('#skF_2'(k1_xboole_0, B_2553, C_2554), C_2554) | k1_xboole_0=C_2554)), inference(demodulation, [status(thm), theory('equality')], [c_5290, c_7338])).
% 8.22/2.79  tff(c_5430, plain, (![E_2441, F_2442, A_2443]: (~r2_hidden(k4_tarski(E_2441, F_2442), A_2443) | ~r2_hidden(F_2442, '#skF_12') | ~r2_hidden(E_2441, '#skF_11'))), inference(resolution, [status(thm)], [c_5406, c_5299])).
% 8.22/2.79  tff(c_5441, plain, (![F_2430, E_2429]: (~r2_hidden(F_2430, '#skF_12') | ~r2_hidden(E_2429, '#skF_11'))), inference(resolution, [status(thm)], [c_5401, c_5430])).
% 8.22/2.79  tff(c_5444, plain, (![E_2429]: (~r2_hidden(E_2429, '#skF_11'))), inference(splitLeft, [status(thm)], [c_5441])).
% 8.22/2.79  tff(c_7388, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_7380, c_5444])).
% 8.22/2.79  tff(c_7406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_7388])).
% 8.22/2.79  tff(c_7407, plain, (![F_2430]: (~r2_hidden(F_2430, '#skF_12'))), inference(splitRight, [status(thm)], [c_5441])).
% 8.22/2.79  tff(c_8098, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8018, c_7407])).
% 8.22/2.79  tff(c_8134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_8098])).
% 8.22/2.79  tff(c_8135, plain, (![F_2430]: (~r2_hidden(F_2430, '#skF_10'))), inference(splitRight, [status(thm)], [c_5425])).
% 8.22/2.79  tff(c_10505, plain, (![A_2778, B_2779, D_2780]: (r2_hidden('#skF_8'(A_2778, B_2779, k2_zfmisc_1(A_2778, B_2779), D_2780), B_2779) | ~r2_hidden(D_2780, k2_zfmisc_1(A_2778, B_2779)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_10555, plain, (![D_2780]: (r2_hidden('#skF_8'('#skF_9', '#skF_10', k1_xboole_0, D_2780), '#skF_10') | ~r2_hidden(D_2780, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_5249, c_10505])).
% 8.22/2.79  tff(c_10571, plain, (![D_2780]: (r2_hidden('#skF_8'('#skF_9', '#skF_10', k1_xboole_0, D_2780), '#skF_10') | ~r2_hidden(D_2780, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5249, c_10555])).
% 8.22/2.79  tff(c_10572, plain, (![D_2780]: (~r2_hidden(D_2780, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_8135, c_10571])).
% 8.22/2.79  tff(c_12153, plain, (![B_2835]: (k4_xboole_0('#skF_12', B_2835)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12126, c_10572])).
% 8.22/2.79  tff(c_5291, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5285])).
% 8.22/2.79  tff(c_12162, plain, (k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_12153, c_5291])).
% 8.22/2.79  tff(c_12178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_12162])).
% 8.22/2.79  tff(c_12180, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_56])).
% 8.22/2.79  tff(c_12181, plain, ('#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_12180, c_81])).
% 8.22/2.79  tff(c_13280, plain, (![B_4462, A_4463]: (k3_xboole_0(B_4462, A_4463)=k3_xboole_0(A_4463, B_4462))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_12182, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12180, c_12180, c_26])).
% 8.22/2.79  tff(c_13296, plain, (![A_4463]: (k3_xboole_0('#skF_12', A_4463)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_13280, c_12182])).
% 8.22/2.79  tff(c_13365, plain, (![B_4465, A_4466]: (k5_xboole_0(B_4465, A_4466)=k5_xboole_0(A_4466, B_4465))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/2.79  tff(c_12183, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_12')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12180, c_28])).
% 8.22/2.79  tff(c_13435, plain, (![A_4469]: (k5_xboole_0('#skF_12', A_4469)=A_4469)), inference(superposition, [status(thm), theory('equality')], [c_13365, c_12183])).
% 8.22/2.79  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_13442, plain, (![B_12]: (k4_xboole_0('#skF_12', B_12)=k3_xboole_0('#skF_12', B_12))), inference(superposition, [status(thm), theory('equality')], [c_13435, c_24])).
% 8.22/2.79  tff(c_13473, plain, (![B_12]: (k4_xboole_0('#skF_12', B_12)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_13296, c_13442])).
% 8.22/2.79  tff(c_14600, plain, (![A_4570, B_4571, C_4572]: (r2_hidden('#skF_1'(A_4570, B_4571, C_4572), A_4570) | r2_hidden('#skF_2'(A_4570, B_4571, C_4572), C_4572) | k4_xboole_0(A_4570, B_4571)=C_4572)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_13593, plain, (![A_4489, B_4490, D_4491]: (r2_hidden('#skF_7'(A_4489, B_4490, k2_zfmisc_1(A_4489, B_4490), D_4491), A_4489) | ~r2_hidden(D_4491, k2_zfmisc_1(A_4489, B_4490)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_13412, plain, (![A_4467, B_4468]: (k5_xboole_0(A_4467, k3_xboole_0(A_4467, B_4468))=k4_xboole_0(A_4467, B_4468))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_13430, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_12')=k4_xboole_0(A_13, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_12182, c_13412])).
% 8.22/2.79  tff(c_13434, plain, (![A_13]: (k4_xboole_0(A_13, '#skF_12')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_12183, c_13430])).
% 8.22/2.79  tff(c_13523, plain, (![D_4475, B_4476, A_4477]: (~r2_hidden(D_4475, B_4476) | ~r2_hidden(D_4475, k4_xboole_0(A_4477, B_4476)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_13529, plain, (![D_4475, A_13]: (~r2_hidden(D_4475, '#skF_12') | ~r2_hidden(D_4475, A_13))), inference(superposition, [status(thm), theory('equality')], [c_13434, c_13523])).
% 8.22/2.79  tff(c_13623, plain, (![B_4495, D_4496, A_4497]: (~r2_hidden('#skF_7'('#skF_12', B_4495, k2_zfmisc_1('#skF_12', B_4495), D_4496), A_4497) | ~r2_hidden(D_4496, k2_zfmisc_1('#skF_12', B_4495)))), inference(resolution, [status(thm)], [c_13593, c_13529])).
% 8.22/2.79  tff(c_13634, plain, (![D_4498, B_4499]: (~r2_hidden(D_4498, k2_zfmisc_1('#skF_12', B_4499)))), inference(resolution, [status(thm)], [c_36, c_13623])).
% 8.22/2.79  tff(c_13649, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_12'))), inference(resolution, [status(thm)], [c_30, c_13634])).
% 8.22/2.79  tff(c_13650, plain, (![E_47]: (~r2_hidden(E_47, '#skF_12'))), inference(splitLeft, [status(thm)], [c_13649])).
% 8.22/2.79  tff(c_14619, plain, (![B_4571, C_4572]: (r2_hidden('#skF_2'('#skF_12', B_4571, C_4572), C_4572) | k4_xboole_0('#skF_12', B_4571)=C_4572)), inference(resolution, [status(thm)], [c_14600, c_13650])).
% 8.22/2.79  tff(c_14668, plain, (![B_4573, C_4574]: (r2_hidden('#skF_2'('#skF_12', B_4573, C_4574), C_4574) | C_4574='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_13473, c_14619])).
% 8.22/2.79  tff(c_13632, plain, (![D_42, B_16]: (~r2_hidden(D_42, k2_zfmisc_1('#skF_12', B_16)))), inference(resolution, [status(thm)], [c_36, c_13623])).
% 8.22/2.79  tff(c_14697, plain, (![B_16]: (k2_zfmisc_1('#skF_12', B_16)='#skF_12')), inference(resolution, [status(thm)], [c_14668, c_13632])).
% 8.22/2.79  tff(c_12299, plain, (![B_2841, A_2842]: (k3_xboole_0(B_2841, A_2842)=k3_xboole_0(A_2842, B_2841))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_12315, plain, (![A_2842]: (k3_xboole_0('#skF_12', A_2842)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_12299, c_12182])).
% 8.22/2.79  tff(c_12210, plain, (![B_2838, A_2839]: (k5_xboole_0(B_2838, A_2839)=k5_xboole_0(A_2839, B_2838))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/2.79  tff(c_12226, plain, (![A_2839]: (k5_xboole_0('#skF_12', A_2839)=A_2839)), inference(superposition, [status(thm), theory('equality')], [c_12210, c_12183])).
% 8.22/2.79  tff(c_12379, plain, (![A_2844, B_2845]: (k5_xboole_0(A_2844, k3_xboole_0(A_2844, B_2845))=k4_xboole_0(A_2844, B_2845))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_12402, plain, (![B_2845]: (k4_xboole_0('#skF_12', B_2845)=k3_xboole_0('#skF_12', B_2845))), inference(superposition, [status(thm), theory('equality')], [c_12226, c_12379])).
% 8.22/2.79  tff(c_12410, plain, (![B_2845]: (k4_xboole_0('#skF_12', B_2845)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12315, c_12402])).
% 8.22/2.79  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_1'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_12522, plain, (![A_2865, B_2866, D_2867]: (r2_hidden('#skF_7'(A_2865, B_2866, k2_zfmisc_1(A_2865, B_2866), D_2867), A_2865) | ~r2_hidden(D_2867, k2_zfmisc_1(A_2865, B_2866)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_12405, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_12')=k4_xboole_0(A_13, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_12182, c_12379])).
% 8.22/2.79  tff(c_12411, plain, (![A_13]: (k4_xboole_0(A_13, '#skF_12')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_12183, c_12405])).
% 8.22/2.79  tff(c_12451, plain, (![D_2851, B_2852, A_2853]: (~r2_hidden(D_2851, B_2852) | ~r2_hidden(D_2851, k4_xboole_0(A_2853, B_2852)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_12457, plain, (![D_2851, A_13]: (~r2_hidden(D_2851, '#skF_12') | ~r2_hidden(D_2851, A_13))), inference(superposition, [status(thm), theory('equality')], [c_12411, c_12451])).
% 8.22/2.79  tff(c_12578, plain, (![B_2874, D_2875, A_2876]: (~r2_hidden('#skF_7'('#skF_12', B_2874, k2_zfmisc_1('#skF_12', B_2874), D_2875), A_2876) | ~r2_hidden(D_2875, k2_zfmisc_1('#skF_12', B_2874)))), inference(resolution, [status(thm)], [c_12522, c_12457])).
% 8.22/2.79  tff(c_12589, plain, (![D_2877, B_2878]: (~r2_hidden(D_2877, k2_zfmisc_1('#skF_12', B_2878)))), inference(resolution, [status(thm)], [c_36, c_12578])).
% 8.22/2.79  tff(c_12614, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_12'))), inference(resolution, [status(thm)], [c_30, c_12589])).
% 8.22/2.79  tff(c_12653, plain, (![E_2882]: (~r2_hidden(E_2882, '#skF_12'))), inference(splitLeft, [status(thm)], [c_12614])).
% 8.22/2.79  tff(c_12657, plain, (![B_6, C_7]: (r2_hidden('#skF_2'('#skF_12', B_6, C_7), C_7) | k4_xboole_0('#skF_12', B_6)=C_7)), inference(resolution, [status(thm)], [c_22, c_12653])).
% 8.22/2.79  tff(c_12905, plain, (![B_2900, C_2901]: (r2_hidden('#skF_2'('#skF_12', B_2900, C_2901), C_2901) | C_2901='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12410, c_12657])).
% 8.22/2.79  tff(c_34, plain, (![A_15, B_16, D_42]: (r2_hidden('#skF_8'(A_15, B_16, k2_zfmisc_1(A_15, B_16), D_42), B_16) | ~r2_hidden(D_42, k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_12677, plain, (![D_42, A_15]: (~r2_hidden(D_42, k2_zfmisc_1(A_15, '#skF_12')))), inference(resolution, [status(thm)], [c_34, c_12653])).
% 8.22/2.79  tff(c_12946, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_12905, c_12677])).
% 8.22/2.79  tff(c_12179, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 8.22/2.79  tff(c_12188, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_12180, c_12180, c_12179])).
% 8.22/2.79  tff(c_12189, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_12188])).
% 8.22/2.79  tff(c_54, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/2.79  tff(c_12295, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_12180, c_12189, c_12180, c_54])).
% 8.22/2.79  tff(c_12957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12946, c_12295])).
% 8.22/2.79  tff(c_12958, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_12614])).
% 8.22/2.79  tff(c_13039, plain, (![A_2907, B_2908]: (k4_xboole_0(A_2907, B_2908)='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_12958, c_12958, c_22])).
% 8.22/2.79  tff(c_12996, plain, (![A_5, B_6, C_7]: (k4_xboole_0(A_5, B_6)=C_7)), inference(negUnitSimplification, [status(thm)], [c_12958, c_12958, c_22])).
% 8.22/2.79  tff(c_13214, plain, (![C_3883]: (C_3883='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_13039, c_12996])).
% 8.22/2.79  tff(c_13229, plain, ('#skF_11'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_13214, c_12315])).
% 8.22/2.79  tff(c_13257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12181, c_13229])).
% 8.22/2.79  tff(c_13258, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_12188])).
% 8.22/2.79  tff(c_13328, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_12180, c_13258, c_12180, c_54])).
% 8.22/2.79  tff(c_14709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14697, c_13328])).
% 8.22/2.79  tff(c_14710, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_13649])).
% 8.22/2.79  tff(c_14730, plain, (![A_4577, B_4578]: (k2_zfmisc_1(A_4577, B_4578)='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_14710, c_14710, c_50])).
% 8.22/2.79  tff(c_14718, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(A_15, B_16)=C_17)), inference(negUnitSimplification, [status(thm)], [c_14710, c_14710, c_50])).
% 8.22/2.79  tff(c_14900, plain, (![C_5228]: (C_5228='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_14730, c_14718])).
% 8.22/2.79  tff(c_14917, plain, ('#skF_11'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_14900, c_13473])).
% 8.22/2.79  tff(c_14955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12181, c_14917])).
% 8.22/2.79  tff(c_14957, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_58])).
% 8.22/2.79  tff(c_60, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.22/2.79  tff(c_15066, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_14957, c_14957, c_14957, c_60])).
% 8.22/2.79  tff(c_15067, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_15066])).
% 8.22/2.79  tff(c_14958, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_14957, c_14957, c_26])).
% 8.22/2.79  tff(c_14983, plain, (![B_5951, A_5952]: (k3_xboole_0(B_5951, A_5952)=k3_xboole_0(A_5952, B_5951))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_15021, plain, (![A_13]: (k3_xboole_0('#skF_11', A_13)='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_14958, c_14983])).
% 8.22/2.79  tff(c_15113, plain, (![A_13]: (k3_xboole_0('#skF_9', A_13)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15067, c_15067, c_15021])).
% 8.22/2.79  tff(c_14959, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_11')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14957, c_28])).
% 8.22/2.79  tff(c_15071, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_9')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_15067, c_14959])).
% 8.22/2.79  tff(c_15148, plain, (![B_5957, A_5958]: (k5_xboole_0(B_5957, A_5958)=k5_xboole_0(A_5958, B_5957))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.22/2.79  tff(c_15186, plain, (![A_14]: (k5_xboole_0('#skF_9', A_14)=A_14)), inference(superposition, [status(thm), theory('equality')], [c_15071, c_15148])).
% 8.22/2.79  tff(c_15242, plain, (![A_5963, B_5964]: (k5_xboole_0(A_5963, k3_xboole_0(A_5963, B_5964))=k4_xboole_0(A_5963, B_5964))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_15256, plain, (![B_5964]: (k4_xboole_0('#skF_9', B_5964)=k3_xboole_0('#skF_9', B_5964))), inference(superposition, [status(thm), theory('equality')], [c_15186, c_15242])).
% 8.22/2.79  tff(c_15272, plain, (![B_5964]: (k4_xboole_0('#skF_9', B_5964)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15113, c_15256])).
% 8.22/2.79  tff(c_15564, plain, (![A_6004, B_6005, C_6006]: (r2_hidden('#skF_1'(A_6004, B_6005, C_6006), A_6004) | r2_hidden('#skF_2'(A_6004, B_6005, C_6006), C_6006) | k4_xboole_0(A_6004, B_6005)=C_6006)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_15379, plain, (![A_5981, B_5982, D_5983]: (r2_hidden('#skF_7'(A_5981, B_5982, k2_zfmisc_1(A_5981, B_5982), D_5983), A_5981) | ~r2_hidden(D_5983, k2_zfmisc_1(A_5981, B_5982)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_15070, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15067, c_15067, c_14958])).
% 8.22/2.79  tff(c_15262, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_9')=k4_xboole_0(A_13, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_15070, c_15242])).
% 8.22/2.79  tff(c_15275, plain, (![A_5965]: (k4_xboole_0(A_5965, '#skF_9')=A_5965)), inference(demodulation, [status(thm), theory('equality')], [c_15071, c_15262])).
% 8.22/2.79  tff(c_15281, plain, (![D_10, A_5965]: (~r2_hidden(D_10, '#skF_9') | ~r2_hidden(D_10, A_5965))), inference(superposition, [status(thm), theory('equality')], [c_15275, c_8])).
% 8.22/2.79  tff(c_15409, plain, (![B_5987, D_5988, A_5989]: (~r2_hidden('#skF_7'('#skF_9', B_5987, k2_zfmisc_1('#skF_9', B_5987), D_5988), A_5989) | ~r2_hidden(D_5988, k2_zfmisc_1('#skF_9', B_5987)))), inference(resolution, [status(thm)], [c_15379, c_15281])).
% 8.22/2.79  tff(c_15420, plain, (![D_5990, B_5991]: (~r2_hidden(D_5990, k2_zfmisc_1('#skF_9', B_5991)))), inference(resolution, [status(thm)], [c_36, c_15409])).
% 8.22/2.79  tff(c_15435, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_9'))), inference(resolution, [status(thm)], [c_30, c_15420])).
% 8.22/2.79  tff(c_15436, plain, (![E_47]: (~r2_hidden(E_47, '#skF_9'))), inference(splitLeft, [status(thm)], [c_15435])).
% 8.22/2.79  tff(c_15580, plain, (![B_6005, C_6006]: (r2_hidden('#skF_2'('#skF_9', B_6005, C_6006), C_6006) | k4_xboole_0('#skF_9', B_6005)=C_6006)), inference(resolution, [status(thm)], [c_15564, c_15436])).
% 8.22/2.79  tff(c_15705, plain, (![B_6013, C_6014]: (r2_hidden('#skF_2'('#skF_9', B_6013, C_6014), C_6014) | C_6014='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15272, c_15580])).
% 8.22/2.79  tff(c_15418, plain, (![D_42, B_16]: (~r2_hidden(D_42, k2_zfmisc_1('#skF_9', B_16)))), inference(resolution, [status(thm)], [c_36, c_15409])).
% 8.22/2.79  tff(c_15749, plain, (![B_16]: (k2_zfmisc_1('#skF_9', B_16)='#skF_9')), inference(resolution, [status(thm)], [c_15705, c_15418])).
% 8.22/2.79  tff(c_14956, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 8.22/2.79  tff(c_14964, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_14957, c_14956])).
% 8.22/2.79  tff(c_15072, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_15067, c_14964])).
% 8.22/2.79  tff(c_15794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15749, c_15072])).
% 8.22/2.79  tff(c_15795, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_15435])).
% 8.22/2.79  tff(c_15839, plain, (![A_6021, B_6022, C_6023]: (k2_zfmisc_1(A_6021, B_6022)=C_6023)), inference(negUnitSimplification, [status(thm)], [c_15795, c_15795, c_50])).
% 8.22/2.79  tff(c_15941, plain, (![C_6023]: (C_6023!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_15839, c_15072])).
% 8.22/2.79  tff(c_16077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15941, c_15272])).
% 8.22/2.79  tff(c_16078, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_15066])).
% 8.22/2.79  tff(c_14981, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9' | '#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_14957, c_14957, c_14957, c_56])).
% 8.22/2.79  tff(c_14982, plain, ('#skF_11'!='#skF_12'), inference(splitLeft, [status(thm)], [c_14981])).
% 8.22/2.79  tff(c_16081, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_16078, c_14982])).
% 8.22/2.79  tff(c_16083, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_10')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_16078, c_14959])).
% 8.22/2.79  tff(c_14999, plain, (![A_5952]: (k3_xboole_0('#skF_11', A_5952)='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_14983, c_14958])).
% 8.22/2.79  tff(c_16080, plain, (![A_5952]: (k3_xboole_0('#skF_10', A_5952)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16078, c_16078, c_14999])).
% 8.22/2.79  tff(c_16211, plain, (![A_7290, B_7291]: (k5_xboole_0(A_7290, k3_xboole_0(A_7290, B_7291))=k4_xboole_0(A_7290, B_7291))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_16220, plain, (![A_5952]: (k5_xboole_0('#skF_10', '#skF_10')=k4_xboole_0('#skF_10', A_5952))), inference(superposition, [status(thm), theory('equality')], [c_16080, c_16211])).
% 8.22/2.79  tff(c_16232, plain, (![A_5952]: (k4_xboole_0('#skF_10', A_5952)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16083, c_16220])).
% 8.22/2.79  tff(c_16392, plain, (![A_7312, B_7313, D_7314]: (r2_hidden('#skF_7'(A_7312, B_7313, k2_zfmisc_1(A_7312, B_7313), D_7314), A_7312) | ~r2_hidden(D_7314, k2_zfmisc_1(A_7312, B_7313)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_16082, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16078, c_16078, c_14958])).
% 8.22/2.79  tff(c_16223, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_10')=k4_xboole_0(A_13, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_16082, c_16211])).
% 8.22/2.79  tff(c_16233, plain, (![A_13]: (k4_xboole_0(A_13, '#skF_10')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_16083, c_16223])).
% 8.22/2.79  tff(c_16320, plain, (![D_7298, B_7299, A_7300]: (~r2_hidden(D_7298, B_7299) | ~r2_hidden(D_7298, k4_xboole_0(A_7300, B_7299)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_16326, plain, (![D_7298, A_13]: (~r2_hidden(D_7298, '#skF_10') | ~r2_hidden(D_7298, A_13))), inference(superposition, [status(thm), theory('equality')], [c_16233, c_16320])).
% 8.22/2.79  tff(c_16422, plain, (![B_7318, D_7319, A_7320]: (~r2_hidden('#skF_7'('#skF_10', B_7318, k2_zfmisc_1('#skF_10', B_7318), D_7319), A_7320) | ~r2_hidden(D_7319, k2_zfmisc_1('#skF_10', B_7318)))), inference(resolution, [status(thm)], [c_16392, c_16326])).
% 8.22/2.79  tff(c_16433, plain, (![D_7321, B_7322]: (~r2_hidden(D_7321, k2_zfmisc_1('#skF_10', B_7322)))), inference(resolution, [status(thm)], [c_36, c_16422])).
% 8.22/2.79  tff(c_16448, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_10'))), inference(resolution, [status(thm)], [c_30, c_16433])).
% 8.22/2.79  tff(c_16487, plain, (![E_7326]: (~r2_hidden(E_7326, '#skF_10'))), inference(splitLeft, [status(thm)], [c_16448])).
% 8.22/2.79  tff(c_16491, plain, (![B_6, C_7]: (r2_hidden('#skF_2'('#skF_10', B_6, C_7), C_7) | k4_xboole_0('#skF_10', B_6)=C_7)), inference(resolution, [status(thm)], [c_22, c_16487])).
% 8.22/2.79  tff(c_16647, plain, (![B_7344, C_7345]: (r2_hidden('#skF_2'('#skF_10', B_7344, C_7345), C_7345) | C_7345='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_16232, c_16491])).
% 8.22/2.79  tff(c_16504, plain, (![D_42, A_15]: (~r2_hidden(D_42, k2_zfmisc_1(A_15, '#skF_10')))), inference(resolution, [status(thm)], [c_34, c_16487])).
% 8.22/2.79  tff(c_16688, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_16647, c_16504])).
% 8.22/2.79  tff(c_16084, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_16078, c_14964])).
% 8.22/2.79  tff(c_16699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16688, c_16084])).
% 8.22/2.79  tff(c_16700, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_16448])).
% 8.22/2.79  tff(c_16768, plain, (![A_7351, B_7352]: (k4_xboole_0(A_7351, B_7352)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_16700, c_16700, c_22])).
% 8.22/2.79  tff(c_16738, plain, (![A_5, B_6, C_7]: (k4_xboole_0(A_5, B_6)=C_7)), inference(negUnitSimplification, [status(thm)], [c_16700, c_16700, c_22])).
% 8.22/2.79  tff(c_16910, plain, (![C_7858]: (C_7858='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_16768, c_16738])).
% 8.22/2.79  tff(c_16924, plain, ('#skF_10'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_16910, c_16080])).
% 8.22/2.79  tff(c_16952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16081, c_16924])).
% 8.22/2.79  tff(c_16954, plain, ('#skF_11'='#skF_12'), inference(splitRight, [status(thm)], [c_14981])).
% 8.22/2.79  tff(c_16956, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_12')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_16954, c_14959])).
% 8.22/2.79  tff(c_17079, plain, (![B_8440, A_8441]: (k3_xboole_0(B_8440, A_8441)=k3_xboole_0(A_8441, B_8440))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_16955, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_16954, c_16954, c_14958])).
% 8.22/2.79  tff(c_17095, plain, (![A_8441]: (k3_xboole_0('#skF_12', A_8441)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_17079, c_16955])).
% 8.22/2.79  tff(c_17167, plain, (![A_8449, B_8450]: (k5_xboole_0(A_8449, k3_xboole_0(A_8449, B_8450))=k4_xboole_0(A_8449, B_8450))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_17180, plain, (![A_8441]: (k5_xboole_0('#skF_12', '#skF_12')=k4_xboole_0('#skF_12', A_8441))), inference(superposition, [status(thm), theory('equality')], [c_17095, c_17167])).
% 8.22/2.79  tff(c_17197, plain, (![A_8441]: (k4_xboole_0('#skF_12', A_8441)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_16956, c_17180])).
% 8.22/2.79  tff(c_17304, plain, (![A_8464, B_8465, D_8466]: (r2_hidden('#skF_7'(A_8464, B_8465, k2_zfmisc_1(A_8464, B_8465), D_8466), A_8464) | ~r2_hidden(D_8466, k2_zfmisc_1(A_8464, B_8465)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_17193, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_12')=k4_xboole_0(A_13, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_16955, c_17167])).
% 8.22/2.79  tff(c_17200, plain, (![A_8451]: (k4_xboole_0(A_8451, '#skF_12')=A_8451)), inference(demodulation, [status(thm), theory('equality')], [c_16956, c_17193])).
% 8.22/2.79  tff(c_17209, plain, (![D_10, A_8451]: (~r2_hidden(D_10, '#skF_12') | ~r2_hidden(D_10, A_8451))), inference(superposition, [status(thm), theory('equality')], [c_17200, c_8])).
% 8.22/2.79  tff(c_17361, plain, (![B_8473, D_8474, A_8475]: (~r2_hidden('#skF_7'('#skF_12', B_8473, k2_zfmisc_1('#skF_12', B_8473), D_8474), A_8475) | ~r2_hidden(D_8474, k2_zfmisc_1('#skF_12', B_8473)))), inference(resolution, [status(thm)], [c_17304, c_17209])).
% 8.22/2.79  tff(c_17372, plain, (![D_8476, B_8477]: (~r2_hidden(D_8476, k2_zfmisc_1('#skF_12', B_8477)))), inference(resolution, [status(thm)], [c_36, c_17361])).
% 8.22/2.79  tff(c_17397, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_12'))), inference(resolution, [status(thm)], [c_30, c_17372])).
% 8.22/2.79  tff(c_17399, plain, (![E_8478]: (~r2_hidden(E_8478, '#skF_12'))), inference(splitLeft, [status(thm)], [c_17397])).
% 8.22/2.79  tff(c_17403, plain, (![B_6, C_7]: (r2_hidden('#skF_2'('#skF_12', B_6, C_7), C_7) | k4_xboole_0('#skF_12', B_6)=C_7)), inference(resolution, [status(thm)], [c_22, c_17399])).
% 8.22/2.79  tff(c_17605, plain, (![B_8499, C_8500]: (r2_hidden('#skF_2'('#skF_12', B_8499, C_8500), C_8500) | C_8500='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_17197, c_17403])).
% 8.22/2.79  tff(c_17416, plain, (![D_42, A_15]: (~r2_hidden(D_42, k2_zfmisc_1(A_15, '#skF_12')))), inference(resolution, [status(thm)], [c_34, c_17399])).
% 8.22/2.79  tff(c_17646, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_17605, c_17416])).
% 8.22/2.79  tff(c_16953, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_14981])).
% 8.22/2.79  tff(c_16967, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_16954, c_16954, c_16953])).
% 8.22/2.79  tff(c_16968, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_16967])).
% 8.22/2.79  tff(c_16957, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_16954, c_14964])).
% 8.22/2.79  tff(c_16991, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_16968, c_16957])).
% 8.22/2.79  tff(c_17657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17646, c_16991])).
% 8.22/2.79  tff(c_17658, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_17397])).
% 8.22/2.79  tff(c_17807, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_17658, c_17658, c_22])).
% 8.22/2.79  tff(c_17666, plain, (![A_8503, B_8504, C_8505]: (k4_xboole_0(A_8503, B_8504)=C_8505)), inference(negUnitSimplification, [status(thm)], [c_17658, c_17658, c_22])).
% 8.22/2.79  tff(c_17912, plain, (![C_10200]: (C_10200='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_17807, c_17666])).
% 8.22/2.79  tff(c_17815, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_17658, c_17658, c_22])).
% 8.22/2.79  tff(c_17866, plain, (![C_9515]: (C_9515='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_17815, c_17666])).
% 8.22/2.79  tff(c_17891, plain, ('#skF_11'!='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_17866, c_16991])).
% 8.22/2.79  tff(c_17939, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_17912, c_17891])).
% 8.22/2.79  tff(c_17941, plain, ('#skF_10'!='#skF_12'), inference(splitRight, [status(thm)], [c_16967])).
% 8.22/2.79  tff(c_18057, plain, (![B_10746, A_10747]: (k3_xboole_0(B_10746, A_10747)=k3_xboole_0(A_10747, B_10746))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.22/2.79  tff(c_18131, plain, (![A_10750]: (k3_xboole_0('#skF_12', A_10750)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_18057, c_16955])).
% 8.22/2.79  tff(c_18136, plain, (![A_10750]: (k5_xboole_0('#skF_12', '#skF_12')=k4_xboole_0('#skF_12', A_10750))), inference(superposition, [status(thm), theory('equality')], [c_18131, c_24])).
% 8.22/2.79  tff(c_18160, plain, (![A_10750]: (k4_xboole_0('#skF_12', A_10750)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_16956, c_18136])).
% 8.22/2.79  tff(c_18499, plain, (![A_10799, B_10800, C_10801]: (r2_hidden('#skF_1'(A_10799, B_10800, C_10801), A_10799) | r2_hidden('#skF_2'(A_10799, B_10800, C_10801), C_10801) | k4_xboole_0(A_10799, B_10800)=C_10801)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_18277, plain, (![A_10770, B_10771, D_10772]: (r2_hidden('#skF_7'(A_10770, B_10771, k2_zfmisc_1(A_10770, B_10771), D_10772), A_10770) | ~r2_hidden(D_10772, k2_zfmisc_1(A_10770, B_10771)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_18104, plain, (![A_10748, B_10749]: (k5_xboole_0(A_10748, k3_xboole_0(A_10748, B_10749))=k4_xboole_0(A_10748, B_10749))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.22/2.79  tff(c_18127, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_12')=k4_xboole_0(A_13, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_16955, c_18104])).
% 8.22/2.79  tff(c_18130, plain, (![A_13]: (k4_xboole_0(A_13, '#skF_12')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_16956, c_18127])).
% 8.22/2.79  tff(c_18200, plain, (![D_10753, B_10754, A_10755]: (~r2_hidden(D_10753, B_10754) | ~r2_hidden(D_10753, k4_xboole_0(A_10755, B_10754)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.79  tff(c_18206, plain, (![D_10753, A_13]: (~r2_hidden(D_10753, '#skF_12') | ~r2_hidden(D_10753, A_13))), inference(superposition, [status(thm), theory('equality')], [c_18130, c_18200])).
% 8.22/2.79  tff(c_18333, plain, (![B_10779, D_10780, A_10781]: (~r2_hidden('#skF_7'('#skF_12', B_10779, k2_zfmisc_1('#skF_12', B_10779), D_10780), A_10781) | ~r2_hidden(D_10780, k2_zfmisc_1('#skF_12', B_10779)))), inference(resolution, [status(thm)], [c_18277, c_18206])).
% 8.22/2.79  tff(c_18344, plain, (![D_10782, B_10783]: (~r2_hidden(D_10782, k2_zfmisc_1('#skF_12', B_10783)))), inference(resolution, [status(thm)], [c_36, c_18333])).
% 8.22/2.79  tff(c_18369, plain, (![F_48, B_16, E_47]: (~r2_hidden(F_48, B_16) | ~r2_hidden(E_47, '#skF_12'))), inference(resolution, [status(thm)], [c_30, c_18344])).
% 8.22/2.79  tff(c_18370, plain, (![E_47]: (~r2_hidden(E_47, '#skF_12'))), inference(splitLeft, [status(thm)], [c_18369])).
% 8.22/2.79  tff(c_18519, plain, (![B_10800, C_10801]: (r2_hidden('#skF_2'('#skF_12', B_10800, C_10801), C_10801) | k4_xboole_0('#skF_12', B_10800)=C_10801)), inference(resolution, [status(thm)], [c_18499, c_18370])).
% 8.22/2.79  tff(c_18619, plain, (![B_10805, C_10806]: (r2_hidden('#skF_2'('#skF_12', B_10805, C_10806), C_10806) | C_10806='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_18160, c_18519])).
% 8.22/2.79  tff(c_18342, plain, (![D_42, B_16]: (~r2_hidden(D_42, k2_zfmisc_1('#skF_12', B_16)))), inference(resolution, [status(thm)], [c_36, c_18333])).
% 8.22/2.79  tff(c_18663, plain, (![B_16]: (k2_zfmisc_1('#skF_12', B_16)='#skF_12')), inference(resolution, [status(thm)], [c_18619, c_18342])).
% 8.22/2.79  tff(c_17940, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_16967])).
% 8.22/2.79  tff(c_17962, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_17940, c_16957])).
% 8.22/2.79  tff(c_18717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18663, c_17962])).
% 8.22/2.79  tff(c_18718, plain, (![F_48, B_16]: (~r2_hidden(F_48, B_16))), inference(splitRight, [status(thm)], [c_18369])).
% 8.22/2.79  tff(c_52, plain, (![A_15, B_16, C_17]: (r2_hidden('#skF_4'(A_15, B_16, C_17), A_15) | r2_hidden('#skF_6'(A_15, B_16, C_17), C_17) | k2_zfmisc_1(A_15, B_16)=C_17)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/2.79  tff(c_18737, plain, (![A_10813, B_10814]: (k2_zfmisc_1(A_10813, B_10814)='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_18718, c_18718, c_52])).
% 8.22/2.79  tff(c_18719, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(A_15, B_16)=C_17)), inference(negUnitSimplification, [status(thm)], [c_18718, c_18718, c_52])).
% 8.22/2.79  tff(c_18907, plain, (![C_11464]: (C_11464='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_18737, c_18719])).
% 8.22/2.79  tff(c_18921, plain, ('#skF_10'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_18907, c_18160])).
% 8.22/2.79  tff(c_18959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17941, c_18921])).
% 8.22/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.79  
% 8.22/2.79  Inference rules
% 8.22/2.79  ----------------------
% 8.22/2.79  #Ref     : 0
% 8.22/2.79  #Sup     : 4240
% 8.22/2.79  #Fact    : 0
% 8.22/2.79  #Define  : 0
% 8.22/2.79  #Split   : 21
% 8.22/2.79  #Chain   : 0
% 8.22/2.79  #Close   : 0
% 8.22/2.79  
% 8.22/2.79  Ordering : KBO
% 8.22/2.79  
% 8.22/2.79  Simplification rules
% 8.22/2.79  ----------------------
% 8.22/2.79  #Subsume      : 1425
% 8.22/2.79  #Demod        : 1125
% 8.22/2.79  #Tautology    : 1018
% 8.22/2.79  #SimpNegUnit  : 171
% 8.22/2.79  #BackRed      : 218
% 8.22/2.79  
% 8.22/2.79  #Partial instantiations: 2863
% 8.22/2.79  #Strategies tried      : 1
% 8.22/2.79  
% 8.22/2.79  Timing (in seconds)
% 8.22/2.79  ----------------------
% 8.22/2.79  Preprocessing        : 0.31
% 8.22/2.79  Parsing              : 0.16
% 8.22/2.79  CNF conversion       : 0.03
% 8.22/2.79  Main loop            : 1.60
% 8.22/2.79  Inferencing          : 0.66
% 8.22/2.79  Reduction            : 0.47
% 8.22/2.79  Demodulation         : 0.30
% 8.22/2.79  BG Simplification    : 0.07
% 8.22/2.79  Subsumption          : 0.25
% 8.22/2.79  Abstraction          : 0.08
% 8.22/2.79  MUC search           : 0.00
% 8.22/2.79  Cooper               : 0.00
% 8.22/2.79  Total                : 2.04
% 8.22/2.79  Index Insertion      : 0.00
% 8.22/2.79  Index Deletion       : 0.00
% 8.22/2.79  Index Matching       : 0.00
% 8.22/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
