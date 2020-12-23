%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:42 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :  168 (1144 expanded)
%              Number of leaves         :   33 ( 343 expanded)
%              Depth                    :   12
%              Number of atoms          :  211 (2208 expanded)
%              Number of equality atoms :  114 (1767 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_15 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_17090,plain,(
    ! [A_1134,B_1135,C_1136] :
      ( r2_hidden('#skF_4'(A_1134,B_1135,C_1136),B_1135)
      | r2_hidden('#skF_5'(A_1134,B_1135,C_1136),C_1136)
      | k2_zfmisc_1(A_1134,B_1135) = C_1136 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14180,plain,(
    ! [A_959,B_960,C_961] :
      ( r2_hidden('#skF_4'(A_959,B_960,C_961),B_960)
      | r2_hidden('#skF_5'(A_959,B_960,C_961),C_961)
      | k2_zfmisc_1(A_959,B_960) = C_961 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11770,plain,(
    ! [A_817,B_818,C_819] :
      ( r2_hidden('#skF_3'(A_817,B_818,C_819),A_817)
      | r2_hidden('#skF_5'(A_817,B_818,C_819),C_819)
      | k2_zfmisc_1(A_817,B_818) = C_819 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7549,plain,(
    ! [A_570,B_571,C_572] :
      ( r2_hidden('#skF_4'(A_570,B_571,C_572),B_571)
      | r2_hidden('#skF_5'(A_570,B_571,C_572),C_572)
      | k2_zfmisc_1(A_570,B_571) = C_572 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5062,plain,(
    ! [A_415,B_416,C_417] :
      ( r2_hidden('#skF_3'(A_415,B_416,C_417),A_415)
      | r2_hidden('#skF_5'(A_415,B_416,C_417),C_417)
      | k2_zfmisc_1(A_415,B_416) = C_417 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1720,plain,(
    ! [A_210,B_211,C_212] :
      ( r2_hidden('#skF_4'(A_210,B_211,C_212),B_211)
      | r2_hidden('#skF_5'(A_210,B_211,C_212),C_212)
      | k2_zfmisc_1(A_210,B_211) = C_212 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_9'(A_45,B_46),A_45)
      | r2_hidden('#skF_10'(A_45,B_46),B_46)
      | k3_tarski(A_45) = B_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_65,B_66] : r1_xboole_0(k4_xboole_0(A_65,B_66),B_66) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_90,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [B_69] : k3_xboole_0(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_142,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [B_69,C_75] :
      ( ~ r1_xboole_0(k1_xboole_0,B_69)
      | ~ r2_hidden(C_75,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_142])).

tff(c_147,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_145])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_542,plain,(
    ! [E_114,F_115,A_116,B_117] :
      ( r2_hidden(k4_tarski(E_114,F_115),k2_zfmisc_1(A_116,B_117))
      | ~ r2_hidden(F_115,B_117)
      | ~ r2_hidden(E_114,A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_547,plain,(
    ! [E_114,F_115] :
      ( r2_hidden(k4_tarski(E_114,F_115),k1_xboole_0)
      | ~ r2_hidden(F_115,'#skF_15')
      | ~ r2_hidden(E_114,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_542])).

tff(c_549,plain,(
    ! [F_115,E_114] :
      ( ~ r2_hidden(F_115,'#skF_15')
      | ~ r2_hidden(E_114,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_547])).

tff(c_551,plain,(
    ! [E_118] : ~ r2_hidden(E_118,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_588,plain,(
    ! [A_119] :
      ( r2_hidden('#skF_9'(A_119,'#skF_14'),A_119)
      | k3_tarski(A_119) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_50,c_551])).

tff(c_550,plain,(
    ! [E_114] : ~ r2_hidden(E_114,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_615,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_588,c_550])).

tff(c_267,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_9'(A_96,B_97),A_96)
      | r2_hidden('#skF_10'(A_96,B_97),B_97)
      | k3_tarski(A_96) = B_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_308,plain,(
    ! [A_96] :
      ( r2_hidden('#skF_9'(A_96,k1_xboole_0),A_96)
      | k3_tarski(A_96) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_267,c_147])).

tff(c_571,plain,(
    k3_tarski('#skF_14') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_308,c_551])).

tff(c_660,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_571])).

tff(c_662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_660])).

tff(c_664,plain,(
    ! [F_123] : ~ r2_hidden(F_123,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_701,plain,(
    ! [A_124] :
      ( r2_hidden('#skF_9'(A_124,'#skF_15'),A_124)
      | k3_tarski(A_124) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_50,c_664])).

tff(c_663,plain,(
    ! [F_115] : ~ r2_hidden(F_115,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_728,plain,(
    k3_tarski('#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_701,c_663])).

tff(c_684,plain,(
    k3_tarski('#skF_15') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_308,c_664])).

tff(c_735,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_684])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_735])).

tff(c_738,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_740,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_743,plain,(
    ! [A_8] : r1_xboole_0('#skF_13',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_81])).

tff(c_770,plain,(
    ! [A_130,B_131] : k4_xboole_0(A_130,k4_xboole_0(A_130,B_131)) = k3_xboole_0(A_130,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_744,plain,(
    ! [A_8] : k4_xboole_0('#skF_13',A_8) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_8])).

tff(c_800,plain,(
    ! [B_132] : k3_xboole_0('#skF_13',B_132) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_744])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_805,plain,(
    ! [B_132,C_5] :
      ( ~ r1_xboole_0('#skF_13',B_132)
      | ~ r2_hidden(C_5,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_4])).

tff(c_810,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_805])).

tff(c_3385,plain,(
    ! [A_294,C_295] :
      ( r2_hidden('#skF_5'(A_294,'#skF_13',C_295),C_295)
      | k2_zfmisc_1(A_294,'#skF_13') = C_295 ) ),
    inference(resolution,[status(thm)],[c_1720,c_810])).

tff(c_3497,plain,(
    ! [A_294] : k2_zfmisc_1(A_294,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_3385,c_810])).

tff(c_64,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_766,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13'
    | k2_zfmisc_1('#skF_14','#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_64])).

tff(c_767,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_3535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3497,c_767])).

tff(c_3536,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_739,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3536,c_740,c_739])).

tff(c_3548,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_3552,plain,(
    ! [A_8] : r1_xboole_0('#skF_12',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_81])).

tff(c_3579,plain,(
    ! [A_301,B_302] : k4_xboole_0(A_301,k4_xboole_0(A_301,B_302)) = k3_xboole_0(A_301,B_302) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3553,plain,(
    ! [A_8] : k4_xboole_0('#skF_12',A_8) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_3548,c_8])).

tff(c_3589,plain,(
    ! [B_302] : k3_xboole_0('#skF_12',B_302) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_3579,c_3553])).

tff(c_3630,plain,(
    ! [A_306,B_307,C_308] :
      ( ~ r1_xboole_0(A_306,B_307)
      | ~ r2_hidden(C_308,k3_xboole_0(A_306,B_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3633,plain,(
    ! [B_302,C_308] :
      ( ~ r1_xboole_0('#skF_12',B_302)
      | ~ r2_hidden(C_308,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3589,c_3630])).

tff(c_3635,plain,(
    ! [C_308] : ~ r2_hidden(C_308,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3552,c_3633])).

tff(c_6208,plain,(
    ! [A_471,B_472] :
      ( r2_hidden('#skF_3'(A_471,B_472,'#skF_12'),A_471)
      | k2_zfmisc_1(A_471,B_472) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_5062,c_3635])).

tff(c_6319,plain,(
    ! [B_472] : k2_zfmisc_1('#skF_12',B_472) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6208,c_3635])).

tff(c_3564,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_739])).

tff(c_3577,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12'
    | k2_zfmisc_1('#skF_14','#skF_15') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_3548,c_64])).

tff(c_3578,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_3564,c_3577])).

tff(c_6345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6319,c_3578])).

tff(c_6347,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6346,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6361,plain,
    ( '#skF_14' = '#skF_12'
    | '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6347,c_6347,c_6346])).

tff(c_6362,plain,(
    '#skF_14' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_6361])).

tff(c_6349,plain,(
    ! [A_8] : r1_xboole_0('#skF_14',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6347,c_81])).

tff(c_6364,plain,(
    ! [A_8] : r1_xboole_0('#skF_13',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_6349])).

tff(c_6398,plain,(
    ! [A_479,B_480] : k4_xboole_0(A_479,k4_xboole_0(A_479,B_480)) = k3_xboole_0(A_479,B_480) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6350,plain,(
    ! [A_8] : k4_xboole_0('#skF_14',A_8) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6347,c_6347,c_8])).

tff(c_6381,plain,(
    ! [A_8] : k4_xboole_0('#skF_13',A_8) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_6362,c_6350])).

tff(c_6428,plain,(
    ! [B_481] : k3_xboole_0('#skF_13',B_481) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_6398,c_6381])).

tff(c_6433,plain,(
    ! [B_481,C_5] :
      ( ~ r1_xboole_0('#skF_13',B_481)
      | ~ r2_hidden(C_5,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6428,c_4])).

tff(c_6438,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6364,c_6433])).

tff(c_9800,plain,(
    ! [A_673,C_674] :
      ( r2_hidden('#skF_5'(A_673,'#skF_13',C_674),C_674)
      | k2_zfmisc_1(A_673,'#skF_13') = C_674 ) ),
    inference(resolution,[status(thm)],[c_7549,c_6438])).

tff(c_9857,plain,(
    ! [A_673] : k2_zfmisc_1(A_673,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_9800,c_6438])).

tff(c_6367,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_6347])).

tff(c_60,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6394,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6367,c_6362,c_6367,c_60])).

tff(c_9875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9857,c_6394])).

tff(c_9876,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_6361])).

tff(c_9878,plain,(
    ! [A_8] : r1_xboole_0('#skF_12',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_6349])).

tff(c_9916,plain,(
    ! [A_680,B_681] : k4_xboole_0(A_680,k4_xboole_0(A_680,B_681)) = k3_xboole_0(A_680,B_681) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9897,plain,(
    ! [A_8] : k4_xboole_0('#skF_12',A_8) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_6350])).

tff(c_9946,plain,(
    ! [B_682] : k3_xboole_0('#skF_12',B_682) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_9916,c_9897])).

tff(c_9951,plain,(
    ! [B_682,C_5] :
      ( ~ r1_xboole_0('#skF_12',B_682)
      | ~ r2_hidden(C_5,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9946,c_4])).

tff(c_9956,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9878,c_9951])).

tff(c_12567,plain,(
    ! [A_846,B_847] :
      ( r2_hidden('#skF_3'(A_846,B_847,'#skF_12'),A_846)
      | k2_zfmisc_1(A_846,B_847) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_11770,c_9956])).

tff(c_12679,plain,(
    ! [B_847] : k2_zfmisc_1('#skF_12',B_847) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_12567,c_9956])).

tff(c_9881,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_6347])).

tff(c_9911,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9881,c_9876,c_9881,c_60])).

tff(c_12716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12679,c_9911])).

tff(c_12718,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_12717,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_12733,plain,
    ( '#skF_15' = '#skF_12'
    | '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12718,c_12717])).

tff(c_12734,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_12733])).

tff(c_12719,plain,(
    ! [A_8] : r1_xboole_0('#skF_15',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_81])).

tff(c_12735,plain,(
    ! [A_8] : r1_xboole_0('#skF_13',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12734,c_12719])).

tff(c_12769,plain,(
    ! [A_857,B_858] : k4_xboole_0(A_857,k4_xboole_0(A_857,B_858)) = k3_xboole_0(A_857,B_858) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12720,plain,(
    ! [A_8] : k4_xboole_0('#skF_15',A_8) = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12718,c_8])).

tff(c_12751,plain,(
    ! [A_8] : k4_xboole_0('#skF_13',A_8) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12734,c_12734,c_12720])).

tff(c_12800,plain,(
    ! [B_862] : k3_xboole_0('#skF_13',B_862) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_12769,c_12751])).

tff(c_12805,plain,(
    ! [B_862,C_5] :
      ( ~ r1_xboole_0('#skF_13',B_862)
      | ~ r2_hidden(C_5,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12800,c_4])).

tff(c_12810,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12735,c_12805])).

tff(c_15667,plain,(
    ! [A_1034,C_1035] :
      ( r2_hidden('#skF_5'(A_1034,'#skF_13',C_1035),C_1035)
      | k2_zfmisc_1(A_1034,'#skF_13') = C_1035 ) ),
    inference(resolution,[status(thm)],[c_14180,c_12810])).

tff(c_15778,plain,(
    ! [A_1034] : k2_zfmisc_1(A_1034,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_15667,c_12810])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12731,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12718,c_12718,c_56])).

tff(c_12736,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12734,c_12731])).

tff(c_15805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15778,c_12736])).

tff(c_15806,plain,(
    '#skF_15' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_12733])).

tff(c_15808,plain,(
    ! [A_8] : r1_xboole_0('#skF_12',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15806,c_12719])).

tff(c_15843,plain,(
    ! [A_1038,B_1039] : k4_xboole_0(A_1038,k4_xboole_0(A_1038,B_1039)) = k3_xboole_0(A_1038,B_1039) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15826,plain,(
    ! [A_8] : k4_xboole_0('#skF_12',A_8) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15806,c_15806,c_12720])).

tff(c_15874,plain,(
    ! [B_1043] : k3_xboole_0('#skF_12',B_1043) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_15843,c_15826])).

tff(c_15879,plain,(
    ! [B_1043,C_5] :
      ( ~ r1_xboole_0('#skF_12',B_1043)
      | ~ r2_hidden(C_5,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15874,c_4])).

tff(c_15884,plain,(
    ! [C_5] : ~ r2_hidden(C_5,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15808,c_15879])).

tff(c_18559,plain,(
    ! [A_1222,C_1223] :
      ( r2_hidden('#skF_5'(A_1222,'#skF_12',C_1223),C_1223)
      | k2_zfmisc_1(A_1222,'#skF_12') = C_1223 ) ),
    inference(resolution,[status(thm)],[c_17090,c_15884])).

tff(c_18671,plain,(
    ! [A_1222] : k2_zfmisc_1(A_1222,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_18559,c_15884])).

tff(c_16439,plain,(
    ! [A_1097,B_1098,D_1099] :
      ( r2_hidden('#skF_6'(A_1097,B_1098,k2_zfmisc_1(A_1097,B_1098),D_1099),A_1097)
      | ~ r2_hidden(D_1099,k2_zfmisc_1(A_1097,B_1098)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16491,plain,(
    ! [D_1099,B_1098] : ~ r2_hidden(D_1099,k2_zfmisc_1('#skF_12',B_1098)) ),
    inference(resolution,[status(thm)],[c_16439,c_15884])).

tff(c_18663,plain,(
    ! [A_1222,B_1098] : k2_zfmisc_1(A_1222,'#skF_12') = k2_zfmisc_1('#skF_12',B_1098) ),
    inference(resolution,[status(thm)],[c_18559,c_16491])).

tff(c_18818,plain,(
    ! [B_1098] : k2_zfmisc_1('#skF_12',B_1098) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18671,c_18663])).

tff(c_15809,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15806,c_12731])).

tff(c_18846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18818,c_15809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:33:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.05/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.72  
% 8.05/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.73  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_15 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_11 > #skF_3 > #skF_1 > #skF_9 > #skF_12
% 8.05/2.73  
% 8.05/2.73  %Foreground sorts:
% 8.05/2.73  
% 8.05/2.73  
% 8.05/2.73  %Background operators:
% 8.05/2.73  
% 8.05/2.73  
% 8.05/2.73  %Foreground operators:
% 8.05/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.05/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.05/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.05/2.73  tff('#skF_15', type, '#skF_15': $i).
% 8.05/2.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.05/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.05/2.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.05/2.73  tff('#skF_14', type, '#skF_14': $i).
% 8.05/2.73  tff('#skF_13', type, '#skF_13': $i).
% 8.05/2.73  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.05/2.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.05/2.73  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 8.05/2.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.05/2.73  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 8.05/2.73  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.05/2.73  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.05/2.73  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 8.05/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.05/2.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.05/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.05/2.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.05/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.05/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.05/2.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.05/2.73  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.05/2.73  tff('#skF_12', type, '#skF_12': $i).
% 8.05/2.73  
% 8.05/2.75  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.05/2.75  tff(f_75, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.05/2.75  tff(f_67, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 8.05/2.75  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 8.05/2.75  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.05/2.75  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.05/2.75  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.05/2.75  tff(c_17090, plain, (![A_1134, B_1135, C_1136]: (r2_hidden('#skF_4'(A_1134, B_1135, C_1136), B_1135) | r2_hidden('#skF_5'(A_1134, B_1135, C_1136), C_1136) | k2_zfmisc_1(A_1134, B_1135)=C_1136)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_14180, plain, (![A_959, B_960, C_961]: (r2_hidden('#skF_4'(A_959, B_960, C_961), B_960) | r2_hidden('#skF_5'(A_959, B_960, C_961), C_961) | k2_zfmisc_1(A_959, B_960)=C_961)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_11770, plain, (![A_817, B_818, C_819]: (r2_hidden('#skF_3'(A_817, B_818, C_819), A_817) | r2_hidden('#skF_5'(A_817, B_818, C_819), C_819) | k2_zfmisc_1(A_817, B_818)=C_819)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_7549, plain, (![A_570, B_571, C_572]: (r2_hidden('#skF_4'(A_570, B_571, C_572), B_571) | r2_hidden('#skF_5'(A_570, B_571, C_572), C_572) | k2_zfmisc_1(A_570, B_571)=C_572)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_5062, plain, (![A_415, B_416, C_417]: (r2_hidden('#skF_3'(A_415, B_416, C_417), A_415) | r2_hidden('#skF_5'(A_415, B_416, C_417), C_417) | k2_zfmisc_1(A_415, B_416)=C_417)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_1720, plain, (![A_210, B_211, C_212]: (r2_hidden('#skF_4'(A_210, B_211, C_212), B_211) | r2_hidden('#skF_5'(A_210, B_211, C_212), C_212) | k2_zfmisc_1(A_210, B_211)=C_212)), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_58, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.05/2.75  tff(c_83, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_58])).
% 8.05/2.75  tff(c_50, plain, (![A_45, B_46]: (r2_hidden('#skF_9'(A_45, B_46), A_45) | r2_hidden('#skF_10'(A_45, B_46), B_46) | k3_tarski(A_45)=B_46)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.05/2.75  tff(c_62, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.05/2.75  tff(c_84, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_62])).
% 8.05/2.75  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.05/2.75  tff(c_78, plain, (![A_65, B_66]: (r1_xboole_0(k4_xboole_0(A_65, B_66), B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.05/2.75  tff(c_81, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_78])).
% 8.05/2.75  tff(c_90, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_103, plain, (![B_69]: (k3_xboole_0(k1_xboole_0, B_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_8])).
% 8.05/2.75  tff(c_142, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.05/2.75  tff(c_145, plain, (![B_69, C_75]: (~r1_xboole_0(k1_xboole_0, B_69) | ~r2_hidden(C_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_142])).
% 8.05/2.75  tff(c_147, plain, (![C_75]: (~r2_hidden(C_75, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_145])).
% 8.05/2.75  tff(c_66, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.05/2.75  tff(c_85, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 8.05/2.75  tff(c_542, plain, (![E_114, F_115, A_116, B_117]: (r2_hidden(k4_tarski(E_114, F_115), k2_zfmisc_1(A_116, B_117)) | ~r2_hidden(F_115, B_117) | ~r2_hidden(E_114, A_116))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_547, plain, (![E_114, F_115]: (r2_hidden(k4_tarski(E_114, F_115), k1_xboole_0) | ~r2_hidden(F_115, '#skF_15') | ~r2_hidden(E_114, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_542])).
% 8.05/2.75  tff(c_549, plain, (![F_115, E_114]: (~r2_hidden(F_115, '#skF_15') | ~r2_hidden(E_114, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_147, c_547])).
% 8.05/2.75  tff(c_551, plain, (![E_118]: (~r2_hidden(E_118, '#skF_14'))), inference(splitLeft, [status(thm)], [c_549])).
% 8.05/2.75  tff(c_588, plain, (![A_119]: (r2_hidden('#skF_9'(A_119, '#skF_14'), A_119) | k3_tarski(A_119)='#skF_14')), inference(resolution, [status(thm)], [c_50, c_551])).
% 8.05/2.75  tff(c_550, plain, (![E_114]: (~r2_hidden(E_114, '#skF_14'))), inference(splitLeft, [status(thm)], [c_549])).
% 8.05/2.75  tff(c_615, plain, (k3_tarski('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_588, c_550])).
% 8.05/2.75  tff(c_267, plain, (![A_96, B_97]: (r2_hidden('#skF_9'(A_96, B_97), A_96) | r2_hidden('#skF_10'(A_96, B_97), B_97) | k3_tarski(A_96)=B_97)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.05/2.75  tff(c_308, plain, (![A_96]: (r2_hidden('#skF_9'(A_96, k1_xboole_0), A_96) | k3_tarski(A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_267, c_147])).
% 8.05/2.75  tff(c_571, plain, (k3_tarski('#skF_14')=k1_xboole_0), inference(resolution, [status(thm)], [c_308, c_551])).
% 8.05/2.75  tff(c_660, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_615, c_571])).
% 8.05/2.75  tff(c_662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_660])).
% 8.05/2.75  tff(c_664, plain, (![F_123]: (~r2_hidden(F_123, '#skF_15'))), inference(splitRight, [status(thm)], [c_549])).
% 8.05/2.75  tff(c_701, plain, (![A_124]: (r2_hidden('#skF_9'(A_124, '#skF_15'), A_124) | k3_tarski(A_124)='#skF_15')), inference(resolution, [status(thm)], [c_50, c_664])).
% 8.05/2.75  tff(c_663, plain, (![F_115]: (~r2_hidden(F_115, '#skF_15'))), inference(splitRight, [status(thm)], [c_549])).
% 8.05/2.75  tff(c_728, plain, (k3_tarski('#skF_15')='#skF_15'), inference(resolution, [status(thm)], [c_701, c_663])).
% 8.05/2.75  tff(c_684, plain, (k3_tarski('#skF_15')=k1_xboole_0), inference(resolution, [status(thm)], [c_308, c_664])).
% 8.05/2.75  tff(c_735, plain, (k1_xboole_0='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_728, c_684])).
% 8.05/2.75  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_735])).
% 8.05/2.75  tff(c_738, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_66])).
% 8.05/2.75  tff(c_740, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_738])).
% 8.05/2.75  tff(c_743, plain, (![A_8]: (r1_xboole_0('#skF_13', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_740, c_81])).
% 8.05/2.75  tff(c_770, plain, (![A_130, B_131]: (k4_xboole_0(A_130, k4_xboole_0(A_130, B_131))=k3_xboole_0(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_744, plain, (![A_8]: (k4_xboole_0('#skF_13', A_8)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_8])).
% 8.05/2.75  tff(c_800, plain, (![B_132]: (k3_xboole_0('#skF_13', B_132)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_770, c_744])).
% 8.05/2.75  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.05/2.75  tff(c_805, plain, (![B_132, C_5]: (~r1_xboole_0('#skF_13', B_132) | ~r2_hidden(C_5, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_800, c_4])).
% 8.05/2.75  tff(c_810, plain, (![C_5]: (~r2_hidden(C_5, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_743, c_805])).
% 8.05/2.75  tff(c_3385, plain, (![A_294, C_295]: (r2_hidden('#skF_5'(A_294, '#skF_13', C_295), C_295) | k2_zfmisc_1(A_294, '#skF_13')=C_295)), inference(resolution, [status(thm)], [c_1720, c_810])).
% 8.05/2.75  tff(c_3497, plain, (![A_294]: (k2_zfmisc_1(A_294, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_3385, c_810])).
% 8.05/2.75  tff(c_64, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.05/2.75  tff(c_766, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13' | k2_zfmisc_1('#skF_14', '#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_64])).
% 8.05/2.75  tff(c_767, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(splitLeft, [status(thm)], [c_766])).
% 8.05/2.75  tff(c_3535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3497, c_767])).
% 8.05/2.75  tff(c_3536, plain, (k2_zfmisc_1('#skF_14', '#skF_15')='#skF_13'), inference(splitRight, [status(thm)], [c_766])).
% 8.05/2.75  tff(c_739, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 8.05/2.75  tff(c_3547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3536, c_740, c_739])).
% 8.05/2.75  tff(c_3548, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_738])).
% 8.05/2.75  tff(c_3552, plain, (![A_8]: (r1_xboole_0('#skF_12', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_81])).
% 8.05/2.75  tff(c_3579, plain, (![A_301, B_302]: (k4_xboole_0(A_301, k4_xboole_0(A_301, B_302))=k3_xboole_0(A_301, B_302))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_3553, plain, (![A_8]: (k4_xboole_0('#skF_12', A_8)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_3548, c_8])).
% 8.05/2.75  tff(c_3589, plain, (![B_302]: (k3_xboole_0('#skF_12', B_302)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_3579, c_3553])).
% 8.05/2.75  tff(c_3630, plain, (![A_306, B_307, C_308]: (~r1_xboole_0(A_306, B_307) | ~r2_hidden(C_308, k3_xboole_0(A_306, B_307)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.05/2.75  tff(c_3633, plain, (![B_302, C_308]: (~r1_xboole_0('#skF_12', B_302) | ~r2_hidden(C_308, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3589, c_3630])).
% 8.05/2.75  tff(c_3635, plain, (![C_308]: (~r2_hidden(C_308, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3552, c_3633])).
% 8.05/2.75  tff(c_6208, plain, (![A_471, B_472]: (r2_hidden('#skF_3'(A_471, B_472, '#skF_12'), A_471) | k2_zfmisc_1(A_471, B_472)='#skF_12')), inference(resolution, [status(thm)], [c_5062, c_3635])).
% 8.05/2.75  tff(c_6319, plain, (![B_472]: (k2_zfmisc_1('#skF_12', B_472)='#skF_12')), inference(resolution, [status(thm)], [c_6208, c_3635])).
% 8.05/2.75  tff(c_3564, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_739])).
% 8.05/2.75  tff(c_3577, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12' | k2_zfmisc_1('#skF_14', '#skF_15')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_3548, c_64])).
% 8.05/2.75  tff(c_3578, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_3564, c_3577])).
% 8.05/2.75  tff(c_6345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6319, c_3578])).
% 8.05/2.75  tff(c_6347, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_62])).
% 8.05/2.75  tff(c_6346, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_62])).
% 8.05/2.75  tff(c_6361, plain, ('#skF_14'='#skF_12' | '#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6347, c_6347, c_6346])).
% 8.05/2.75  tff(c_6362, plain, ('#skF_14'='#skF_13'), inference(splitLeft, [status(thm)], [c_6361])).
% 8.05/2.75  tff(c_6349, plain, (![A_8]: (r1_xboole_0('#skF_14', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_6347, c_81])).
% 8.05/2.75  tff(c_6364, plain, (![A_8]: (r1_xboole_0('#skF_13', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_6349])).
% 8.05/2.75  tff(c_6398, plain, (![A_479, B_480]: (k4_xboole_0(A_479, k4_xboole_0(A_479, B_480))=k3_xboole_0(A_479, B_480))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_6350, plain, (![A_8]: (k4_xboole_0('#skF_14', A_8)='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_6347, c_6347, c_8])).
% 8.05/2.75  tff(c_6381, plain, (![A_8]: (k4_xboole_0('#skF_13', A_8)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_6362, c_6350])).
% 8.05/2.75  tff(c_6428, plain, (![B_481]: (k3_xboole_0('#skF_13', B_481)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_6398, c_6381])).
% 8.05/2.75  tff(c_6433, plain, (![B_481, C_5]: (~r1_xboole_0('#skF_13', B_481) | ~r2_hidden(C_5, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_6428, c_4])).
% 8.05/2.75  tff(c_6438, plain, (![C_5]: (~r2_hidden(C_5, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_6364, c_6433])).
% 8.05/2.75  tff(c_9800, plain, (![A_673, C_674]: (r2_hidden('#skF_5'(A_673, '#skF_13', C_674), C_674) | k2_zfmisc_1(A_673, '#skF_13')=C_674)), inference(resolution, [status(thm)], [c_7549, c_6438])).
% 8.05/2.75  tff(c_9857, plain, (![A_673]: (k2_zfmisc_1(A_673, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_9800, c_6438])).
% 8.05/2.75  tff(c_6367, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_6347])).
% 8.05/2.75  tff(c_60, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.05/2.75  tff(c_6394, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6367, c_6362, c_6367, c_60])).
% 8.05/2.75  tff(c_9875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9857, c_6394])).
% 8.05/2.75  tff(c_9876, plain, ('#skF_14'='#skF_12'), inference(splitRight, [status(thm)], [c_6361])).
% 8.05/2.75  tff(c_9878, plain, (![A_8]: (r1_xboole_0('#skF_12', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_6349])).
% 8.05/2.75  tff(c_9916, plain, (![A_680, B_681]: (k4_xboole_0(A_680, k4_xboole_0(A_680, B_681))=k3_xboole_0(A_680, B_681))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_9897, plain, (![A_8]: (k4_xboole_0('#skF_12', A_8)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_6350])).
% 8.05/2.75  tff(c_9946, plain, (![B_682]: (k3_xboole_0('#skF_12', B_682)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_9916, c_9897])).
% 8.05/2.75  tff(c_9951, plain, (![B_682, C_5]: (~r1_xboole_0('#skF_12', B_682) | ~r2_hidden(C_5, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_9946, c_4])).
% 8.05/2.75  tff(c_9956, plain, (![C_5]: (~r2_hidden(C_5, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_9878, c_9951])).
% 8.05/2.75  tff(c_12567, plain, (![A_846, B_847]: (r2_hidden('#skF_3'(A_846, B_847, '#skF_12'), A_846) | k2_zfmisc_1(A_846, B_847)='#skF_12')), inference(resolution, [status(thm)], [c_11770, c_9956])).
% 8.05/2.75  tff(c_12679, plain, (![B_847]: (k2_zfmisc_1('#skF_12', B_847)='#skF_12')), inference(resolution, [status(thm)], [c_12567, c_9956])).
% 8.05/2.75  tff(c_9881, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_6347])).
% 8.05/2.75  tff(c_9911, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9881, c_9876, c_9881, c_60])).
% 8.05/2.75  tff(c_12716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12679, c_9911])).
% 8.05/2.75  tff(c_12718, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_58])).
% 8.05/2.75  tff(c_12717, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_58])).
% 8.05/2.75  tff(c_12733, plain, ('#skF_15'='#skF_12' | '#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12718, c_12717])).
% 8.05/2.75  tff(c_12734, plain, ('#skF_15'='#skF_13'), inference(splitLeft, [status(thm)], [c_12733])).
% 8.05/2.75  tff(c_12719, plain, (![A_8]: (r1_xboole_0('#skF_15', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_81])).
% 8.05/2.75  tff(c_12735, plain, (![A_8]: (r1_xboole_0('#skF_13', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_12734, c_12719])).
% 8.05/2.75  tff(c_12769, plain, (![A_857, B_858]: (k4_xboole_0(A_857, k4_xboole_0(A_857, B_858))=k3_xboole_0(A_857, B_858))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_12720, plain, (![A_8]: (k4_xboole_0('#skF_15', A_8)='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12718, c_8])).
% 8.05/2.75  tff(c_12751, plain, (![A_8]: (k4_xboole_0('#skF_13', A_8)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12734, c_12734, c_12720])).
% 8.05/2.75  tff(c_12800, plain, (![B_862]: (k3_xboole_0('#skF_13', B_862)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_12769, c_12751])).
% 8.05/2.75  tff(c_12805, plain, (![B_862, C_5]: (~r1_xboole_0('#skF_13', B_862) | ~r2_hidden(C_5, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_12800, c_4])).
% 8.05/2.75  tff(c_12810, plain, (![C_5]: (~r2_hidden(C_5, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_12735, c_12805])).
% 8.05/2.75  tff(c_15667, plain, (![A_1034, C_1035]: (r2_hidden('#skF_5'(A_1034, '#skF_13', C_1035), C_1035) | k2_zfmisc_1(A_1034, '#skF_13')=C_1035)), inference(resolution, [status(thm)], [c_14180, c_12810])).
% 8.05/2.75  tff(c_15778, plain, (![A_1034]: (k2_zfmisc_1(A_1034, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_15667, c_12810])).
% 8.05/2.75  tff(c_56, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.05/2.75  tff(c_12731, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_12718, c_12718, c_56])).
% 8.05/2.75  tff(c_12736, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12734, c_12731])).
% 8.05/2.75  tff(c_15805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15778, c_12736])).
% 8.05/2.75  tff(c_15806, plain, ('#skF_15'='#skF_12'), inference(splitRight, [status(thm)], [c_12733])).
% 8.05/2.75  tff(c_15808, plain, (![A_8]: (r1_xboole_0('#skF_12', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_15806, c_12719])).
% 8.05/2.75  tff(c_15843, plain, (![A_1038, B_1039]: (k4_xboole_0(A_1038, k4_xboole_0(A_1038, B_1039))=k3_xboole_0(A_1038, B_1039))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.75  tff(c_15826, plain, (![A_8]: (k4_xboole_0('#skF_12', A_8)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_15806, c_15806, c_12720])).
% 8.05/2.75  tff(c_15874, plain, (![B_1043]: (k3_xboole_0('#skF_12', B_1043)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_15843, c_15826])).
% 8.05/2.75  tff(c_15879, plain, (![B_1043, C_5]: (~r1_xboole_0('#skF_12', B_1043) | ~r2_hidden(C_5, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_15874, c_4])).
% 8.05/2.75  tff(c_15884, plain, (![C_5]: (~r2_hidden(C_5, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_15808, c_15879])).
% 8.05/2.75  tff(c_18559, plain, (![A_1222, C_1223]: (r2_hidden('#skF_5'(A_1222, '#skF_12', C_1223), C_1223) | k2_zfmisc_1(A_1222, '#skF_12')=C_1223)), inference(resolution, [status(thm)], [c_17090, c_15884])).
% 8.05/2.75  tff(c_18671, plain, (![A_1222]: (k2_zfmisc_1(A_1222, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_18559, c_15884])).
% 8.05/2.75  tff(c_16439, plain, (![A_1097, B_1098, D_1099]: (r2_hidden('#skF_6'(A_1097, B_1098, k2_zfmisc_1(A_1097, B_1098), D_1099), A_1097) | ~r2_hidden(D_1099, k2_zfmisc_1(A_1097, B_1098)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.75  tff(c_16491, plain, (![D_1099, B_1098]: (~r2_hidden(D_1099, k2_zfmisc_1('#skF_12', B_1098)))), inference(resolution, [status(thm)], [c_16439, c_15884])).
% 8.05/2.75  tff(c_18663, plain, (![A_1222, B_1098]: (k2_zfmisc_1(A_1222, '#skF_12')=k2_zfmisc_1('#skF_12', B_1098))), inference(resolution, [status(thm)], [c_18559, c_16491])).
% 8.05/2.75  tff(c_18818, plain, (![B_1098]: (k2_zfmisc_1('#skF_12', B_1098)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_18671, c_18663])).
% 8.05/2.75  tff(c_15809, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_15806, c_12731])).
% 8.05/2.75  tff(c_18846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18818, c_15809])).
% 8.05/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.75  
% 8.05/2.75  Inference rules
% 8.05/2.75  ----------------------
% 8.05/2.75  #Ref     : 0
% 8.05/2.75  #Sup     : 4110
% 8.05/2.75  #Fact    : 0
% 8.05/2.75  #Define  : 0
% 8.05/2.75  #Split   : 10
% 8.05/2.75  #Chain   : 0
% 8.05/2.75  #Close   : 0
% 8.05/2.75  
% 8.05/2.75  Ordering : KBO
% 8.05/2.75  
% 8.05/2.75  Simplification rules
% 8.05/2.75  ----------------------
% 8.05/2.75  #Subsume      : 894
% 8.05/2.75  #Demod        : 1412
% 8.05/2.75  #Tautology    : 1610
% 8.05/2.75  #SimpNegUnit  : 154
% 8.05/2.75  #BackRed      : 161
% 8.05/2.75  
% 8.05/2.75  #Partial instantiations: 0
% 8.05/2.75  #Strategies tried      : 1
% 8.05/2.75  
% 8.05/2.75  Timing (in seconds)
% 8.05/2.75  ----------------------
% 8.05/2.75  Preprocessing        : 0.31
% 8.05/2.75  Parsing              : 0.15
% 8.05/2.75  CNF conversion       : 0.03
% 8.05/2.75  Main loop            : 1.67
% 8.05/2.75  Inferencing          : 0.63
% 8.05/2.75  Reduction            : 0.51
% 8.05/2.75  Demodulation         : 0.32
% 8.05/2.75  BG Simplification    : 0.07
% 8.05/2.75  Subsumption          : 0.31
% 8.05/2.75  Abstraction          : 0.10
% 8.05/2.75  MUC search           : 0.00
% 8.05/2.75  Cooper               : 0.00
% 8.05/2.75  Total                : 2.04
% 8.05/2.75  Index Insertion      : 0.00
% 8.05/2.75  Index Deletion       : 0.00
% 8.05/2.75  Index Matching       : 0.00
% 8.05/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
