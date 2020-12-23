%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:18 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 700 expanded)
%              Number of leaves         :   37 ( 242 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 (1527 expanded)
%              Number of equality atoms :   59 ( 442 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_3 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_12 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_66,plain,
    ( '#skF_14' != '#skF_12'
    | '#skF_11' != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_75,plain,(
    '#skF_11' != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_4'(A_17,B_18),B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_429,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( r2_hidden(k4_tarski(A_138,B_139),k2_zfmisc_1(C_140,D_141))
      | ~ r2_hidden(B_139,D_141)
      | ~ r2_hidden(A_138,C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_687,plain,(
    ! [A_157,B_158] :
      ( r2_hidden(k4_tarski(A_157,B_158),k2_zfmisc_1('#skF_13','#skF_14'))
      | ~ r2_hidden(B_158,'#skF_12')
      | ~ r2_hidden(A_157,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_429])).

tff(c_58,plain,(
    ! [A_56,C_58,B_57,D_59] :
      ( r2_hidden(A_56,C_58)
      | ~ r2_hidden(k4_tarski(A_56,B_57),k2_zfmisc_1(C_58,D_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_708,plain,(
    ! [A_157,B_158] :
      ( r2_hidden(A_157,'#skF_13')
      | ~ r2_hidden(B_158,'#skF_12')
      | ~ r2_hidden(A_157,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_687,c_58])).

tff(c_1679,plain,(
    ! [B_158] : ~ r2_hidden(B_158,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_57,D_59,A_56,C_58] :
      ( r2_hidden(B_57,D_59)
      | ~ r2_hidden(k4_tarski(A_56,B_57),k2_zfmisc_1(C_58,D_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_707,plain,(
    ! [B_158,A_157] :
      ( r2_hidden(B_158,'#skF_14')
      | ~ r2_hidden(B_158,'#skF_12')
      | ~ r2_hidden(A_157,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_687,c_56])).

tff(c_954,plain,(
    ! [A_175] : ~ r2_hidden(A_175,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_979,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_954])).

tff(c_28,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_176,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_191,plain,(
    ! [A_20,C_93] :
      ( ~ r1_xboole_0(A_20,k1_xboole_0)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_176])).

tff(c_203,plain,(
    ! [C_96] : ~ r2_hidden(C_96,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191])).

tff(c_238,plain,(
    ! [B_101] : r1_tarski(k1_xboole_0,B_101) ),
    inference(resolution,[status(thm)],[c_10,c_203])).

tff(c_155,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_4'(A_83,B_84),B_84)
      | ~ r2_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r2_xboole_0(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_164,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_242,plain,(
    ! [B_101] :
      ( ~ v1_xboole_0(B_101)
      | k1_xboole_0 = B_101 ) ),
    inference(resolution,[status(thm)],[c_238,c_164])).

tff(c_984,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_979,c_242])).

tff(c_991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_984])).

tff(c_993,plain,(
    ! [B_176] :
      ( r2_hidden(B_176,'#skF_14')
      | ~ r2_hidden(B_176,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1344,plain,(
    ! [A_210] :
      ( r1_tarski(A_210,'#skF_14')
      | ~ r2_hidden('#skF_2'(A_210,'#skF_14'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_993,c_8])).

tff(c_1349,plain,(
    r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_10,c_1344])).

tff(c_62,plain,(
    ! [A_60] : k2_zfmisc_1(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1350,plain,(
    ! [A_211,B_212,C_213] :
      ( r2_hidden('#skF_7'(A_211,B_212,C_213),B_212)
      | r2_hidden('#skF_8'(A_211,B_212,C_213),C_213)
      | k2_zfmisc_1(A_211,B_212) = C_213 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_196,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191])).

tff(c_1368,plain,(
    ! [A_211,C_213] :
      ( r2_hidden('#skF_8'(A_211,k1_xboole_0,C_213),C_213)
      | k2_zfmisc_1(A_211,k1_xboole_0) = C_213 ) ),
    inference(resolution,[status(thm)],[c_1350,c_196])).

tff(c_1423,plain,(
    ! [A_214,C_215] :
      ( r2_hidden('#skF_8'(A_214,k1_xboole_0,C_215),C_215)
      | k1_xboole_0 = C_215 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1368])).

tff(c_416,plain,(
    ! [B_130,D_131,A_132,C_133] :
      ( r2_hidden(B_130,D_131)
      | ~ r2_hidden(k4_tarski(A_132,B_130),k2_zfmisc_1(C_133,D_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_419,plain,(
    ! [B_130,A_132] :
      ( r2_hidden(B_130,'#skF_12')
      | ~ r2_hidden(k4_tarski(A_132,B_130),k2_zfmisc_1('#skF_13','#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_416])).

tff(c_458,plain,(
    ! [B_139,A_138] :
      ( r2_hidden(B_139,'#skF_12')
      | ~ r2_hidden(B_139,'#skF_14')
      | ~ r2_hidden(A_138,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_429,c_419])).

tff(c_467,plain,(
    ! [A_142] : ~ r2_hidden(A_142,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_487,plain,(
    v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_4,c_467])).

tff(c_496,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_487,c_242])).

tff(c_64,plain,(
    ! [B_61] : k2_zfmisc_1(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_509,plain,(
    ! [B_61] : k2_zfmisc_1('#skF_13',B_61) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_496,c_64])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_140,plain,(
    ! [B_81,A_82] :
      ( k1_xboole_0 = B_81
      | k1_xboole_0 = A_82
      | k2_zfmisc_1(A_82,B_81) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_143,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_140])).

tff(c_150,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_68,c_143])).

tff(c_506,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_150])).

tff(c_685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_506])).

tff(c_686,plain,(
    ! [B_139] :
      ( r2_hidden(B_139,'#skF_12')
      | ~ r2_hidden(B_139,'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_1451,plain,(
    ! [A_214] :
      ( r2_hidden('#skF_8'(A_214,k1_xboole_0,'#skF_14'),'#skF_12')
      | k1_xboole_0 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_1423,c_686])).

tff(c_1541,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_1451])).

tff(c_711,plain,(
    ! [B_159] :
      ( r2_hidden(B_159,'#skF_12')
      | ~ r2_hidden(B_159,'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_731,plain,
    ( r2_hidden('#skF_1'('#skF_14'),'#skF_12')
    | v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_4,c_711])).

tff(c_732,plain,(
    v1_xboole_0('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_731])).

tff(c_741,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_732,c_242])).

tff(c_755,plain,(
    ! [A_60] : k2_zfmisc_1(A_60,'#skF_14') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_741,c_62])).

tff(c_751,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_150])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_751])).

tff(c_838,plain,(
    r2_hidden('#skF_1'('#skF_14'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_731])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1262,plain,(
    ! [B_204] :
      ( r2_hidden('#skF_1'('#skF_14'),B_204)
      | ~ r1_tarski('#skF_12',B_204) ) ),
    inference(resolution,[status(thm)],[c_838,c_6])).

tff(c_1293,plain,(
    ~ r1_tarski('#skF_12',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1262,c_196])).

tff(c_1543,plain,(
    ~ r1_tarski('#skF_12','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1293])).

tff(c_1564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_1543])).

tff(c_1566,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_1451])).

tff(c_1567,plain,(
    ! [A_221,B_222,C_223] :
      ( r2_hidden('#skF_6'(A_221,B_222,C_223),A_221)
      | r2_hidden('#skF_8'(A_221,B_222,C_223),C_223)
      | k2_zfmisc_1(A_221,B_222) = C_223 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1585,plain,(
    ! [B_222,C_223] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_222,C_223),C_223)
      | k2_zfmisc_1(k1_xboole_0,B_222) = C_223 ) ),
    inference(resolution,[status(thm)],[c_1567,c_196])).

tff(c_1635,plain,(
    ! [B_225,C_226] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_225,C_226),C_226)
      | k1_xboole_0 = C_226 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1585])).

tff(c_1647,plain,(
    ! [B_225] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_225,'#skF_14'),'#skF_12')
      | k1_xboole_0 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_1635,c_686])).

tff(c_1665,plain,(
    ! [B_225] : r2_hidden('#skF_8'(k1_xboole_0,B_225,'#skF_14'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_1566,c_1647])).

tff(c_1685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1679,c_1665])).

tff(c_1687,plain,(
    ! [A_228] :
      ( r2_hidden(A_228,'#skF_13')
      | ~ r2_hidden(A_228,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_2008,plain,(
    ! [A_249] :
      ( r2_hidden('#skF_4'(A_249,'#skF_11'),'#skF_13')
      | ~ r2_xboole_0(A_249,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_24,c_1687])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden('#skF_4'(A_17,B_18),A_17)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2019,plain,(
    ~ r2_xboole_0('#skF_13','#skF_11') ),
    inference(resolution,[status(thm)],[c_2008,c_22])).

tff(c_2023,plain,
    ( '#skF_11' = '#skF_13'
    | ~ r1_tarski('#skF_13','#skF_11') ),
    inference(resolution,[status(thm)],[c_12,c_2019])).

tff(c_2026,plain,(
    ~ r1_tarski('#skF_13','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2023])).

tff(c_845,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_1'('#skF_14'),B_6)
      | ~ r1_tarski('#skF_12',B_6) ) ),
    inference(resolution,[status(thm)],[c_838,c_6])).

tff(c_328,plain,(
    ! [A_115,C_116,B_117,D_118] :
      ( r2_hidden(A_115,C_116)
      | ~ r2_hidden(k4_tarski(A_115,B_117),k2_zfmisc_1(C_116,D_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_331,plain,(
    ! [A_115,B_117] :
      ( r2_hidden(A_115,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_115,B_117),k2_zfmisc_1('#skF_13','#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_328])).

tff(c_459,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(A_138,'#skF_11')
      | ~ r2_hidden(B_139,'#skF_14')
      | ~ r2_hidden(A_138,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_429,c_331])).

tff(c_1472,plain,(
    ! [B_219] : ~ r2_hidden(B_219,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_1486,plain,(
    ~ r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_845,c_1472])).

tff(c_1516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_1486])).

tff(c_1518,plain,(
    ! [A_220] :
      ( r2_hidden(A_220,'#skF_11')
      | ~ r2_hidden(A_220,'#skF_13') ) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_2068,plain,(
    ! [A_256] :
      ( r1_tarski(A_256,'#skF_11')
      | ~ r2_hidden('#skF_2'(A_256,'#skF_11'),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1518,c_8])).

tff(c_2072,plain,(
    r1_tarski('#skF_13','#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_2068])).

tff(c_2076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2026,c_2026,c_2072])).

tff(c_2077,plain,(
    '#skF_14' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2078,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2079,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_70])).

tff(c_2084,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k2_zfmisc_1('#skF_13','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_72])).

tff(c_2493,plain,(
    ! [A_337,B_338,C_339,D_340] :
      ( r2_hidden(k4_tarski(A_337,B_338),k2_zfmisc_1(C_339,D_340))
      | ~ r2_hidden(B_338,D_340)
      | ~ r2_hidden(A_337,C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2560,plain,(
    ! [A_348,B_349] :
      ( r2_hidden(k4_tarski(A_348,B_349),k2_zfmisc_1('#skF_13','#skF_12'))
      | ~ r2_hidden(B_349,'#skF_14')
      | ~ r2_hidden(A_348,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_2493])).

tff(c_2576,plain,(
    ! [B_349,A_348] :
      ( r2_hidden(B_349,'#skF_12')
      | ~ r2_hidden(B_349,'#skF_14')
      | ~ r2_hidden(A_348,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_2560,c_56])).

tff(c_2739,plain,(
    ! [A_360] : ~ r2_hidden(A_360,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_2576])).

tff(c_2769,plain,(
    v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_4,c_2739])).

tff(c_2191,plain,(
    ! [A_284,B_285,C_286] :
      ( ~ r1_xboole_0(A_284,B_285)
      | ~ r2_hidden(C_286,k3_xboole_0(A_284,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2206,plain,(
    ! [A_20,C_286] :
      ( ~ r1_xboole_0(A_20,k1_xboole_0)
      | ~ r2_hidden(C_286,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2191])).

tff(c_2212,plain,(
    ! [C_287] : ~ r2_hidden(C_287,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2206])).

tff(c_2234,plain,(
    ! [B_289] : r1_tarski(k1_xboole_0,B_289) ),
    inference(resolution,[status(thm)],[c_10,c_2212])).

tff(c_2166,plain,(
    ! [A_278,B_279] :
      ( r2_hidden('#skF_4'(A_278,B_279),B_279)
      | ~ r2_xboole_0(A_278,B_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2176,plain,(
    ! [B_280,A_281] :
      ( ~ v1_xboole_0(B_280)
      | ~ r2_xboole_0(A_281,B_280) ) ),
    inference(resolution,[status(thm)],[c_2166,c_2])).

tff(c_2180,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_2176])).

tff(c_2238,plain,(
    ! [B_289] :
      ( ~ v1_xboole_0(B_289)
      | k1_xboole_0 = B_289 ) ),
    inference(resolution,[status(thm)],[c_2234,c_2180])).

tff(c_2776,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_2769,c_2238])).

tff(c_2782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2079,c_2776])).

tff(c_2807,plain,(
    ! [B_363] :
      ( r2_hidden(B_363,'#skF_12')
      | ~ r2_hidden(B_363,'#skF_14') ) ),
    inference(splitRight,[status(thm)],[c_2576])).

tff(c_3328,plain,(
    ! [B_403] :
      ( r2_hidden('#skF_2'('#skF_14',B_403),'#skF_12')
      | r1_tarski('#skF_14',B_403) ) ),
    inference(resolution,[status(thm)],[c_10,c_2807])).

tff(c_3339,plain,(
    r1_tarski('#skF_14','#skF_12') ),
    inference(resolution,[status(thm)],[c_3328,c_8])).

tff(c_2245,plain,(
    ! [C_291,B_292,A_293] :
      ( r2_hidden(C_291,B_292)
      | ~ r2_hidden(C_291,A_293)
      | ~ r1_tarski(A_293,B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2465,plain,(
    ! [A_332,B_333,B_334] :
      ( r2_hidden('#skF_4'(A_332,B_333),B_334)
      | ~ r1_tarski(B_333,B_334)
      | ~ r2_xboole_0(A_332,B_333) ) ),
    inference(resolution,[status(thm)],[c_24,c_2245])).

tff(c_2525,plain,(
    ! [B_341,B_342] :
      ( ~ r1_tarski(B_341,B_342)
      | ~ r2_xboole_0(B_342,B_341) ) ),
    inference(resolution,[status(thm)],[c_2465,c_22])).

tff(c_2529,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_2525])).

tff(c_3342,plain,
    ( '#skF_14' = '#skF_12'
    | ~ r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_3339,c_2529])).

tff(c_3353,plain,(
    ~ r1_tarski('#skF_12','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_2077,c_3342])).

tff(c_2426,plain,(
    ! [B_323,D_324,A_325,C_326] :
      ( r2_hidden(B_323,D_324)
      | ~ r2_hidden(k4_tarski(A_325,B_323),k2_zfmisc_1(C_326,D_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2435,plain,(
    ! [B_323,A_325] :
      ( r2_hidden(B_323,'#skF_14')
      | ~ r2_hidden(k4_tarski(A_325,B_323),k2_zfmisc_1('#skF_13','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_2426])).

tff(c_2518,plain,(
    ! [B_338,A_337] :
      ( r2_hidden(B_338,'#skF_14')
      | ~ r2_hidden(B_338,'#skF_12')
      | ~ r2_hidden(A_337,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_2493,c_2435])).

tff(c_2597,plain,(
    ! [A_352] : ~ r2_hidden(A_352,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_2518])).

tff(c_2622,plain,(
    v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_4,c_2597])).

tff(c_2629,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_2622,c_2238])).

tff(c_2635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2079,c_2629])).

tff(c_2637,plain,(
    ! [B_353] :
      ( r2_hidden(B_353,'#skF_14')
      | ~ r2_hidden(B_353,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_2518])).

tff(c_3363,plain,(
    ! [A_404] :
      ( r1_tarski(A_404,'#skF_14')
      | ~ r2_hidden('#skF_2'(A_404,'#skF_14'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_2637,c_8])).

tff(c_3371,plain,(
    r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_10,c_3363])).

tff(c_3377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3353,c_3353,c_3371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:02:53 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.78  
% 4.09/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.78  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_3 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_12 > #skF_4
% 4.09/1.78  
% 4.09/1.78  %Foreground sorts:
% 4.09/1.78  
% 4.09/1.78  
% 4.09/1.78  %Background operators:
% 4.09/1.78  
% 4.09/1.78  
% 4.09/1.78  %Foreground operators:
% 4.09/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.78  tff('#skF_11', type, '#skF_11': $i).
% 4.09/1.78  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.09/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.09/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.09/1.78  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 4.09/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.78  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 4.09/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.09/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.78  tff('#skF_14', type, '#skF_14': $i).
% 4.09/1.78  tff('#skF_13', type, '#skF_13': $i).
% 4.09/1.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.09/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.09/1.78  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.09/1.78  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.09/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.09/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.78  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.09/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.78  tff('#skF_12', type, '#skF_12': $i).
% 4.09/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.09/1.78  
% 4.48/1.80  tff(f_108, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.48/1.80  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.48/1.80  tff(f_69, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 4.48/1.80  tff(f_91, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.48/1.80  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.48/1.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.48/1.80  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.48/1.80  tff(f_71, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.48/1.80  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.48/1.80  tff(f_97, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.48/1.80  tff(f_85, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.48/1.80  tff(c_66, plain, ('#skF_14'!='#skF_12' | '#skF_11'!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.48/1.80  tff(c_75, plain, ('#skF_11'!='#skF_13'), inference(splitLeft, [status(thm)], [c_66])).
% 4.48/1.80  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.48/1.80  tff(c_24, plain, (![A_17, B_18]: (r2_hidden('#skF_4'(A_17, B_18), B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.48/1.80  tff(c_72, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.48/1.80  tff(c_429, plain, (![A_138, B_139, C_140, D_141]: (r2_hidden(k4_tarski(A_138, B_139), k2_zfmisc_1(C_140, D_141)) | ~r2_hidden(B_139, D_141) | ~r2_hidden(A_138, C_140))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_687, plain, (![A_157, B_158]: (r2_hidden(k4_tarski(A_157, B_158), k2_zfmisc_1('#skF_13', '#skF_14')) | ~r2_hidden(B_158, '#skF_12') | ~r2_hidden(A_157, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_429])).
% 4.48/1.80  tff(c_58, plain, (![A_56, C_58, B_57, D_59]: (r2_hidden(A_56, C_58) | ~r2_hidden(k4_tarski(A_56, B_57), k2_zfmisc_1(C_58, D_59)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_708, plain, (![A_157, B_158]: (r2_hidden(A_157, '#skF_13') | ~r2_hidden(B_158, '#skF_12') | ~r2_hidden(A_157, '#skF_11'))), inference(resolution, [status(thm)], [c_687, c_58])).
% 4.48/1.80  tff(c_1679, plain, (![B_158]: (~r2_hidden(B_158, '#skF_12'))), inference(splitLeft, [status(thm)], [c_708])).
% 4.48/1.80  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_70, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.48/1.80  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.48/1.80  tff(c_56, plain, (![B_57, D_59, A_56, C_58]: (r2_hidden(B_57, D_59) | ~r2_hidden(k4_tarski(A_56, B_57), k2_zfmisc_1(C_58, D_59)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_707, plain, (![B_158, A_157]: (r2_hidden(B_158, '#skF_14') | ~r2_hidden(B_158, '#skF_12') | ~r2_hidden(A_157, '#skF_11'))), inference(resolution, [status(thm)], [c_687, c_56])).
% 4.48/1.80  tff(c_954, plain, (![A_175]: (~r2_hidden(A_175, '#skF_11'))), inference(splitLeft, [status(thm)], [c_707])).
% 4.48/1.80  tff(c_979, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_954])).
% 4.48/1.80  tff(c_28, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.48/1.80  tff(c_26, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_176, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.48/1.80  tff(c_191, plain, (![A_20, C_93]: (~r1_xboole_0(A_20, k1_xboole_0) | ~r2_hidden(C_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_176])).
% 4.48/1.80  tff(c_203, plain, (![C_96]: (~r2_hidden(C_96, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_191])).
% 4.48/1.80  tff(c_238, plain, (![B_101]: (r1_tarski(k1_xboole_0, B_101))), inference(resolution, [status(thm)], [c_10, c_203])).
% 4.48/1.80  tff(c_155, plain, (![A_83, B_84]: (r2_hidden('#skF_4'(A_83, B_84), B_84) | ~r2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.48/1.80  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.48/1.80  tff(c_160, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r2_xboole_0(A_86, B_85))), inference(resolution, [status(thm)], [c_155, c_2])).
% 4.48/1.80  tff(c_164, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_160])).
% 4.48/1.80  tff(c_242, plain, (![B_101]: (~v1_xboole_0(B_101) | k1_xboole_0=B_101)), inference(resolution, [status(thm)], [c_238, c_164])).
% 4.48/1.80  tff(c_984, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_979, c_242])).
% 4.48/1.80  tff(c_991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_984])).
% 4.48/1.80  tff(c_993, plain, (![B_176]: (r2_hidden(B_176, '#skF_14') | ~r2_hidden(B_176, '#skF_12'))), inference(splitRight, [status(thm)], [c_707])).
% 4.48/1.80  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_1344, plain, (![A_210]: (r1_tarski(A_210, '#skF_14') | ~r2_hidden('#skF_2'(A_210, '#skF_14'), '#skF_12'))), inference(resolution, [status(thm)], [c_993, c_8])).
% 4.48/1.80  tff(c_1349, plain, (r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_10, c_1344])).
% 4.48/1.80  tff(c_62, plain, (![A_60]: (k2_zfmisc_1(A_60, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.48/1.80  tff(c_1350, plain, (![A_211, B_212, C_213]: (r2_hidden('#skF_7'(A_211, B_212, C_213), B_212) | r2_hidden('#skF_8'(A_211, B_212, C_213), C_213) | k2_zfmisc_1(A_211, B_212)=C_213)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.48/1.80  tff(c_196, plain, (![C_93]: (~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_191])).
% 4.48/1.80  tff(c_1368, plain, (![A_211, C_213]: (r2_hidden('#skF_8'(A_211, k1_xboole_0, C_213), C_213) | k2_zfmisc_1(A_211, k1_xboole_0)=C_213)), inference(resolution, [status(thm)], [c_1350, c_196])).
% 4.48/1.80  tff(c_1423, plain, (![A_214, C_215]: (r2_hidden('#skF_8'(A_214, k1_xboole_0, C_215), C_215) | k1_xboole_0=C_215)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1368])).
% 4.48/1.80  tff(c_416, plain, (![B_130, D_131, A_132, C_133]: (r2_hidden(B_130, D_131) | ~r2_hidden(k4_tarski(A_132, B_130), k2_zfmisc_1(C_133, D_131)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_419, plain, (![B_130, A_132]: (r2_hidden(B_130, '#skF_12') | ~r2_hidden(k4_tarski(A_132, B_130), k2_zfmisc_1('#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_416])).
% 4.48/1.80  tff(c_458, plain, (![B_139, A_138]: (r2_hidden(B_139, '#skF_12') | ~r2_hidden(B_139, '#skF_14') | ~r2_hidden(A_138, '#skF_13'))), inference(resolution, [status(thm)], [c_429, c_419])).
% 4.48/1.80  tff(c_467, plain, (![A_142]: (~r2_hidden(A_142, '#skF_13'))), inference(splitLeft, [status(thm)], [c_458])).
% 4.48/1.80  tff(c_487, plain, (v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_4, c_467])).
% 4.48/1.80  tff(c_496, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_487, c_242])).
% 4.48/1.80  tff(c_64, plain, (![B_61]: (k2_zfmisc_1(k1_xboole_0, B_61)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.48/1.80  tff(c_509, plain, (![B_61]: (k2_zfmisc_1('#skF_13', B_61)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_496, c_64])).
% 4.48/1.80  tff(c_68, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.48/1.80  tff(c_140, plain, (![B_81, A_82]: (k1_xboole_0=B_81 | k1_xboole_0=A_82 | k2_zfmisc_1(A_82, B_81)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.48/1.80  tff(c_143, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_72, c_140])).
% 4.48/1.80  tff(c_150, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_68, c_143])).
% 4.48/1.80  tff(c_506, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_496, c_150])).
% 4.48/1.80  tff(c_685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_509, c_506])).
% 4.48/1.80  tff(c_686, plain, (![B_139]: (r2_hidden(B_139, '#skF_12') | ~r2_hidden(B_139, '#skF_14'))), inference(splitRight, [status(thm)], [c_458])).
% 4.48/1.80  tff(c_1451, plain, (![A_214]: (r2_hidden('#skF_8'(A_214, k1_xboole_0, '#skF_14'), '#skF_12') | k1_xboole_0='#skF_14')), inference(resolution, [status(thm)], [c_1423, c_686])).
% 4.48/1.80  tff(c_1541, plain, (k1_xboole_0='#skF_14'), inference(splitLeft, [status(thm)], [c_1451])).
% 4.48/1.80  tff(c_711, plain, (![B_159]: (r2_hidden(B_159, '#skF_12') | ~r2_hidden(B_159, '#skF_14'))), inference(splitRight, [status(thm)], [c_458])).
% 4.48/1.80  tff(c_731, plain, (r2_hidden('#skF_1'('#skF_14'), '#skF_12') | v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_4, c_711])).
% 4.48/1.80  tff(c_732, plain, (v1_xboole_0('#skF_14')), inference(splitLeft, [status(thm)], [c_731])).
% 4.48/1.80  tff(c_741, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_732, c_242])).
% 4.48/1.80  tff(c_755, plain, (![A_60]: (k2_zfmisc_1(A_60, '#skF_14')='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_741, c_741, c_62])).
% 4.48/1.80  tff(c_751, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_741, c_150])).
% 4.48/1.80  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_755, c_751])).
% 4.48/1.80  tff(c_838, plain, (r2_hidden('#skF_1'('#skF_14'), '#skF_12')), inference(splitRight, [status(thm)], [c_731])).
% 4.48/1.80  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_1262, plain, (![B_204]: (r2_hidden('#skF_1'('#skF_14'), B_204) | ~r1_tarski('#skF_12', B_204))), inference(resolution, [status(thm)], [c_838, c_6])).
% 4.48/1.80  tff(c_1293, plain, (~r1_tarski('#skF_12', k1_xboole_0)), inference(resolution, [status(thm)], [c_1262, c_196])).
% 4.48/1.80  tff(c_1543, plain, (~r1_tarski('#skF_12', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1293])).
% 4.48/1.80  tff(c_1564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1349, c_1543])).
% 4.48/1.80  tff(c_1566, plain, (k1_xboole_0!='#skF_14'), inference(splitRight, [status(thm)], [c_1451])).
% 4.48/1.80  tff(c_1567, plain, (![A_221, B_222, C_223]: (r2_hidden('#skF_6'(A_221, B_222, C_223), A_221) | r2_hidden('#skF_8'(A_221, B_222, C_223), C_223) | k2_zfmisc_1(A_221, B_222)=C_223)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.48/1.80  tff(c_1585, plain, (![B_222, C_223]: (r2_hidden('#skF_8'(k1_xboole_0, B_222, C_223), C_223) | k2_zfmisc_1(k1_xboole_0, B_222)=C_223)), inference(resolution, [status(thm)], [c_1567, c_196])).
% 4.48/1.80  tff(c_1635, plain, (![B_225, C_226]: (r2_hidden('#skF_8'(k1_xboole_0, B_225, C_226), C_226) | k1_xboole_0=C_226)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1585])).
% 4.48/1.80  tff(c_1647, plain, (![B_225]: (r2_hidden('#skF_8'(k1_xboole_0, B_225, '#skF_14'), '#skF_12') | k1_xboole_0='#skF_14')), inference(resolution, [status(thm)], [c_1635, c_686])).
% 4.48/1.80  tff(c_1665, plain, (![B_225]: (r2_hidden('#skF_8'(k1_xboole_0, B_225, '#skF_14'), '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1566, c_1647])).
% 4.48/1.80  tff(c_1685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1679, c_1665])).
% 4.48/1.80  tff(c_1687, plain, (![A_228]: (r2_hidden(A_228, '#skF_13') | ~r2_hidden(A_228, '#skF_11'))), inference(splitRight, [status(thm)], [c_708])).
% 4.48/1.80  tff(c_2008, plain, (![A_249]: (r2_hidden('#skF_4'(A_249, '#skF_11'), '#skF_13') | ~r2_xboole_0(A_249, '#skF_11'))), inference(resolution, [status(thm)], [c_24, c_1687])).
% 4.48/1.80  tff(c_22, plain, (![A_17, B_18]: (~r2_hidden('#skF_4'(A_17, B_18), A_17) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.48/1.80  tff(c_2019, plain, (~r2_xboole_0('#skF_13', '#skF_11')), inference(resolution, [status(thm)], [c_2008, c_22])).
% 4.48/1.80  tff(c_2023, plain, ('#skF_11'='#skF_13' | ~r1_tarski('#skF_13', '#skF_11')), inference(resolution, [status(thm)], [c_12, c_2019])).
% 4.48/1.80  tff(c_2026, plain, (~r1_tarski('#skF_13', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_75, c_2023])).
% 4.48/1.80  tff(c_845, plain, (![B_6]: (r2_hidden('#skF_1'('#skF_14'), B_6) | ~r1_tarski('#skF_12', B_6))), inference(resolution, [status(thm)], [c_838, c_6])).
% 4.48/1.80  tff(c_328, plain, (![A_115, C_116, B_117, D_118]: (r2_hidden(A_115, C_116) | ~r2_hidden(k4_tarski(A_115, B_117), k2_zfmisc_1(C_116, D_118)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_331, plain, (![A_115, B_117]: (r2_hidden(A_115, '#skF_11') | ~r2_hidden(k4_tarski(A_115, B_117), k2_zfmisc_1('#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_328])).
% 4.48/1.80  tff(c_459, plain, (![A_138, B_139]: (r2_hidden(A_138, '#skF_11') | ~r2_hidden(B_139, '#skF_14') | ~r2_hidden(A_138, '#skF_13'))), inference(resolution, [status(thm)], [c_429, c_331])).
% 4.48/1.80  tff(c_1472, plain, (![B_219]: (~r2_hidden(B_219, '#skF_14'))), inference(splitLeft, [status(thm)], [c_459])).
% 4.48/1.80  tff(c_1486, plain, (~r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_845, c_1472])).
% 4.48/1.80  tff(c_1516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1349, c_1486])).
% 4.48/1.80  tff(c_1518, plain, (![A_220]: (r2_hidden(A_220, '#skF_11') | ~r2_hidden(A_220, '#skF_13'))), inference(splitRight, [status(thm)], [c_459])).
% 4.48/1.80  tff(c_2068, plain, (![A_256]: (r1_tarski(A_256, '#skF_11') | ~r2_hidden('#skF_2'(A_256, '#skF_11'), '#skF_13'))), inference(resolution, [status(thm)], [c_1518, c_8])).
% 4.48/1.80  tff(c_2072, plain, (r1_tarski('#skF_13', '#skF_11')), inference(resolution, [status(thm)], [c_10, c_2068])).
% 4.48/1.80  tff(c_2076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2026, c_2026, c_2072])).
% 4.48/1.80  tff(c_2077, plain, ('#skF_14'!='#skF_12'), inference(splitRight, [status(thm)], [c_66])).
% 4.48/1.80  tff(c_2078, plain, ('#skF_11'='#skF_13'), inference(splitRight, [status(thm)], [c_66])).
% 4.48/1.80  tff(c_2079, plain, (k1_xboole_0!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_70])).
% 4.48/1.80  tff(c_2084, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k2_zfmisc_1('#skF_13', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_72])).
% 4.48/1.80  tff(c_2493, plain, (![A_337, B_338, C_339, D_340]: (r2_hidden(k4_tarski(A_337, B_338), k2_zfmisc_1(C_339, D_340)) | ~r2_hidden(B_338, D_340) | ~r2_hidden(A_337, C_339))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_2560, plain, (![A_348, B_349]: (r2_hidden(k4_tarski(A_348, B_349), k2_zfmisc_1('#skF_13', '#skF_12')) | ~r2_hidden(B_349, '#skF_14') | ~r2_hidden(A_348, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_2493])).
% 4.48/1.80  tff(c_2576, plain, (![B_349, A_348]: (r2_hidden(B_349, '#skF_12') | ~r2_hidden(B_349, '#skF_14') | ~r2_hidden(A_348, '#skF_13'))), inference(resolution, [status(thm)], [c_2560, c_56])).
% 4.48/1.80  tff(c_2739, plain, (![A_360]: (~r2_hidden(A_360, '#skF_13'))), inference(splitLeft, [status(thm)], [c_2576])).
% 4.48/1.80  tff(c_2769, plain, (v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_4, c_2739])).
% 4.48/1.80  tff(c_2191, plain, (![A_284, B_285, C_286]: (~r1_xboole_0(A_284, B_285) | ~r2_hidden(C_286, k3_xboole_0(A_284, B_285)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.48/1.80  tff(c_2206, plain, (![A_20, C_286]: (~r1_xboole_0(A_20, k1_xboole_0) | ~r2_hidden(C_286, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2191])).
% 4.48/1.80  tff(c_2212, plain, (![C_287]: (~r2_hidden(C_287, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2206])).
% 4.48/1.80  tff(c_2234, plain, (![B_289]: (r1_tarski(k1_xboole_0, B_289))), inference(resolution, [status(thm)], [c_10, c_2212])).
% 4.48/1.80  tff(c_2166, plain, (![A_278, B_279]: (r2_hidden('#skF_4'(A_278, B_279), B_279) | ~r2_xboole_0(A_278, B_279))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.48/1.80  tff(c_2176, plain, (![B_280, A_281]: (~v1_xboole_0(B_280) | ~r2_xboole_0(A_281, B_280))), inference(resolution, [status(thm)], [c_2166, c_2])).
% 4.48/1.80  tff(c_2180, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_2176])).
% 4.48/1.80  tff(c_2238, plain, (![B_289]: (~v1_xboole_0(B_289) | k1_xboole_0=B_289)), inference(resolution, [status(thm)], [c_2234, c_2180])).
% 4.48/1.80  tff(c_2776, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_2769, c_2238])).
% 4.48/1.80  tff(c_2782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2079, c_2776])).
% 4.48/1.80  tff(c_2807, plain, (![B_363]: (r2_hidden(B_363, '#skF_12') | ~r2_hidden(B_363, '#skF_14'))), inference(splitRight, [status(thm)], [c_2576])).
% 4.48/1.80  tff(c_3328, plain, (![B_403]: (r2_hidden('#skF_2'('#skF_14', B_403), '#skF_12') | r1_tarski('#skF_14', B_403))), inference(resolution, [status(thm)], [c_10, c_2807])).
% 4.48/1.80  tff(c_3339, plain, (r1_tarski('#skF_14', '#skF_12')), inference(resolution, [status(thm)], [c_3328, c_8])).
% 4.48/1.80  tff(c_2245, plain, (![C_291, B_292, A_293]: (r2_hidden(C_291, B_292) | ~r2_hidden(C_291, A_293) | ~r1_tarski(A_293, B_292))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_2465, plain, (![A_332, B_333, B_334]: (r2_hidden('#skF_4'(A_332, B_333), B_334) | ~r1_tarski(B_333, B_334) | ~r2_xboole_0(A_332, B_333))), inference(resolution, [status(thm)], [c_24, c_2245])).
% 4.48/1.80  tff(c_2525, plain, (![B_341, B_342]: (~r1_tarski(B_341, B_342) | ~r2_xboole_0(B_342, B_341))), inference(resolution, [status(thm)], [c_2465, c_22])).
% 4.48/1.80  tff(c_2529, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_2525])).
% 4.48/1.80  tff(c_3342, plain, ('#skF_14'='#skF_12' | ~r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_3339, c_2529])).
% 4.48/1.80  tff(c_3353, plain, (~r1_tarski('#skF_12', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_2077, c_3342])).
% 4.48/1.80  tff(c_2426, plain, (![B_323, D_324, A_325, C_326]: (r2_hidden(B_323, D_324) | ~r2_hidden(k4_tarski(A_325, B_323), k2_zfmisc_1(C_326, D_324)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.80  tff(c_2435, plain, (![B_323, A_325]: (r2_hidden(B_323, '#skF_14') | ~r2_hidden(k4_tarski(A_325, B_323), k2_zfmisc_1('#skF_13', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_2426])).
% 4.48/1.80  tff(c_2518, plain, (![B_338, A_337]: (r2_hidden(B_338, '#skF_14') | ~r2_hidden(B_338, '#skF_12') | ~r2_hidden(A_337, '#skF_13'))), inference(resolution, [status(thm)], [c_2493, c_2435])).
% 4.48/1.80  tff(c_2597, plain, (![A_352]: (~r2_hidden(A_352, '#skF_13'))), inference(splitLeft, [status(thm)], [c_2518])).
% 4.48/1.80  tff(c_2622, plain, (v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_4, c_2597])).
% 4.48/1.80  tff(c_2629, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_2622, c_2238])).
% 4.48/1.80  tff(c_2635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2079, c_2629])).
% 4.48/1.80  tff(c_2637, plain, (![B_353]: (r2_hidden(B_353, '#skF_14') | ~r2_hidden(B_353, '#skF_12'))), inference(splitRight, [status(thm)], [c_2518])).
% 4.48/1.80  tff(c_3363, plain, (![A_404]: (r1_tarski(A_404, '#skF_14') | ~r2_hidden('#skF_2'(A_404, '#skF_14'), '#skF_12'))), inference(resolution, [status(thm)], [c_2637, c_8])).
% 4.48/1.80  tff(c_3371, plain, (r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_10, c_3363])).
% 4.48/1.80  tff(c_3377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3353, c_3353, c_3371])).
% 4.48/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.80  
% 4.48/1.80  Inference rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Ref     : 0
% 4.48/1.80  #Sup     : 706
% 4.48/1.80  #Fact    : 0
% 4.48/1.80  #Define  : 0
% 4.48/1.80  #Split   : 17
% 4.48/1.80  #Chain   : 0
% 4.48/1.80  #Close   : 0
% 4.48/1.80  
% 4.48/1.80  Ordering : KBO
% 4.48/1.80  
% 4.48/1.80  Simplification rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Subsume      : 218
% 4.48/1.80  #Demod        : 208
% 4.48/1.80  #Tautology    : 132
% 4.48/1.80  #SimpNegUnit  : 48
% 4.48/1.80  #BackRed      : 69
% 4.48/1.80  
% 4.48/1.80  #Partial instantiations: 0
% 4.48/1.80  #Strategies tried      : 1
% 4.48/1.80  
% 4.48/1.80  Timing (in seconds)
% 4.48/1.80  ----------------------
% 4.48/1.81  Preprocessing        : 0.32
% 4.48/1.81  Parsing              : 0.16
% 4.48/1.81  CNF conversion       : 0.03
% 4.48/1.81  Main loop            : 0.70
% 4.48/1.81  Inferencing          : 0.27
% 4.48/1.81  Reduction            : 0.20
% 4.48/1.81  Demodulation         : 0.13
% 4.48/1.81  BG Simplification    : 0.03
% 4.48/1.81  Subsumption          : 0.14
% 4.48/1.81  Abstraction          : 0.03
% 4.48/1.81  MUC search           : 0.00
% 4.48/1.81  Cooper               : 0.00
% 4.48/1.81  Total                : 1.08
% 4.48/1.81  Index Insertion      : 0.00
% 4.48/1.81  Index Deletion       : 0.00
% 4.48/1.81  Index Matching       : 0.00
% 4.48/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
