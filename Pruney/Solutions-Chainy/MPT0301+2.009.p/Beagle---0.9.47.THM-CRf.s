%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 19.31s
% Output     : CNFRefutation 19.49s
% Verified   : 
% Statistics : Number of formulae       :  255 (1458 expanded)
%              Number of leaves         :   39 ( 442 expanded)
%              Depth                    :   11
%              Number of atoms          :  328 (2807 expanded)
%              Number of equality atoms :  130 (2047 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_15 > #skF_10 > #skF_14 > #skF_13 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_87,axiom,(
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
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_106,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_156,plain,(
    ! [B_85] : k3_xboole_0(k1_xboole_0,B_85) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_20])).

tff(c_66976,plain,(
    ! [A_26175,B_26176,C_26177] :
      ( ~ r1_xboole_0(A_26175,B_26176)
      | ~ r2_hidden(C_26177,k3_xboole_0(A_26175,B_26176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66983,plain,(
    ! [B_85,C_26177] :
      ( ~ r1_xboole_0(k1_xboole_0,B_85)
      | ~ r2_hidden(C_26177,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_66976])).

tff(c_66990,plain,(
    ! [C_26177] : ~ r2_hidden(C_26177,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_66983])).

tff(c_82,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_136,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_137,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_252,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,k3_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_259,plain,(
    ! [B_85,C_97] :
      ( ~ r1_xboole_0(k1_xboole_0,B_85)
      | ~ r2_hidden(C_97,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_252])).

tff(c_266,plain,(
    ! [C_97] : ~ r2_hidden(C_97,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_92,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_234,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_1475,plain,(
    ! [E_191,F_192,A_193,B_194] :
      ( r2_hidden(k4_tarski(E_191,F_192),k2_zfmisc_1(A_193,B_194))
      | ~ r2_hidden(F_192,B_194)
      | ~ r2_hidden(E_191,A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1480,plain,(
    ! [E_191,F_192] :
      ( r2_hidden(k4_tarski(E_191,F_192),k1_xboole_0)
      | ~ r2_hidden(F_192,'#skF_15')
      | ~ r2_hidden(E_191,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1475])).

tff(c_1482,plain,(
    ! [F_192,E_191] :
      ( ~ r2_hidden(F_192,'#skF_15')
      | ~ r2_hidden(E_191,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_1480])).

tff(c_1484,plain,(
    ! [E_195] : ~ r2_hidden(E_195,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1508,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_12,c_1484])).

tff(c_1517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1508])).

tff(c_1519,plain,(
    ! [F_196] : ~ r2_hidden(F_196,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_1543,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_12,c_1519])).

tff(c_1552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1543])).

tff(c_1553,plain,(
    ! [B_85] : ~ r1_xboole_0(k1_xboole_0,B_85) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1619,plain,(
    ! [A_208,B_209] :
      ( ~ r2_hidden(A_208,B_209)
      | k4_xboole_0(k1_tarski(A_208),B_209) != k1_tarski(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1638,plain,(
    ! [A_208] : ~ r2_hidden(A_208,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1619])).

tff(c_1865,plain,(
    ! [A_236,B_237] :
      ( r2_hidden('#skF_2'(A_236,B_237),k3_xboole_0(A_236,B_237))
      | r1_xboole_0(A_236,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1876,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_85),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_1865])).

tff(c_1881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1553,c_1638,c_1876])).

tff(c_1882,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1884,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_1882])).

tff(c_1890,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_12])).

tff(c_63673,plain,(
    ! [A_25579,B_25580,D_25581] :
      ( r2_hidden('#skF_11'(A_25579,B_25580,k2_zfmisc_1(A_25579,B_25580),D_25581),B_25580)
      | ~ r2_hidden(D_25581,k2_zfmisc_1(A_25579,B_25580)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1901,plain,(
    ! [A_239] : k4_xboole_0('#skF_13',A_239) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_1884,c_20])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1944,plain,(
    ! [B_244] : k3_xboole_0('#skF_13',B_244) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_1901,c_18])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1949,plain,(
    ! [B_244,C_10] :
      ( ~ r1_xboole_0('#skF_13',B_244)
      | ~ r2_hidden(C_10,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1944,c_10])).

tff(c_2012,plain,(
    ! [C_10] : ~ r2_hidden(C_10,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_1949])).

tff(c_64516,plain,(
    ! [D_25758,A_25759] : ~ r2_hidden(D_25758,k2_zfmisc_1(A_25759,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_63673,c_2012])).

tff(c_64576,plain,(
    ! [A_25759] : k2_zfmisc_1(A_25759,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_1890,c_64516])).

tff(c_90,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_185,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_1888,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_185])).

tff(c_64580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64576,c_1888])).

tff(c_64581,plain,(
    ! [B_244] : ~ r1_xboole_0('#skF_13',B_244) ),
    inference(splitRight,[status(thm)],[c_1949])).

tff(c_1894,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_16])).

tff(c_64782,plain,(
    ! [A_25962,B_25963] :
      ( ~ r2_hidden(A_25962,B_25963)
      | k4_xboole_0(k1_tarski(A_25962),B_25963) != k1_tarski(A_25962) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64805,plain,(
    ! [A_25962] : ~ r2_hidden(A_25962,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1894,c_64782])).

tff(c_1910,plain,(
    ! [B_16] : k3_xboole_0('#skF_13',B_16) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_1901,c_18])).

tff(c_64926,plain,(
    ! [A_25981,B_25982] :
      ( r2_hidden('#skF_2'(A_25981,B_25982),k3_xboole_0(A_25981,B_25982))
      | r1_xboole_0(A_25981,B_25982) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64937,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_2'('#skF_13',B_16),'#skF_13')
      | r1_xboole_0('#skF_13',B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_64926])).

tff(c_64942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64581,c_64805,c_64937])).

tff(c_64943,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1882])).

tff(c_64951,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64943,c_12])).

tff(c_66463,plain,(
    ! [A_26113,B_26114,D_26115] :
      ( r2_hidden('#skF_10'(A_26113,B_26114,k2_zfmisc_1(A_26113,B_26114),D_26115),A_26113)
      | ~ r2_hidden(D_26115,k2_zfmisc_1(A_26113,B_26114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64950,plain,(
    ! [B_85] : k3_xboole_0('#skF_12',B_85) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64943,c_64943,c_156])).

tff(c_65013,plain,(
    ! [A_25987,B_25988,C_25989] :
      ( ~ r1_xboole_0(A_25987,B_25988)
      | ~ r2_hidden(C_25989,k3_xboole_0(A_25987,B_25988)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65016,plain,(
    ! [B_85,C_25989] :
      ( ~ r1_xboole_0('#skF_12',B_85)
      | ~ r2_hidden(C_25989,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64950,c_65013])).

tff(c_65064,plain,(
    ! [C_25989] : ~ r2_hidden(C_25989,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_65016])).

tff(c_66482,plain,(
    ! [D_26116,B_26117] : ~ r2_hidden(D_26116,k2_zfmisc_1('#skF_12',B_26117)) ),
    inference(resolution,[status(thm)],[c_66463,c_65064])).

tff(c_66522,plain,(
    ! [B_26117] : k2_zfmisc_1('#skF_12',B_26117) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_64951,c_66482])).

tff(c_64949,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64943,c_185])).

tff(c_66526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66522,c_64949])).

tff(c_66527,plain,(
    ! [B_85] : ~ r1_xboole_0('#skF_12',B_85) ),
    inference(splitRight,[status(thm)],[c_65016])).

tff(c_64955,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_12') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64943,c_16])).

tff(c_66743,plain,(
    ! [A_26152,B_26153] :
      ( ~ r2_hidden(A_26152,B_26153)
      | k4_xboole_0(k1_tarski(A_26152),B_26153) != k1_tarski(A_26152) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66766,plain,(
    ! [A_26152] : ~ r2_hidden(A_26152,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_64955,c_66743])).

tff(c_66887,plain,(
    ! [A_26165,B_26166] :
      ( r2_hidden('#skF_2'(A_26165,B_26166),k3_xboole_0(A_26165,B_26166))
      | r1_xboole_0(A_26165,B_26166) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66898,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_2'('#skF_12',B_85),'#skF_12')
      | r1_xboole_0('#skF_12',B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64950,c_66887])).

tff(c_66903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66527,c_66766,c_66898])).

tff(c_66905,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_68199,plain,(
    ! [E_26271,F_26272,A_26273,B_26274] :
      ( r2_hidden(k4_tarski(E_26271,F_26272),k2_zfmisc_1(A_26273,B_26274))
      | ~ r2_hidden(F_26272,B_26274)
      | ~ r2_hidden(E_26271,A_26273) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_68204,plain,(
    ! [E_26271,F_26272] :
      ( r2_hidden(k4_tarski(E_26271,F_26272),k1_xboole_0)
      | ~ r2_hidden(F_26272,'#skF_13')
      | ~ r2_hidden(E_26271,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66905,c_68199])).

tff(c_68209,plain,(
    ! [F_26272,E_26271] :
      ( ~ r2_hidden(F_26272,'#skF_13')
      | ~ r2_hidden(E_26271,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66990,c_68204])).

tff(c_68212,plain,(
    ! [E_26275] : ~ r2_hidden(E_26275,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_68209])).

tff(c_68242,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_12,c_68212])).

tff(c_68274,plain,(
    '#skF_15' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68242,c_136])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68273,plain,(
    '#skF_14' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68242,c_137])).

tff(c_66904,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_68207,plain,(
    ! [E_26271,F_26272] :
      ( r2_hidden(k4_tarski(E_26271,F_26272),k1_xboole_0)
      | ~ r2_hidden(F_26272,'#skF_15')
      | ~ r2_hidden(E_26271,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66904,c_68199])).

tff(c_68210,plain,(
    ! [F_26272,E_26271] :
      ( ~ r2_hidden(F_26272,'#skF_15')
      | ~ r2_hidden(E_26271,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66990,c_68207])).

tff(c_68486,plain,(
    ! [E_26291] : ~ r2_hidden(E_26291,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_68210])).

tff(c_68516,plain,(
    ! [B_2] : r1_tarski('#skF_14',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_68486])).

tff(c_67279,plain,(
    ! [C_26209,B_26210,A_26211] :
      ( r2_hidden(C_26209,B_26210)
      | ~ r2_hidden(C_26209,A_26211)
      | ~ r1_tarski(A_26211,B_26210) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67287,plain,(
    ! [A_11,B_26210] :
      ( r2_hidden('#skF_3'(A_11),B_26210)
      | ~ r1_tarski(A_11,B_26210)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_12,c_67279])).

tff(c_68240,plain,(
    ! [A_11] :
      ( ~ r1_tarski(A_11,'#skF_12')
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_67287,c_68212])).

tff(c_68556,plain,(
    ! [A_26296] :
      ( ~ r1_tarski(A_26296,'#skF_12')
      | A_26296 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68242,c_68240])).

tff(c_68560,plain,(
    '#skF_14' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_68516,c_68556])).

tff(c_68580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68273,c_68560])).

tff(c_68583,plain,(
    ! [F_26300] : ~ r2_hidden(F_26300,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_68210])).

tff(c_68613,plain,(
    ! [B_2] : r1_tarski('#skF_15',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_68583])).

tff(c_68655,plain,(
    ! [A_26305] :
      ( ~ r1_tarski(A_26305,'#skF_12')
      | A_26305 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68242,c_68240])).

tff(c_68659,plain,(
    '#skF_15' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_68613,c_68655])).

tff(c_68679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68274,c_68659])).

tff(c_68681,plain,(
    ! [F_26306] : ~ r2_hidden(F_26306,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_68209])).

tff(c_68711,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_12,c_68681])).

tff(c_68743,plain,(
    '#skF_15' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68711,c_136])).

tff(c_68742,plain,(
    '#skF_14' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68711,c_137])).

tff(c_68952,plain,(
    ! [E_26322] : ~ r2_hidden(E_26322,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_68210])).

tff(c_68982,plain,(
    ! [B_2] : r1_tarski('#skF_14',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_68952])).

tff(c_68709,plain,(
    ! [A_11] :
      ( ~ r1_tarski(A_11,'#skF_13')
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_67287,c_68681])).

tff(c_69121,plain,(
    ! [A_26332] :
      ( ~ r1_tarski(A_26332,'#skF_13')
      | A_26332 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68711,c_68709])).

tff(c_69125,plain,(
    '#skF_14' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_68982,c_69121])).

tff(c_69145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68742,c_69125])).

tff(c_69147,plain,(
    ! [F_26333] : ~ r2_hidden(F_26333,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_68210])).

tff(c_69177,plain,(
    ! [B_2] : r1_tarski('#skF_15',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_69147])).

tff(c_69364,plain,(
    ! [A_26348] :
      ( ~ r1_tarski(A_26348,'#skF_13')
      | A_26348 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68711,c_68709])).

tff(c_69368,plain,(
    '#skF_15' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_69177,c_69364])).

tff(c_69388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68743,c_69368])).

tff(c_69389,plain,(
    ! [B_85] : ~ r1_xboole_0(k1_xboole_0,B_85) ),
    inference(splitRight,[status(thm)],[c_66983])).

tff(c_69455,plain,(
    ! [A_26360,B_26361] :
      ( ~ r2_hidden(A_26360,B_26361)
      | k4_xboole_0(k1_tarski(A_26360),B_26361) != k1_tarski(A_26360) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_69474,plain,(
    ! [A_26360] : ~ r2_hidden(A_26360,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_69455])).

tff(c_69717,plain,(
    ! [A_26390,B_26391] :
      ( r2_hidden('#skF_2'(A_26390,B_26391),k3_xboole_0(A_26390,B_26391))
      | r1_xboole_0(A_26390,B_26391) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69728,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_85),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_69717])).

tff(c_69733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69389,c_69474,c_69728])).

tff(c_69735,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_69734,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_69745,plain,
    ( '#skF_14' = '#skF_12'
    | '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_69735,c_69734])).

tff(c_69746,plain,(
    '#skF_14' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_69745])).

tff(c_69749,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69746,c_69735])).

tff(c_69790,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69749,c_12])).

tff(c_155929,plain,(
    ! [A_58202,B_58203,D_58204] :
      ( r2_hidden('#skF_11'(A_58202,B_58203,k2_zfmisc_1(A_58202,B_58203),D_58204),B_58203)
      | ~ r2_hidden(D_58204,k2_zfmisc_1(A_58202,B_58203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_69823,plain,(
    ! [A_26403,B_26404] : k4_xboole_0(A_26403,k4_xboole_0(A_26403,B_26404)) = k3_xboole_0(A_26403,B_26404) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69737,plain,(
    ! [A_17] : k4_xboole_0('#skF_14',A_17) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_69735,c_20])).

tff(c_69771,plain,(
    ! [A_17] : k4_xboole_0('#skF_13',A_17) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69746,c_69746,c_69737])).

tff(c_69833,plain,(
    ! [B_26404] : k3_xboole_0('#skF_13',B_26404) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_69823,c_69771])).

tff(c_69910,plain,(
    ! [A_26413,B_26414,C_26415] :
      ( ~ r1_xboole_0(A_26413,B_26414)
      | ~ r2_hidden(C_26415,k3_xboole_0(A_26413,B_26414)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69917,plain,(
    ! [B_26404,C_26415] :
      ( ~ r1_xboole_0('#skF_13',B_26404)
      | ~ r2_hidden(C_26415,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69833,c_69910])).

tff(c_69941,plain,(
    ! [C_26415] : ~ r2_hidden(C_26415,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_69917])).

tff(c_156778,plain,(
    ! [D_58381,A_58382] : ~ r2_hidden(D_58381,k2_zfmisc_1(A_58382,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_155929,c_69941])).

tff(c_156838,plain,(
    ! [A_58382] : k2_zfmisc_1(A_58382,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_69790,c_156778])).

tff(c_86,plain,
    ( k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_69770,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69749,c_69746,c_69749,c_86])).

tff(c_156846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156838,c_69770])).

tff(c_156847,plain,(
    ! [B_26404] : ~ r1_xboole_0('#skF_13',B_26404) ),
    inference(splitRight,[status(thm)],[c_69917])).

tff(c_69738,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_14') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69735,c_16])).

tff(c_69759,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69746,c_69738])).

tff(c_156849,plain,(
    ! [A_58560,B_58561] :
      ( ~ r2_hidden(A_58560,B_58561)
      | k4_xboole_0(k1_tarski(A_58560),B_58561) != k1_tarski(A_58560) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156864,plain,(
    ! [A_58560] : ~ r2_hidden(A_58560,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_69759,c_156849])).

tff(c_157185,plain,(
    ! [A_58598,B_58599] :
      ( r2_hidden('#skF_2'(A_58598,B_58599),k3_xboole_0(A_58598,B_58599))
      | r1_xboole_0(A_58598,B_58599) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_157196,plain,(
    ! [B_26404] :
      ( r2_hidden('#skF_2'('#skF_13',B_26404),'#skF_13')
      | r1_xboole_0('#skF_13',B_26404) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69833,c_157185])).

tff(c_157201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156847,c_156864,c_157196])).

tff(c_157202,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_69745])).

tff(c_157206,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157202,c_69735])).

tff(c_157245,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157206,c_12])).

tff(c_196751,plain,(
    ! [A_76667,B_76668,D_76669] :
      ( r2_hidden('#skF_10'(A_76667,B_76668,k2_zfmisc_1(A_76667,B_76668),D_76669),A_76667)
      | ~ r2_hidden(D_76669,k2_zfmisc_1(A_76667,B_76668)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_157272,plain,(
    ! [A_58608,B_58609] : k4_xboole_0(A_58608,k4_xboole_0(A_58608,B_58609)) = k3_xboole_0(A_58608,B_58609) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_157217,plain,(
    ! [A_17] : k4_xboole_0('#skF_12',A_17) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157202,c_157202,c_69737])).

tff(c_157282,plain,(
    ! [B_58609] : k3_xboole_0('#skF_12',B_58609) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_157272,c_157217])).

tff(c_157309,plain,(
    ! [A_58611,B_58612,C_58613] :
      ( ~ r1_xboole_0(A_58611,B_58612)
      | ~ r2_hidden(C_58613,k3_xboole_0(A_58611,B_58612)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_157312,plain,(
    ! [B_58609,C_58613] :
      ( ~ r1_xboole_0('#skF_12',B_58609)
      | ~ r2_hidden(C_58613,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157282,c_157309])).

tff(c_157355,plain,(
    ! [C_58613] : ~ r2_hidden(C_58613,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_157312])).

tff(c_197182,plain,(
    ! [D_76758,B_76759] : ~ r2_hidden(D_76758,k2_zfmisc_1('#skF_12',B_76759)) ),
    inference(resolution,[status(thm)],[c_196751,c_157355])).

tff(c_197232,plain,(
    ! [B_76759] : k2_zfmisc_1('#skF_12',B_76759) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_157245,c_197182])).

tff(c_157253,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157206,c_157202,c_157206,c_86])).

tff(c_197236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197232,c_157253])).

tff(c_197237,plain,(
    ! [B_58609] : ~ r1_xboole_0('#skF_12',B_58609) ),
    inference(splitRight,[status(thm)],[c_157312])).

tff(c_157225,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_12') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157202,c_69738])).

tff(c_197395,plain,(
    ! [A_76877,B_76878] :
      ( ~ r2_hidden(A_76877,B_76878)
      | k4_xboole_0(k1_tarski(A_76877),B_76878) != k1_tarski(A_76877) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_197414,plain,(
    ! [A_76877] : ~ r2_hidden(A_76877,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_157225,c_197395])).

tff(c_197734,plain,(
    ! [A_76908,B_76909] :
      ( r2_hidden('#skF_2'(A_76908,B_76909),k3_xboole_0(A_76908,B_76909))
      | r1_xboole_0(A_76908,B_76909) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_197745,plain,(
    ! [B_58609] :
      ( r2_hidden('#skF_2'('#skF_12',B_58609),'#skF_12')
      | r1_xboole_0('#skF_12',B_58609) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157282,c_197734])).

tff(c_197750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197237,c_197414,c_197745])).

tff(c_197752,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_197799,plain,
    ( '#skF_15' = '#skF_13'
    | '#skF_15' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197752,c_197752,c_197752,c_84])).

tff(c_197800,plain,(
    '#skF_15' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_197799])).

tff(c_197791,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_15' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197752,c_12])).

tff(c_197801,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197800,c_197791])).

tff(c_260449,plain,(
    ! [A_101857,B_101858,D_101859] :
      ( r2_hidden('#skF_10'(A_101857,B_101858,k2_zfmisc_1(A_101857,B_101858),D_101859),A_101857)
      | ~ r2_hidden(D_101859,k2_zfmisc_1(A_101857,B_101858)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_197880,plain,(
    ! [A_76927,B_76928] : k4_xboole_0(A_76927,k4_xboole_0(A_76927,B_76928)) = k3_xboole_0(A_76927,B_76928) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_197753,plain,(
    ! [A_17] : k4_xboole_0('#skF_15',A_17) = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197752,c_197752,c_20])).

tff(c_197803,plain,(
    ! [A_17] : k4_xboole_0('#skF_12',A_17) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197800,c_197800,c_197753])).

tff(c_197910,plain,(
    ! [B_76929] : k3_xboole_0('#skF_12',B_76929) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_197880,c_197803])).

tff(c_197915,plain,(
    ! [B_76929,C_10] :
      ( ~ r1_xboole_0('#skF_12',B_76929)
      | ~ r2_hidden(C_10,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197910,c_10])).

tff(c_197976,plain,(
    ! [C_10] : ~ r2_hidden(C_10,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_197915])).

tff(c_261298,plain,(
    ! [D_102036,B_102037] : ~ r2_hidden(D_102036,k2_zfmisc_1('#skF_12',B_102037)) ),
    inference(resolution,[status(thm)],[c_260449,c_197976])).

tff(c_261366,plain,(
    ! [B_102037] : k2_zfmisc_1('#skF_12',B_102037) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_197801,c_261298])).

tff(c_197751,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_197761,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197752,c_197751])).

tff(c_197805,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197800,c_197761])).

tff(c_261370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261366,c_197805])).

tff(c_261371,plain,(
    ! [B_76929] : ~ r1_xboole_0('#skF_12',B_76929) ),
    inference(splitRight,[status(thm)],[c_197915])).

tff(c_197754,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_15') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197752,c_16])).

tff(c_197802,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_12') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197800,c_197754])).

tff(c_261430,plain,(
    ! [A_102224,B_102225] :
      ( ~ r2_hidden(A_102224,B_102225)
      | k4_xboole_0(k1_tarski(A_102224),B_102225) != k1_tarski(A_102224) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_261449,plain,(
    ! [A_102224] : ~ r2_hidden(A_102224,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_197802,c_261430])).

tff(c_197890,plain,(
    ! [B_76928] : k3_xboole_0('#skF_12',B_76928) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_197880,c_197803])).

tff(c_261694,plain,(
    ! [A_102254,B_102255] :
      ( r2_hidden('#skF_2'(A_102254,B_102255),k3_xboole_0(A_102254,B_102255))
      | r1_xboole_0(A_102254,B_102255) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_261705,plain,(
    ! [B_76928] :
      ( r2_hidden('#skF_2'('#skF_12',B_76928),'#skF_12')
      | r1_xboole_0('#skF_12',B_76928) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197890,c_261694])).

tff(c_261710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261371,c_261449,c_261705])).

tff(c_261711,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_197799])).

tff(c_261713,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261711,c_197791])).

tff(c_301421,plain,(
    ! [A_120499,B_120500,D_120501] :
      ( r2_hidden('#skF_11'(A_120499,B_120500,k2_zfmisc_1(A_120499,B_120500),D_120501),B_120500)
      | ~ r2_hidden(D_120501,k2_zfmisc_1(A_120499,B_120500)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_261786,plain,(
    ! [A_102266,B_102267] : k4_xboole_0(A_102266,k4_xboole_0(A_102266,B_102267)) = k3_xboole_0(A_102266,B_102267) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_261715,plain,(
    ! [A_17] : k4_xboole_0('#skF_13',A_17) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261711,c_261711,c_197753])).

tff(c_261796,plain,(
    ! [B_102267] : k3_xboole_0('#skF_13',B_102267) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_261786,c_261715])).

tff(c_261870,plain,(
    ! [A_102273,B_102274,C_102275] :
      ( ~ r1_xboole_0(A_102273,B_102274)
      | ~ r2_hidden(C_102275,k3_xboole_0(A_102273,B_102274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_261873,plain,(
    ! [B_102267,C_102275] :
      ( ~ r1_xboole_0('#skF_13',B_102267)
      | ~ r2_hidden(C_102275,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261796,c_261870])).

tff(c_261884,plain,(
    ! [C_102275] : ~ r2_hidden(C_102275,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_261873])).

tff(c_301852,plain,(
    ! [D_120590,A_120591] : ~ r2_hidden(D_120590,k2_zfmisc_1(A_120591,'#skF_13')) ),
    inference(resolution,[status(thm)],[c_301421,c_261884])).

tff(c_301902,plain,(
    ! [A_120591] : k2_zfmisc_1(A_120591,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_261713,c_301852])).

tff(c_261717,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261711,c_197761])).

tff(c_301906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_301902,c_261717])).

tff(c_301907,plain,(
    ! [B_102267] : ~ r1_xboole_0('#skF_13',B_102267) ),
    inference(splitRight,[status(thm)],[c_261873])).

tff(c_261714,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261711,c_197754])).

tff(c_302106,plain,(
    ! [A_120710,B_120711] :
      ( ~ r2_hidden(A_120710,B_120711)
      | k4_xboole_0(k1_tarski(A_120710),B_120711) != k1_tarski(A_120710) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_302129,plain,(
    ! [A_120710] : ~ r2_hidden(A_120710,'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_261714,c_302106])).

tff(c_302327,plain,(
    ! [A_120734,B_120735] :
      ( r2_hidden('#skF_2'(A_120734,B_120735),k3_xboole_0(A_120734,B_120735))
      | r1_xboole_0(A_120734,B_120735) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_302338,plain,(
    ! [B_102267] :
      ( r2_hidden('#skF_2'('#skF_13',B_102267),'#skF_13')
      | r1_xboole_0('#skF_13',B_102267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261796,c_302327])).

tff(c_302343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301907,c_302129,c_302338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.31/10.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.41/10.33  
% 19.41/10.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.41/10.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_15 > #skF_10 > #skF_14 > #skF_13 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 19.41/10.33  
% 19.41/10.33  %Foreground sorts:
% 19.41/10.33  
% 19.41/10.33  
% 19.41/10.33  %Background operators:
% 19.41/10.33  
% 19.41/10.33  
% 19.41/10.33  %Foreground operators:
% 19.41/10.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.41/10.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.41/10.33  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 19.41/10.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.41/10.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.41/10.33  tff('#skF_15', type, '#skF_15': $i).
% 19.41/10.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 19.41/10.33  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 19.41/10.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.41/10.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.41/10.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.41/10.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.41/10.33  tff('#skF_14', type, '#skF_14': $i).
% 19.41/10.33  tff('#skF_13', type, '#skF_13': $i).
% 19.41/10.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 19.41/10.33  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 19.41/10.33  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 19.41/10.33  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 19.41/10.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.41/10.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.41/10.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 19.41/10.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.41/10.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.41/10.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.41/10.33  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 19.41/10.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.41/10.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.41/10.33  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.41/10.33  tff('#skF_12', type, '#skF_12': $i).
% 19.41/10.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.41/10.33  
% 19.49/10.36  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 19.49/10.36  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.49/10.36  tff(f_62, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 19.49/10.36  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 19.49/10.36  tff(f_119, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 19.49/10.36  tff(f_87, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 19.49/10.36  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 19.49/10.36  tff(f_106, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 19.49/10.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.49/10.36  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.49/10.36  tff(c_146, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k4_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.49/10.36  tff(c_20, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 19.49/10.36  tff(c_156, plain, (![B_85]: (k3_xboole_0(k1_xboole_0, B_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_146, c_20])).
% 19.49/10.36  tff(c_66976, plain, (![A_26175, B_26176, C_26177]: (~r1_xboole_0(A_26175, B_26176) | ~r2_hidden(C_26177, k3_xboole_0(A_26175, B_26176)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_66983, plain, (![B_85, C_26177]: (~r1_xboole_0(k1_xboole_0, B_85) | ~r2_hidden(C_26177, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_66976])).
% 19.49/10.36  tff(c_66990, plain, (![C_26177]: (~r2_hidden(C_26177, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_66983])).
% 19.49/10.36  tff(c_82, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.49/10.36  tff(c_136, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_82])).
% 19.49/10.36  tff(c_88, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.49/10.36  tff(c_137, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_88])).
% 19.49/10.36  tff(c_252, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, k3_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_259, plain, (![B_85, C_97]: (~r1_xboole_0(k1_xboole_0, B_85) | ~r2_hidden(C_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_252])).
% 19.49/10.36  tff(c_266, plain, (![C_97]: (~r2_hidden(C_97, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_259])).
% 19.49/10.36  tff(c_92, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.49/10.36  tff(c_234, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_92])).
% 19.49/10.36  tff(c_1475, plain, (![E_191, F_192, A_193, B_194]: (r2_hidden(k4_tarski(E_191, F_192), k2_zfmisc_1(A_193, B_194)) | ~r2_hidden(F_192, B_194) | ~r2_hidden(E_191, A_193))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_1480, plain, (![E_191, F_192]: (r2_hidden(k4_tarski(E_191, F_192), k1_xboole_0) | ~r2_hidden(F_192, '#skF_15') | ~r2_hidden(E_191, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_1475])).
% 19.49/10.36  tff(c_1482, plain, (![F_192, E_191]: (~r2_hidden(F_192, '#skF_15') | ~r2_hidden(E_191, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_266, c_1480])).
% 19.49/10.36  tff(c_1484, plain, (![E_195]: (~r2_hidden(E_195, '#skF_14'))), inference(splitLeft, [status(thm)], [c_1482])).
% 19.49/10.36  tff(c_1508, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_12, c_1484])).
% 19.49/10.36  tff(c_1517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_1508])).
% 19.49/10.36  tff(c_1519, plain, (![F_196]: (~r2_hidden(F_196, '#skF_15'))), inference(splitRight, [status(thm)], [c_1482])).
% 19.49/10.36  tff(c_1543, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_12, c_1519])).
% 19.49/10.36  tff(c_1552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1543])).
% 19.49/10.36  tff(c_1553, plain, (![B_85]: (~r1_xboole_0(k1_xboole_0, B_85))), inference(splitRight, [status(thm)], [c_259])).
% 19.49/10.36  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.49/10.36  tff(c_1619, plain, (![A_208, B_209]: (~r2_hidden(A_208, B_209) | k4_xboole_0(k1_tarski(A_208), B_209)!=k1_tarski(A_208))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_1638, plain, (![A_208]: (~r2_hidden(A_208, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1619])).
% 19.49/10.36  tff(c_1865, plain, (![A_236, B_237]: (r2_hidden('#skF_2'(A_236, B_237), k3_xboole_0(A_236, B_237)) | r1_xboole_0(A_236, B_237))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_1876, plain, (![B_85]: (r2_hidden('#skF_2'(k1_xboole_0, B_85), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_156, c_1865])).
% 19.49/10.36  tff(c_1881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1553, c_1638, c_1876])).
% 19.49/10.36  tff(c_1882, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_92])).
% 19.49/10.36  tff(c_1884, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_1882])).
% 19.49/10.36  tff(c_1890, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_12])).
% 19.49/10.36  tff(c_63673, plain, (![A_25579, B_25580, D_25581]: (r2_hidden('#skF_11'(A_25579, B_25580, k2_zfmisc_1(A_25579, B_25580), D_25581), B_25580) | ~r2_hidden(D_25581, k2_zfmisc_1(A_25579, B_25580)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_1901, plain, (![A_239]: (k4_xboole_0('#skF_13', A_239)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_1884, c_20])).
% 19.49/10.36  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.49/10.36  tff(c_1944, plain, (![B_244]: (k3_xboole_0('#skF_13', B_244)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1901, c_18])).
% 19.49/10.36  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_1949, plain, (![B_244, C_10]: (~r1_xboole_0('#skF_13', B_244) | ~r2_hidden(C_10, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1944, c_10])).
% 19.49/10.36  tff(c_2012, plain, (![C_10]: (~r2_hidden(C_10, '#skF_13'))), inference(splitLeft, [status(thm)], [c_1949])).
% 19.49/10.36  tff(c_64516, plain, (![D_25758, A_25759]: (~r2_hidden(D_25758, k2_zfmisc_1(A_25759, '#skF_13')))), inference(resolution, [status(thm)], [c_63673, c_2012])).
% 19.49/10.36  tff(c_64576, plain, (![A_25759]: (k2_zfmisc_1(A_25759, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_1890, c_64516])).
% 19.49/10.36  tff(c_90, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.49/10.36  tff(c_185, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 19.49/10.36  tff(c_1888, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_185])).
% 19.49/10.36  tff(c_64580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64576, c_1888])).
% 19.49/10.36  tff(c_64581, plain, (![B_244]: (~r1_xboole_0('#skF_13', B_244))), inference(splitRight, [status(thm)], [c_1949])).
% 19.49/10.36  tff(c_1894, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_16])).
% 19.49/10.36  tff(c_64782, plain, (![A_25962, B_25963]: (~r2_hidden(A_25962, B_25963) | k4_xboole_0(k1_tarski(A_25962), B_25963)!=k1_tarski(A_25962))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_64805, plain, (![A_25962]: (~r2_hidden(A_25962, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1894, c_64782])).
% 19.49/10.36  tff(c_1910, plain, (![B_16]: (k3_xboole_0('#skF_13', B_16)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1901, c_18])).
% 19.49/10.36  tff(c_64926, plain, (![A_25981, B_25982]: (r2_hidden('#skF_2'(A_25981, B_25982), k3_xboole_0(A_25981, B_25982)) | r1_xboole_0(A_25981, B_25982))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_64937, plain, (![B_16]: (r2_hidden('#skF_2'('#skF_13', B_16), '#skF_13') | r1_xboole_0('#skF_13', B_16))), inference(superposition, [status(thm), theory('equality')], [c_1910, c_64926])).
% 19.49/10.36  tff(c_64942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64581, c_64805, c_64937])).
% 19.49/10.36  tff(c_64943, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_1882])).
% 19.49/10.36  tff(c_64951, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_64943, c_12])).
% 19.49/10.36  tff(c_66463, plain, (![A_26113, B_26114, D_26115]: (r2_hidden('#skF_10'(A_26113, B_26114, k2_zfmisc_1(A_26113, B_26114), D_26115), A_26113) | ~r2_hidden(D_26115, k2_zfmisc_1(A_26113, B_26114)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_64950, plain, (![B_85]: (k3_xboole_0('#skF_12', B_85)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_64943, c_64943, c_156])).
% 19.49/10.36  tff(c_65013, plain, (![A_25987, B_25988, C_25989]: (~r1_xboole_0(A_25987, B_25988) | ~r2_hidden(C_25989, k3_xboole_0(A_25987, B_25988)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_65016, plain, (![B_85, C_25989]: (~r1_xboole_0('#skF_12', B_85) | ~r2_hidden(C_25989, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_64950, c_65013])).
% 19.49/10.36  tff(c_65064, plain, (![C_25989]: (~r2_hidden(C_25989, '#skF_12'))), inference(splitLeft, [status(thm)], [c_65016])).
% 19.49/10.36  tff(c_66482, plain, (![D_26116, B_26117]: (~r2_hidden(D_26116, k2_zfmisc_1('#skF_12', B_26117)))), inference(resolution, [status(thm)], [c_66463, c_65064])).
% 19.49/10.36  tff(c_66522, plain, (![B_26117]: (k2_zfmisc_1('#skF_12', B_26117)='#skF_12')), inference(resolution, [status(thm)], [c_64951, c_66482])).
% 19.49/10.36  tff(c_64949, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_64943, c_185])).
% 19.49/10.36  tff(c_66526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66522, c_64949])).
% 19.49/10.36  tff(c_66527, plain, (![B_85]: (~r1_xboole_0('#skF_12', B_85))), inference(splitRight, [status(thm)], [c_65016])).
% 19.49/10.36  tff(c_64955, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_12')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_64943, c_16])).
% 19.49/10.36  tff(c_66743, plain, (![A_26152, B_26153]: (~r2_hidden(A_26152, B_26153) | k4_xboole_0(k1_tarski(A_26152), B_26153)!=k1_tarski(A_26152))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_66766, plain, (![A_26152]: (~r2_hidden(A_26152, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_64955, c_66743])).
% 19.49/10.36  tff(c_66887, plain, (![A_26165, B_26166]: (r2_hidden('#skF_2'(A_26165, B_26166), k3_xboole_0(A_26165, B_26166)) | r1_xboole_0(A_26165, B_26166))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_66898, plain, (![B_85]: (r2_hidden('#skF_2'('#skF_12', B_85), '#skF_12') | r1_xboole_0('#skF_12', B_85))), inference(superposition, [status(thm), theory('equality')], [c_64950, c_66887])).
% 19.49/10.36  tff(c_66903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66527, c_66766, c_66898])).
% 19.49/10.36  tff(c_66905, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 19.49/10.36  tff(c_68199, plain, (![E_26271, F_26272, A_26273, B_26274]: (r2_hidden(k4_tarski(E_26271, F_26272), k2_zfmisc_1(A_26273, B_26274)) | ~r2_hidden(F_26272, B_26274) | ~r2_hidden(E_26271, A_26273))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_68204, plain, (![E_26271, F_26272]: (r2_hidden(k4_tarski(E_26271, F_26272), k1_xboole_0) | ~r2_hidden(F_26272, '#skF_13') | ~r2_hidden(E_26271, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_66905, c_68199])).
% 19.49/10.36  tff(c_68209, plain, (![F_26272, E_26271]: (~r2_hidden(F_26272, '#skF_13') | ~r2_hidden(E_26271, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_66990, c_68204])).
% 19.49/10.36  tff(c_68212, plain, (![E_26275]: (~r2_hidden(E_26275, '#skF_12'))), inference(splitLeft, [status(thm)], [c_68209])).
% 19.49/10.36  tff(c_68242, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_12, c_68212])).
% 19.49/10.36  tff(c_68274, plain, ('#skF_15'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_68242, c_136])).
% 19.49/10.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.49/10.36  tff(c_68273, plain, ('#skF_14'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_68242, c_137])).
% 19.49/10.36  tff(c_66904, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 19.49/10.36  tff(c_68207, plain, (![E_26271, F_26272]: (r2_hidden(k4_tarski(E_26271, F_26272), k1_xboole_0) | ~r2_hidden(F_26272, '#skF_15') | ~r2_hidden(E_26271, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_66904, c_68199])).
% 19.49/10.36  tff(c_68210, plain, (![F_26272, E_26271]: (~r2_hidden(F_26272, '#skF_15') | ~r2_hidden(E_26271, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_66990, c_68207])).
% 19.49/10.36  tff(c_68486, plain, (![E_26291]: (~r2_hidden(E_26291, '#skF_14'))), inference(splitLeft, [status(thm)], [c_68210])).
% 19.49/10.36  tff(c_68516, plain, (![B_2]: (r1_tarski('#skF_14', B_2))), inference(resolution, [status(thm)], [c_6, c_68486])).
% 19.49/10.36  tff(c_67279, plain, (![C_26209, B_26210, A_26211]: (r2_hidden(C_26209, B_26210) | ~r2_hidden(C_26209, A_26211) | ~r1_tarski(A_26211, B_26210))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.49/10.36  tff(c_67287, plain, (![A_11, B_26210]: (r2_hidden('#skF_3'(A_11), B_26210) | ~r1_tarski(A_11, B_26210) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_12, c_67279])).
% 19.49/10.36  tff(c_68240, plain, (![A_11]: (~r1_tarski(A_11, '#skF_12') | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_67287, c_68212])).
% 19.49/10.36  tff(c_68556, plain, (![A_26296]: (~r1_tarski(A_26296, '#skF_12') | A_26296='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_68242, c_68240])).
% 19.49/10.36  tff(c_68560, plain, ('#skF_14'='#skF_12'), inference(resolution, [status(thm)], [c_68516, c_68556])).
% 19.49/10.36  tff(c_68580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68273, c_68560])).
% 19.49/10.36  tff(c_68583, plain, (![F_26300]: (~r2_hidden(F_26300, '#skF_15'))), inference(splitRight, [status(thm)], [c_68210])).
% 19.49/10.36  tff(c_68613, plain, (![B_2]: (r1_tarski('#skF_15', B_2))), inference(resolution, [status(thm)], [c_6, c_68583])).
% 19.49/10.36  tff(c_68655, plain, (![A_26305]: (~r1_tarski(A_26305, '#skF_12') | A_26305='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_68242, c_68240])).
% 19.49/10.36  tff(c_68659, plain, ('#skF_15'='#skF_12'), inference(resolution, [status(thm)], [c_68613, c_68655])).
% 19.49/10.36  tff(c_68679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68274, c_68659])).
% 19.49/10.36  tff(c_68681, plain, (![F_26306]: (~r2_hidden(F_26306, '#skF_13'))), inference(splitRight, [status(thm)], [c_68209])).
% 19.49/10.36  tff(c_68711, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_12, c_68681])).
% 19.49/10.36  tff(c_68743, plain, ('#skF_15'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_68711, c_136])).
% 19.49/10.36  tff(c_68742, plain, ('#skF_14'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_68711, c_137])).
% 19.49/10.36  tff(c_68952, plain, (![E_26322]: (~r2_hidden(E_26322, '#skF_14'))), inference(splitLeft, [status(thm)], [c_68210])).
% 19.49/10.36  tff(c_68982, plain, (![B_2]: (r1_tarski('#skF_14', B_2))), inference(resolution, [status(thm)], [c_6, c_68952])).
% 19.49/10.36  tff(c_68709, plain, (![A_11]: (~r1_tarski(A_11, '#skF_13') | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_67287, c_68681])).
% 19.49/10.36  tff(c_69121, plain, (![A_26332]: (~r1_tarski(A_26332, '#skF_13') | A_26332='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_68711, c_68709])).
% 19.49/10.36  tff(c_69125, plain, ('#skF_14'='#skF_13'), inference(resolution, [status(thm)], [c_68982, c_69121])).
% 19.49/10.36  tff(c_69145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68742, c_69125])).
% 19.49/10.36  tff(c_69147, plain, (![F_26333]: (~r2_hidden(F_26333, '#skF_15'))), inference(splitRight, [status(thm)], [c_68210])).
% 19.49/10.36  tff(c_69177, plain, (![B_2]: (r1_tarski('#skF_15', B_2))), inference(resolution, [status(thm)], [c_6, c_69147])).
% 19.49/10.36  tff(c_69364, plain, (![A_26348]: (~r1_tarski(A_26348, '#skF_13') | A_26348='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_68711, c_68709])).
% 19.49/10.36  tff(c_69368, plain, ('#skF_15'='#skF_13'), inference(resolution, [status(thm)], [c_69177, c_69364])).
% 19.49/10.36  tff(c_69388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68743, c_69368])).
% 19.49/10.36  tff(c_69389, plain, (![B_85]: (~r1_xboole_0(k1_xboole_0, B_85))), inference(splitRight, [status(thm)], [c_66983])).
% 19.49/10.36  tff(c_69455, plain, (![A_26360, B_26361]: (~r2_hidden(A_26360, B_26361) | k4_xboole_0(k1_tarski(A_26360), B_26361)!=k1_tarski(A_26360))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_69474, plain, (![A_26360]: (~r2_hidden(A_26360, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_69455])).
% 19.49/10.36  tff(c_69717, plain, (![A_26390, B_26391]: (r2_hidden('#skF_2'(A_26390, B_26391), k3_xboole_0(A_26390, B_26391)) | r1_xboole_0(A_26390, B_26391))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_69728, plain, (![B_85]: (r2_hidden('#skF_2'(k1_xboole_0, B_85), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_156, c_69717])).
% 19.49/10.36  tff(c_69733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69389, c_69474, c_69728])).
% 19.49/10.36  tff(c_69735, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_88])).
% 19.49/10.36  tff(c_69734, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_88])).
% 19.49/10.36  tff(c_69745, plain, ('#skF_14'='#skF_12' | '#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_69735, c_69734])).
% 19.49/10.36  tff(c_69746, plain, ('#skF_14'='#skF_13'), inference(splitLeft, [status(thm)], [c_69745])).
% 19.49/10.36  tff(c_69749, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_69746, c_69735])).
% 19.49/10.36  tff(c_69790, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_69749, c_12])).
% 19.49/10.36  tff(c_155929, plain, (![A_58202, B_58203, D_58204]: (r2_hidden('#skF_11'(A_58202, B_58203, k2_zfmisc_1(A_58202, B_58203), D_58204), B_58203) | ~r2_hidden(D_58204, k2_zfmisc_1(A_58202, B_58203)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_69823, plain, (![A_26403, B_26404]: (k4_xboole_0(A_26403, k4_xboole_0(A_26403, B_26404))=k3_xboole_0(A_26403, B_26404))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.49/10.36  tff(c_69737, plain, (![A_17]: (k4_xboole_0('#skF_14', A_17)='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_69735, c_20])).
% 19.49/10.36  tff(c_69771, plain, (![A_17]: (k4_xboole_0('#skF_13', A_17)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_69746, c_69746, c_69737])).
% 19.49/10.36  tff(c_69833, plain, (![B_26404]: (k3_xboole_0('#skF_13', B_26404)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_69823, c_69771])).
% 19.49/10.36  tff(c_69910, plain, (![A_26413, B_26414, C_26415]: (~r1_xboole_0(A_26413, B_26414) | ~r2_hidden(C_26415, k3_xboole_0(A_26413, B_26414)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_69917, plain, (![B_26404, C_26415]: (~r1_xboole_0('#skF_13', B_26404) | ~r2_hidden(C_26415, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_69833, c_69910])).
% 19.49/10.36  tff(c_69941, plain, (![C_26415]: (~r2_hidden(C_26415, '#skF_13'))), inference(splitLeft, [status(thm)], [c_69917])).
% 19.49/10.36  tff(c_156778, plain, (![D_58381, A_58382]: (~r2_hidden(D_58381, k2_zfmisc_1(A_58382, '#skF_13')))), inference(resolution, [status(thm)], [c_155929, c_69941])).
% 19.49/10.36  tff(c_156838, plain, (![A_58382]: (k2_zfmisc_1(A_58382, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_69790, c_156778])).
% 19.49/10.36  tff(c_86, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0 | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.49/10.36  tff(c_69770, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_69749, c_69746, c_69749, c_86])).
% 19.49/10.36  tff(c_156846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156838, c_69770])).
% 19.49/10.36  tff(c_156847, plain, (![B_26404]: (~r1_xboole_0('#skF_13', B_26404))), inference(splitRight, [status(thm)], [c_69917])).
% 19.49/10.36  tff(c_69738, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_14')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_69735, c_16])).
% 19.49/10.36  tff(c_69759, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_69746, c_69738])).
% 19.49/10.36  tff(c_156849, plain, (![A_58560, B_58561]: (~r2_hidden(A_58560, B_58561) | k4_xboole_0(k1_tarski(A_58560), B_58561)!=k1_tarski(A_58560))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_156864, plain, (![A_58560]: (~r2_hidden(A_58560, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_69759, c_156849])).
% 19.49/10.36  tff(c_157185, plain, (![A_58598, B_58599]: (r2_hidden('#skF_2'(A_58598, B_58599), k3_xboole_0(A_58598, B_58599)) | r1_xboole_0(A_58598, B_58599))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_157196, plain, (![B_26404]: (r2_hidden('#skF_2'('#skF_13', B_26404), '#skF_13') | r1_xboole_0('#skF_13', B_26404))), inference(superposition, [status(thm), theory('equality')], [c_69833, c_157185])).
% 19.49/10.36  tff(c_157201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156847, c_156864, c_157196])).
% 19.49/10.36  tff(c_157202, plain, ('#skF_14'='#skF_12'), inference(splitRight, [status(thm)], [c_69745])).
% 19.49/10.36  tff(c_157206, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_157202, c_69735])).
% 19.49/10.36  tff(c_157245, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_157206, c_12])).
% 19.49/10.36  tff(c_196751, plain, (![A_76667, B_76668, D_76669]: (r2_hidden('#skF_10'(A_76667, B_76668, k2_zfmisc_1(A_76667, B_76668), D_76669), A_76667) | ~r2_hidden(D_76669, k2_zfmisc_1(A_76667, B_76668)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_157272, plain, (![A_58608, B_58609]: (k4_xboole_0(A_58608, k4_xboole_0(A_58608, B_58609))=k3_xboole_0(A_58608, B_58609))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.49/10.36  tff(c_157217, plain, (![A_17]: (k4_xboole_0('#skF_12', A_17)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_157202, c_157202, c_69737])).
% 19.49/10.36  tff(c_157282, plain, (![B_58609]: (k3_xboole_0('#skF_12', B_58609)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_157272, c_157217])).
% 19.49/10.36  tff(c_157309, plain, (![A_58611, B_58612, C_58613]: (~r1_xboole_0(A_58611, B_58612) | ~r2_hidden(C_58613, k3_xboole_0(A_58611, B_58612)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_157312, plain, (![B_58609, C_58613]: (~r1_xboole_0('#skF_12', B_58609) | ~r2_hidden(C_58613, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_157282, c_157309])).
% 19.49/10.36  tff(c_157355, plain, (![C_58613]: (~r2_hidden(C_58613, '#skF_12'))), inference(splitLeft, [status(thm)], [c_157312])).
% 19.49/10.36  tff(c_197182, plain, (![D_76758, B_76759]: (~r2_hidden(D_76758, k2_zfmisc_1('#skF_12', B_76759)))), inference(resolution, [status(thm)], [c_196751, c_157355])).
% 19.49/10.36  tff(c_197232, plain, (![B_76759]: (k2_zfmisc_1('#skF_12', B_76759)='#skF_12')), inference(resolution, [status(thm)], [c_157245, c_197182])).
% 19.49/10.36  tff(c_157253, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_157206, c_157202, c_157206, c_86])).
% 19.49/10.36  tff(c_197236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197232, c_157253])).
% 19.49/10.36  tff(c_197237, plain, (![B_58609]: (~r1_xboole_0('#skF_12', B_58609))), inference(splitRight, [status(thm)], [c_157312])).
% 19.49/10.36  tff(c_157225, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_12')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_157202, c_69738])).
% 19.49/10.36  tff(c_197395, plain, (![A_76877, B_76878]: (~r2_hidden(A_76877, B_76878) | k4_xboole_0(k1_tarski(A_76877), B_76878)!=k1_tarski(A_76877))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_197414, plain, (![A_76877]: (~r2_hidden(A_76877, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_157225, c_197395])).
% 19.49/10.36  tff(c_197734, plain, (![A_76908, B_76909]: (r2_hidden('#skF_2'(A_76908, B_76909), k3_xboole_0(A_76908, B_76909)) | r1_xboole_0(A_76908, B_76909))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_197745, plain, (![B_58609]: (r2_hidden('#skF_2'('#skF_12', B_58609), '#skF_12') | r1_xboole_0('#skF_12', B_58609))), inference(superposition, [status(thm), theory('equality')], [c_157282, c_197734])).
% 19.49/10.36  tff(c_197750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197237, c_197414, c_197745])).
% 19.49/10.36  tff(c_197752, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_82])).
% 19.49/10.36  tff(c_84, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_119])).
% 19.49/10.36  tff(c_197799, plain, ('#skF_15'='#skF_13' | '#skF_15'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_197752, c_197752, c_197752, c_84])).
% 19.49/10.36  tff(c_197800, plain, ('#skF_15'='#skF_12'), inference(splitLeft, [status(thm)], [c_197799])).
% 19.49/10.36  tff(c_197791, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_197752, c_12])).
% 19.49/10.36  tff(c_197801, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_197800, c_197791])).
% 19.49/10.36  tff(c_260449, plain, (![A_101857, B_101858, D_101859]: (r2_hidden('#skF_10'(A_101857, B_101858, k2_zfmisc_1(A_101857, B_101858), D_101859), A_101857) | ~r2_hidden(D_101859, k2_zfmisc_1(A_101857, B_101858)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_197880, plain, (![A_76927, B_76928]: (k4_xboole_0(A_76927, k4_xboole_0(A_76927, B_76928))=k3_xboole_0(A_76927, B_76928))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.49/10.36  tff(c_197753, plain, (![A_17]: (k4_xboole_0('#skF_15', A_17)='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_197752, c_197752, c_20])).
% 19.49/10.36  tff(c_197803, plain, (![A_17]: (k4_xboole_0('#skF_12', A_17)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_197800, c_197800, c_197753])).
% 19.49/10.36  tff(c_197910, plain, (![B_76929]: (k3_xboole_0('#skF_12', B_76929)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_197880, c_197803])).
% 19.49/10.36  tff(c_197915, plain, (![B_76929, C_10]: (~r1_xboole_0('#skF_12', B_76929) | ~r2_hidden(C_10, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_197910, c_10])).
% 19.49/10.36  tff(c_197976, plain, (![C_10]: (~r2_hidden(C_10, '#skF_12'))), inference(splitLeft, [status(thm)], [c_197915])).
% 19.49/10.36  tff(c_261298, plain, (![D_102036, B_102037]: (~r2_hidden(D_102036, k2_zfmisc_1('#skF_12', B_102037)))), inference(resolution, [status(thm)], [c_260449, c_197976])).
% 19.49/10.36  tff(c_261366, plain, (![B_102037]: (k2_zfmisc_1('#skF_12', B_102037)='#skF_12')), inference(resolution, [status(thm)], [c_197801, c_261298])).
% 19.49/10.36  tff(c_197751, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 19.49/10.36  tff(c_197761, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_197752, c_197751])).
% 19.49/10.36  tff(c_197805, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_197800, c_197761])).
% 19.49/10.36  tff(c_261370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261366, c_197805])).
% 19.49/10.36  tff(c_261371, plain, (![B_76929]: (~r1_xboole_0('#skF_12', B_76929))), inference(splitRight, [status(thm)], [c_197915])).
% 19.49/10.36  tff(c_197754, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_15')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_197752, c_16])).
% 19.49/10.36  tff(c_197802, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_12')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_197800, c_197754])).
% 19.49/10.36  tff(c_261430, plain, (![A_102224, B_102225]: (~r2_hidden(A_102224, B_102225) | k4_xboole_0(k1_tarski(A_102224), B_102225)!=k1_tarski(A_102224))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_261449, plain, (![A_102224]: (~r2_hidden(A_102224, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_197802, c_261430])).
% 19.49/10.36  tff(c_197890, plain, (![B_76928]: (k3_xboole_0('#skF_12', B_76928)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_197880, c_197803])).
% 19.49/10.36  tff(c_261694, plain, (![A_102254, B_102255]: (r2_hidden('#skF_2'(A_102254, B_102255), k3_xboole_0(A_102254, B_102255)) | r1_xboole_0(A_102254, B_102255))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_261705, plain, (![B_76928]: (r2_hidden('#skF_2'('#skF_12', B_76928), '#skF_12') | r1_xboole_0('#skF_12', B_76928))), inference(superposition, [status(thm), theory('equality')], [c_197890, c_261694])).
% 19.49/10.36  tff(c_261710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261371, c_261449, c_261705])).
% 19.49/10.36  tff(c_261711, plain, ('#skF_15'='#skF_13'), inference(splitRight, [status(thm)], [c_197799])).
% 19.49/10.36  tff(c_261713, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_261711, c_197791])).
% 19.49/10.36  tff(c_301421, plain, (![A_120499, B_120500, D_120501]: (r2_hidden('#skF_11'(A_120499, B_120500, k2_zfmisc_1(A_120499, B_120500), D_120501), B_120500) | ~r2_hidden(D_120501, k2_zfmisc_1(A_120499, B_120500)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.49/10.36  tff(c_261786, plain, (![A_102266, B_102267]: (k4_xboole_0(A_102266, k4_xboole_0(A_102266, B_102267))=k3_xboole_0(A_102266, B_102267))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.49/10.36  tff(c_261715, plain, (![A_17]: (k4_xboole_0('#skF_13', A_17)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_261711, c_261711, c_197753])).
% 19.49/10.36  tff(c_261796, plain, (![B_102267]: (k3_xboole_0('#skF_13', B_102267)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_261786, c_261715])).
% 19.49/10.36  tff(c_261870, plain, (![A_102273, B_102274, C_102275]: (~r1_xboole_0(A_102273, B_102274) | ~r2_hidden(C_102275, k3_xboole_0(A_102273, B_102274)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_261873, plain, (![B_102267, C_102275]: (~r1_xboole_0('#skF_13', B_102267) | ~r2_hidden(C_102275, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_261796, c_261870])).
% 19.49/10.36  tff(c_261884, plain, (![C_102275]: (~r2_hidden(C_102275, '#skF_13'))), inference(splitLeft, [status(thm)], [c_261873])).
% 19.49/10.36  tff(c_301852, plain, (![D_120590, A_120591]: (~r2_hidden(D_120590, k2_zfmisc_1(A_120591, '#skF_13')))), inference(resolution, [status(thm)], [c_301421, c_261884])).
% 19.49/10.36  tff(c_301902, plain, (![A_120591]: (k2_zfmisc_1(A_120591, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_261713, c_301852])).
% 19.49/10.36  tff(c_261717, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_261711, c_197761])).
% 19.49/10.36  tff(c_301906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_301902, c_261717])).
% 19.49/10.36  tff(c_301907, plain, (![B_102267]: (~r1_xboole_0('#skF_13', B_102267))), inference(splitRight, [status(thm)], [c_261873])).
% 19.49/10.36  tff(c_261714, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_261711, c_197754])).
% 19.49/10.36  tff(c_302106, plain, (![A_120710, B_120711]: (~r2_hidden(A_120710, B_120711) | k4_xboole_0(k1_tarski(A_120710), B_120711)!=k1_tarski(A_120710))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.49/10.36  tff(c_302129, plain, (![A_120710]: (~r2_hidden(A_120710, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_261714, c_302106])).
% 19.49/10.36  tff(c_302327, plain, (![A_120734, B_120735]: (r2_hidden('#skF_2'(A_120734, B_120735), k3_xboole_0(A_120734, B_120735)) | r1_xboole_0(A_120734, B_120735))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.49/10.36  tff(c_302338, plain, (![B_102267]: (r2_hidden('#skF_2'('#skF_13', B_102267), '#skF_13') | r1_xboole_0('#skF_13', B_102267))), inference(superposition, [status(thm), theory('equality')], [c_261796, c_302327])).
% 19.49/10.36  tff(c_302343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301907, c_302129, c_302338])).
% 19.49/10.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.49/10.36  
% 19.49/10.36  Inference rules
% 19.49/10.36  ----------------------
% 19.49/10.36  #Ref     : 0
% 19.49/10.36  #Sup     : 35673
% 19.49/10.36  #Fact    : 50
% 19.49/10.36  #Define  : 0
% 19.49/10.36  #Split   : 24
% 19.49/10.36  #Chain   : 0
% 19.49/10.36  #Close   : 0
% 19.49/10.36  
% 19.49/10.36  Ordering : KBO
% 19.49/10.36  
% 19.49/10.36  Simplification rules
% 19.49/10.36  ----------------------
% 19.49/10.36  #Subsume      : 8494
% 19.49/10.36  #Demod        : 12651
% 19.49/10.36  #Tautology    : 6486
% 19.49/10.36  #SimpNegUnit  : 1110
% 19.49/10.36  #BackRed      : 202
% 19.49/10.36  
% 19.49/10.36  #Partial instantiations: 64992
% 19.49/10.36  #Strategies tried      : 1
% 19.49/10.36  
% 19.49/10.36  Timing (in seconds)
% 19.49/10.36  ----------------------
% 19.49/10.36  Preprocessing        : 0.33
% 19.49/10.36  Parsing              : 0.16
% 19.49/10.37  CNF conversion       : 0.03
% 19.49/10.37  Main loop            : 9.24
% 19.49/10.37  Inferencing          : 3.27
% 19.49/10.37  Reduction            : 3.07
% 19.49/10.37  Demodulation         : 1.99
% 19.49/10.37  BG Simplification    : 0.39
% 19.49/10.37  Subsumption          : 2.00
% 19.49/10.37  Abstraction          : 0.39
% 19.49/10.37  MUC search           : 0.00
% 19.49/10.37  Cooper               : 0.00
% 19.49/10.37  Total                : 9.64
% 19.49/10.37  Index Insertion      : 0.00
% 19.49/10.37  Index Deletion       : 0.00
% 19.49/10.37  Index Matching       : 0.00
% 19.49/10.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
