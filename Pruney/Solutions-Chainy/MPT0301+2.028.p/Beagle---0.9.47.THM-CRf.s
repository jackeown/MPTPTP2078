%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  180 (1724 expanded)
%              Number of leaves         :   31 ( 511 expanded)
%              Depth                    :   12
%              Number of atoms          :  231 (3325 expanded)
%              Number of equality atoms :  115 (2800 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_7124,plain,(
    ! [A_793,B_794,C_795] :
      ( r2_hidden('#skF_4'(A_793,B_794,C_795),B_794)
      | r2_hidden('#skF_5'(A_793,B_794,C_795),C_795)
      | k2_zfmisc_1(A_793,B_794) = C_795 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6130,plain,(
    ! [A_690,B_691,C_692] :
      ( r2_hidden('#skF_4'(A_690,B_691,C_692),B_691)
      | r2_hidden('#skF_5'(A_690,B_691,C_692),C_692)
      | k2_zfmisc_1(A_690,B_691) = C_692 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5300,plain,(
    ! [A_604,B_605,C_606] :
      ( r2_hidden('#skF_4'(A_604,B_605,C_606),B_605)
      | r2_hidden('#skF_5'(A_604,B_605,C_606),C_606)
      | k2_zfmisc_1(A_604,B_605) = C_606 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4012,plain,(
    ! [A_471,B_472,C_473] :
      ( r2_hidden('#skF_4'(A_471,B_472,C_473),B_472)
      | r2_hidden('#skF_5'(A_471,B_472,C_473),C_473)
      | k2_zfmisc_1(A_471,B_472) = C_473 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3026,plain,(
    ! [A_371,B_372,C_373] :
      ( r2_hidden('#skF_3'(A_371,B_372,C_373),A_371)
      | r2_hidden('#skF_5'(A_371,B_372,C_373),C_373)
      | k2_zfmisc_1(A_371,B_372) = C_373 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1521,plain,(
    ! [A_213,B_214,C_215] :
      ( r2_hidden('#skF_4'(A_213,B_214,C_215),B_214)
      | r2_hidden('#skF_5'(A_213,B_214,C_215),C_215)
      | k2_zfmisc_1(A_213,B_214) = C_215 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_714,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_4'(A_162,B_163,C_164),B_163)
      | r2_hidden('#skF_5'(A_162,B_163,C_164),C_164)
      | k2_zfmisc_1(A_162,B_163) = C_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ! [A_58,B_59] : r1_xboole_0(k3_xboole_0(A_58,B_59),k5_xboole_0(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_10,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_122,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_74,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [B_55] : k3_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_12])).

tff(c_133,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_136,plain,(
    ! [B_55,C_63] :
      ( ~ r1_xboole_0(k1_xboole_0,B_55)
      | ~ r2_hidden(C_63,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_133])).

tff(c_141,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_136])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_125,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_166,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_hidden(k4_tarski(A_76,B_77),k2_zfmisc_1(C_78,D_79))
      | ~ r2_hidden(B_77,D_79)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_175,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski(A_76,B_77),k1_xboole_0)
      | ~ r2_hidden(B_77,'#skF_11')
      | ~ r2_hidden(A_76,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_166])).

tff(c_178,plain,(
    ! [B_77,A_76] :
      ( ~ r2_hidden(B_77,'#skF_11')
      | ~ r2_hidden(A_76,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_175])).

tff(c_179,plain,(
    ! [A_76] : ~ r2_hidden(A_76,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_1052,plain,(
    ! [A_177,C_178] :
      ( r2_hidden('#skF_5'(A_177,'#skF_10',C_178),C_178)
      | k2_zfmisc_1(A_177,'#skF_10') = C_178 ) ),
    inference(resolution,[status(thm)],[c_714,c_179])).

tff(c_1190,plain,(
    ! [A_177] : k2_zfmisc_1(A_177,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1052,c_179])).

tff(c_1191,plain,(
    ! [A_177] : k2_zfmisc_1(A_177,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1052,c_141])).

tff(c_1310,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1191])).

tff(c_1311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1310])).

tff(c_1312,plain,(
    ! [B_77] : ~ r2_hidden(B_77,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_1726,plain,(
    ! [A_226,C_227] :
      ( r2_hidden('#skF_5'(A_226,'#skF_11',C_227),C_227)
      | k2_zfmisc_1(A_226,'#skF_11') = C_227 ) ),
    inference(resolution,[status(thm)],[c_1521,c_1312])).

tff(c_1804,plain,(
    ! [A_226] : k2_zfmisc_1(A_226,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_1726,c_1312])).

tff(c_1812,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_125])).

tff(c_1814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1812])).

tff(c_1815,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1818,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1815])).

tff(c_1816,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2817,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_1816])).

tff(c_2185,plain,(
    ! [A_286,B_287,C_288] :
      ( r2_hidden('#skF_4'(A_286,B_287,C_288),B_287)
      | r2_hidden('#skF_5'(A_286,B_287,C_288),C_288)
      | k2_zfmisc_1(A_286,B_287) = C_288 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1819,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_122])).

tff(c_1821,plain,(
    ! [B_55] : k3_xboole_0('#skF_9',B_55) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_1818,c_82])).

tff(c_1900,plain,(
    ! [A_234,B_235,C_236] :
      ( ~ r1_xboole_0(A_234,B_235)
      | ~ r2_hidden(C_236,k3_xboole_0(A_234,B_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1903,plain,(
    ! [B_55,C_236] :
      ( ~ r1_xboole_0('#skF_9',B_55)
      | ~ r2_hidden(C_236,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_1900])).

tff(c_1908,plain,(
    ! [C_236] : ~ r2_hidden(C_236,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_1903])).

tff(c_2700,plain,(
    ! [A_327,C_328] :
      ( r2_hidden('#skF_5'(A_327,'#skF_9',C_328),C_328)
      | k2_zfmisc_1(A_327,'#skF_9') = C_328 ) ),
    inference(resolution,[status(thm)],[c_2185,c_1908])).

tff(c_2789,plain,(
    ! [A_327] : k2_zfmisc_1(A_327,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2700,c_1908])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1848,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_1818,c_54])).

tff(c_1849,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1848])).

tff(c_2801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_1849])).

tff(c_2802,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1848])).

tff(c_2818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2817,c_2802])).

tff(c_2819,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1815])).

tff(c_2821,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_122])).

tff(c_2823,plain,(
    ! [B_55] : k3_xboole_0('#skF_8',B_55) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_2819,c_82])).

tff(c_2904,plain,(
    ! [A_336,B_337,C_338] :
      ( ~ r1_xboole_0(A_336,B_337)
      | ~ r2_hidden(C_338,k3_xboole_0(A_336,B_337)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2907,plain,(
    ! [B_55,C_338] :
      ( ~ r1_xboole_0('#skF_8',B_55)
      | ~ r2_hidden(C_338,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2823,c_2904])).

tff(c_2912,plain,(
    ! [C_338] : ~ r2_hidden(C_338,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2821,c_2907])).

tff(c_3685,plain,(
    ! [A_426,B_427] :
      ( r2_hidden('#skF_3'(A_426,B_427,'#skF_8'),A_426)
      | k2_zfmisc_1(A_426,B_427) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3026,c_2912])).

tff(c_3774,plain,(
    ! [B_427] : k2_zfmisc_1('#skF_8',B_427) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3685,c_2912])).

tff(c_2834,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_1816])).

tff(c_2849,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_2819,c_54])).

tff(c_2850,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_2834,c_2849])).

tff(c_3803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3774,c_2850])).

tff(c_3805,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3817,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3805,c_3805,c_3805,c_48])).

tff(c_3818,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3817])).

tff(c_3811,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_11') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3805,c_14])).

tff(c_3831,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_8') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3818,c_3811])).

tff(c_3810,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3805,c_3805,c_10])).

tff(c_3841,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3818,c_3818,c_3810])).

tff(c_3889,plain,(
    ! [A_436,B_437] : r1_xboole_0(k3_xboole_0(A_436,B_437),k5_xboole_0(A_436,B_437)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3895,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',k5_xboole_0(A_10,'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3841,c_3889])).

tff(c_3899,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3831,c_3895])).

tff(c_3806,plain,(
    ! [B_55] : k3_xboole_0('#skF_11',B_55) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3805,c_3805,c_82])).

tff(c_3854,plain,(
    ! [B_55] : k3_xboole_0('#skF_8',B_55) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3818,c_3818,c_3806])).

tff(c_3906,plain,(
    ! [A_439,B_440,C_441] :
      ( ~ r1_xboole_0(A_439,B_440)
      | ~ r2_hidden(C_441,k3_xboole_0(A_439,B_440)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3909,plain,(
    ! [B_55,C_441] :
      ( ~ r1_xboole_0('#skF_8',B_55)
      | ~ r2_hidden(C_441,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3854,c_3906])).

tff(c_3914,plain,(
    ! [C_441] : ~ r2_hidden(C_441,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3899,c_3909])).

tff(c_4705,plain,(
    ! [A_532,C_533] :
      ( r2_hidden('#skF_5'(A_532,'#skF_8',C_533),C_533)
      | k2_zfmisc_1(A_532,'#skF_8') = C_533 ) ),
    inference(resolution,[status(thm)],[c_4012,c_3914])).

tff(c_4794,plain,(
    ! [A_532] : k2_zfmisc_1(A_532,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4705,c_3914])).

tff(c_3942,plain,(
    ! [A_458,B_459,D_460] :
      ( r2_hidden('#skF_6'(A_458,B_459,k2_zfmisc_1(A_458,B_459),D_460),A_458)
      | ~ r2_hidden(D_460,k2_zfmisc_1(A_458,B_459)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3951,plain,(
    ! [D_460,B_459] : ~ r2_hidden(D_460,k2_zfmisc_1('#skF_8',B_459)) ),
    inference(resolution,[status(thm)],[c_3942,c_3914])).

tff(c_4793,plain,(
    ! [A_532,B_459] : k2_zfmisc_1(A_532,'#skF_8') = k2_zfmisc_1('#skF_8',B_459) ),
    inference(resolution,[status(thm)],[c_4705,c_3951])).

tff(c_4884,plain,(
    ! [B_459] : k2_zfmisc_1('#skF_8',B_459) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_4793])).

tff(c_3820,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3818,c_3805])).

tff(c_3804,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3853,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3820,c_3804])).

tff(c_4898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4884,c_3853])).

tff(c_4899,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3817])).

tff(c_4912,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_4899,c_3810])).

tff(c_4926,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_9') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_3811])).

tff(c_4972,plain,(
    ! [A_545,B_546] : r1_xboole_0(k3_xboole_0(A_545,B_546),k5_xboole_0(A_545,B_546)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4978,plain,(
    ! [A_12] : r1_xboole_0(k3_xboole_0(A_12,'#skF_9'),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_4926,c_4972])).

tff(c_4982,plain,(
    ! [A_12] : r1_xboole_0('#skF_9',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4912,c_4978])).

tff(c_4938,plain,(
    ! [B_55] : k3_xboole_0('#skF_9',B_55) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_4899,c_3806])).

tff(c_4990,plain,(
    ! [A_548,B_549,C_550] :
      ( ~ r1_xboole_0(A_548,B_549)
      | ~ r2_hidden(C_550,k3_xboole_0(A_548,B_549)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4993,plain,(
    ! [B_55,C_550] :
      ( ~ r1_xboole_0('#skF_9',B_55)
      | ~ r2_hidden(C_550,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4938,c_4990])).

tff(c_4998,plain,(
    ! [C_550] : ~ r2_hidden(C_550,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4982,c_4993])).

tff(c_5771,plain,(
    ! [A_638,C_639] :
      ( r2_hidden('#skF_5'(A_638,'#skF_9',C_639),C_639)
      | k2_zfmisc_1(A_638,'#skF_9') = C_639 ) ),
    inference(resolution,[status(thm)],[c_5300,c_4998])).

tff(c_5860,plain,(
    ! [A_638] : k2_zfmisc_1(A_638,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5771,c_4998])).

tff(c_4902,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4899,c_3805])).

tff(c_4937,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4902,c_3804])).

tff(c_5890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5860,c_4937])).

tff(c_5892,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5891,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5902,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5892,c_5892,c_5891])).

tff(c_5903,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_5902])).

tff(c_5895,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5892,c_5892,c_10])).

tff(c_5915,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5903,c_5903,c_5895])).

tff(c_5896,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_10') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5892,c_14])).

tff(c_5927,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_9') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5903,c_5896])).

tff(c_5975,plain,(
    ! [A_649,B_650] : r1_xboole_0(k3_xboole_0(A_649,B_650),k5_xboole_0(A_649,B_650)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5981,plain,(
    ! [A_12] : r1_xboole_0(k3_xboole_0(A_12,'#skF_9'),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_5927,c_5975])).

tff(c_5985,plain,(
    ! [A_12] : r1_xboole_0('#skF_9',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5915,c_5981])).

tff(c_5905,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5903,c_5892])).

tff(c_5939,plain,(
    ! [B_55] : k3_xboole_0('#skF_9',B_55) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5905,c_5905,c_82])).

tff(c_5992,plain,(
    ! [A_652,B_653,C_654] :
      ( ~ r1_xboole_0(A_652,B_653)
      | ~ r2_hidden(C_654,k3_xboole_0(A_652,B_653)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5995,plain,(
    ! [B_55,C_654] :
      ( ~ r1_xboole_0('#skF_9',B_55)
      | ~ r2_hidden(C_654,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5939,c_5992])).

tff(c_6000,plain,(
    ! [C_654] : ~ r2_hidden(C_654,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5985,c_5995])).

tff(c_6791,plain,(
    ! [A_745,C_746] :
      ( r2_hidden('#skF_5'(A_745,'#skF_9',C_746),C_746)
      | k2_zfmisc_1(A_745,'#skF_9') = C_746 ) ),
    inference(resolution,[status(thm)],[c_6130,c_6000])).

tff(c_6880,plain,(
    ! [A_745] : k2_zfmisc_1(A_745,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6791,c_6000])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5938,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5905,c_5903,c_5905,c_50])).

tff(c_6892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_5938])).

tff(c_6893,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5902])).

tff(c_6906,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6893,c_6893,c_5895])).

tff(c_6919,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_8') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6893,c_5896])).

tff(c_6968,plain,(
    ! [A_752,B_753] : r1_xboole_0(k3_xboole_0(A_752,B_753),k5_xboole_0(A_752,B_753)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6974,plain,(
    ! [A_12] : r1_xboole_0(k3_xboole_0(A_12,'#skF_8'),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6919,c_6968])).

tff(c_6978,plain,(
    ! [A_12] : r1_xboole_0('#skF_8',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6906,c_6974])).

tff(c_6896,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6893,c_5892])).

tff(c_6931,plain,(
    ! [B_55] : k3_xboole_0('#skF_8',B_55) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6896,c_6896,c_82])).

tff(c_6986,plain,(
    ! [A_755,B_756,C_757] :
      ( ~ r1_xboole_0(A_755,B_756)
      | ~ r2_hidden(C_757,k3_xboole_0(A_755,B_756)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6989,plain,(
    ! [B_55,C_757] :
      ( ~ r1_xboole_0('#skF_8',B_55)
      | ~ r2_hidden(C_757,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6931,c_6986])).

tff(c_6994,plain,(
    ! [C_757] : ~ r2_hidden(C_757,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6978,c_6989])).

tff(c_7785,plain,(
    ! [A_848,C_849] :
      ( r2_hidden('#skF_5'(A_848,'#skF_8',C_849),C_849)
      | k2_zfmisc_1(A_848,'#skF_8') = C_849 ) ),
    inference(resolution,[status(thm)],[c_7124,c_6994])).

tff(c_7874,plain,(
    ! [A_848] : k2_zfmisc_1(A_848,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7785,c_6994])).

tff(c_7022,plain,(
    ! [A_774,B_775,D_776] :
      ( r2_hidden('#skF_6'(A_774,B_775,k2_zfmisc_1(A_774,B_775),D_776),A_774)
      | ~ r2_hidden(D_776,k2_zfmisc_1(A_774,B_775)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7031,plain,(
    ! [D_776,B_775] : ~ r2_hidden(D_776,k2_zfmisc_1('#skF_8',B_775)) ),
    inference(resolution,[status(thm)],[c_7022,c_6994])).

tff(c_7873,plain,(
    ! [A_848,B_775] : k2_zfmisc_1(A_848,'#skF_8') = k2_zfmisc_1('#skF_8',B_775) ),
    inference(resolution,[status(thm)],[c_7785,c_7031])).

tff(c_7963,plain,(
    ! [B_775] : k2_zfmisc_1('#skF_8',B_775) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7874,c_7873])).

tff(c_6930,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6896,c_6893,c_6896,c_50])).

tff(c_7977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7963,c_6930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/3.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/3.03  
% 7.46/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/3.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 7.46/3.04  
% 7.46/3.04  %Foreground sorts:
% 7.46/3.04  
% 7.46/3.04  
% 7.46/3.04  %Background operators:
% 7.46/3.04  
% 7.46/3.04  
% 7.46/3.04  %Foreground operators:
% 7.46/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.46/3.04  tff('#skF_11', type, '#skF_11': $i).
% 7.46/3.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.46/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.46/3.04  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.46/3.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.46/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.46/3.04  tff('#skF_10', type, '#skF_10': $i).
% 7.46/3.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.46/3.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.46/3.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.46/3.04  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.46/3.04  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.46/3.04  tff('#skF_9', type, '#skF_9': $i).
% 7.46/3.04  tff('#skF_8', type, '#skF_8': $i).
% 7.46/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/3.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.46/3.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.46/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/3.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.46/3.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.46/3.04  
% 7.83/3.08  tff(f_63, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 7.83/3.08  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.83/3.08  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.83/3.08  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.83/3.08  tff(f_41, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 7.83/3.08  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.83/3.08  tff(f_49, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.83/3.08  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.83/3.08  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.83/3.08  tff(c_7124, plain, (![A_793, B_794, C_795]: (r2_hidden('#skF_4'(A_793, B_794, C_795), B_794) | r2_hidden('#skF_5'(A_793, B_794, C_795), C_795) | k2_zfmisc_1(A_793, B_794)=C_795)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_6130, plain, (![A_690, B_691, C_692]: (r2_hidden('#skF_4'(A_690, B_691, C_692), B_691) | r2_hidden('#skF_5'(A_690, B_691, C_692), C_692) | k2_zfmisc_1(A_690, B_691)=C_692)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_5300, plain, (![A_604, B_605, C_606]: (r2_hidden('#skF_4'(A_604, B_605, C_606), B_605) | r2_hidden('#skF_5'(A_604, B_605, C_606), C_606) | k2_zfmisc_1(A_604, B_605)=C_606)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_4012, plain, (![A_471, B_472, C_473]: (r2_hidden('#skF_4'(A_471, B_472, C_473), B_472) | r2_hidden('#skF_5'(A_471, B_472, C_473), C_473) | k2_zfmisc_1(A_471, B_472)=C_473)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_3026, plain, (![A_371, B_372, C_373]: (r2_hidden('#skF_3'(A_371, B_372, C_373), A_371) | r2_hidden('#skF_5'(A_371, B_372, C_373), C_373) | k2_zfmisc_1(A_371, B_372)=C_373)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_46, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/3.08  tff(c_110, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_46])).
% 7.83/3.08  tff(c_1521, plain, (![A_213, B_214, C_215]: (r2_hidden('#skF_4'(A_213, B_214, C_215), B_214) | r2_hidden('#skF_5'(A_213, B_214, C_215), C_215) | k2_zfmisc_1(A_213, B_214)=C_215)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_52, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/3.08  tff(c_90, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_52])).
% 7.83/3.08  tff(c_714, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_4'(A_162, B_163, C_164), B_163) | r2_hidden('#skF_5'(A_162, B_163, C_164), C_164) | k2_zfmisc_1(A_162, B_163)=C_164)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.83/3.08  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.83/3.08  tff(c_112, plain, (![A_58, B_59]: (r1_xboole_0(k3_xboole_0(A_58, B_59), k5_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.83/3.08  tff(c_118, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_10, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_112])).
% 7.83/3.08  tff(c_122, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_118])).
% 7.83/3.08  tff(c_74, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), A_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.83/3.08  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.83/3.08  tff(c_82, plain, (![B_55]: (k3_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_12])).
% 7.83/3.08  tff(c_133, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_136, plain, (![B_55, C_63]: (~r1_xboole_0(k1_xboole_0, B_55) | ~r2_hidden(C_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_133])).
% 7.83/3.08  tff(c_141, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_136])).
% 7.83/3.08  tff(c_56, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/3.08  tff(c_125, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 7.83/3.08  tff(c_166, plain, (![A_76, B_77, C_78, D_79]: (r2_hidden(k4_tarski(A_76, B_77), k2_zfmisc_1(C_78, D_79)) | ~r2_hidden(B_77, D_79) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.83/3.08  tff(c_175, plain, (![A_76, B_77]: (r2_hidden(k4_tarski(A_76, B_77), k1_xboole_0) | ~r2_hidden(B_77, '#skF_11') | ~r2_hidden(A_76, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_166])).
% 7.83/3.08  tff(c_178, plain, (![B_77, A_76]: (~r2_hidden(B_77, '#skF_11') | ~r2_hidden(A_76, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_141, c_175])).
% 7.83/3.08  tff(c_179, plain, (![A_76]: (~r2_hidden(A_76, '#skF_10'))), inference(splitLeft, [status(thm)], [c_178])).
% 7.83/3.08  tff(c_1052, plain, (![A_177, C_178]: (r2_hidden('#skF_5'(A_177, '#skF_10', C_178), C_178) | k2_zfmisc_1(A_177, '#skF_10')=C_178)), inference(resolution, [status(thm)], [c_714, c_179])).
% 7.83/3.08  tff(c_1190, plain, (![A_177]: (k2_zfmisc_1(A_177, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1052, c_179])).
% 7.83/3.08  tff(c_1191, plain, (![A_177]: (k2_zfmisc_1(A_177, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1052, c_141])).
% 7.83/3.08  tff(c_1310, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1191])).
% 7.83/3.08  tff(c_1311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1310])).
% 7.83/3.08  tff(c_1312, plain, (![B_77]: (~r2_hidden(B_77, '#skF_11'))), inference(splitRight, [status(thm)], [c_178])).
% 7.83/3.08  tff(c_1726, plain, (![A_226, C_227]: (r2_hidden('#skF_5'(A_226, '#skF_11', C_227), C_227) | k2_zfmisc_1(A_226, '#skF_11')=C_227)), inference(resolution, [status(thm)], [c_1521, c_1312])).
% 7.83/3.08  tff(c_1804, plain, (![A_226]: (k2_zfmisc_1(A_226, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_1726, c_1312])).
% 7.83/3.08  tff(c_1812, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_125])).
% 7.83/3.08  tff(c_1814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_1812])).
% 7.83/3.08  tff(c_1815, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_56])).
% 7.83/3.08  tff(c_1818, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1815])).
% 7.83/3.08  tff(c_1816, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 7.83/3.08  tff(c_2817, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1818, c_1816])).
% 7.83/3.08  tff(c_2185, plain, (![A_286, B_287, C_288]: (r2_hidden('#skF_4'(A_286, B_287, C_288), B_287) | r2_hidden('#skF_5'(A_286, B_287, C_288), C_288) | k2_zfmisc_1(A_286, B_287)=C_288)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_1819, plain, (![A_10]: (r1_xboole_0('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1818, c_122])).
% 7.83/3.08  tff(c_1821, plain, (![B_55]: (k3_xboole_0('#skF_9', B_55)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1818, c_1818, c_82])).
% 7.83/3.08  tff(c_1900, plain, (![A_234, B_235, C_236]: (~r1_xboole_0(A_234, B_235) | ~r2_hidden(C_236, k3_xboole_0(A_234, B_235)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_1903, plain, (![B_55, C_236]: (~r1_xboole_0('#skF_9', B_55) | ~r2_hidden(C_236, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1821, c_1900])).
% 7.83/3.08  tff(c_1908, plain, (![C_236]: (~r2_hidden(C_236, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_1903])).
% 7.83/3.08  tff(c_2700, plain, (![A_327, C_328]: (r2_hidden('#skF_5'(A_327, '#skF_9', C_328), C_328) | k2_zfmisc_1(A_327, '#skF_9')=C_328)), inference(resolution, [status(thm)], [c_2185, c_1908])).
% 7.83/3.08  tff(c_2789, plain, (![A_327]: (k2_zfmisc_1(A_327, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_2700, c_1908])).
% 7.83/3.08  tff(c_54, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/3.08  tff(c_1848, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1818, c_1818, c_54])).
% 7.83/3.08  tff(c_1849, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(splitLeft, [status(thm)], [c_1848])).
% 7.83/3.08  tff(c_2801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2789, c_1849])).
% 7.83/3.08  tff(c_2802, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(splitRight, [status(thm)], [c_1848])).
% 7.83/3.08  tff(c_2818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2817, c_2802])).
% 7.83/3.08  tff(c_2819, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1815])).
% 7.83/3.08  tff(c_2821, plain, (![A_10]: (r1_xboole_0('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_122])).
% 7.83/3.08  tff(c_2823, plain, (![B_55]: (k3_xboole_0('#skF_8', B_55)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_2819, c_82])).
% 7.83/3.08  tff(c_2904, plain, (![A_336, B_337, C_338]: (~r1_xboole_0(A_336, B_337) | ~r2_hidden(C_338, k3_xboole_0(A_336, B_337)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_2907, plain, (![B_55, C_338]: (~r1_xboole_0('#skF_8', B_55) | ~r2_hidden(C_338, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2823, c_2904])).
% 7.83/3.08  tff(c_2912, plain, (![C_338]: (~r2_hidden(C_338, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2821, c_2907])).
% 7.83/3.08  tff(c_3685, plain, (![A_426, B_427]: (r2_hidden('#skF_3'(A_426, B_427, '#skF_8'), A_426) | k2_zfmisc_1(A_426, B_427)='#skF_8')), inference(resolution, [status(thm)], [c_3026, c_2912])).
% 7.83/3.08  tff(c_3774, plain, (![B_427]: (k2_zfmisc_1('#skF_8', B_427)='#skF_8')), inference(resolution, [status(thm)], [c_3685, c_2912])).
% 7.83/3.08  tff(c_2834, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_1816])).
% 7.83/3.08  tff(c_2849, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_2819, c_54])).
% 7.83/3.08  tff(c_2850, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_2834, c_2849])).
% 7.83/3.08  tff(c_3803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3774, c_2850])).
% 7.83/3.08  tff(c_3805, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_46])).
% 7.83/3.08  tff(c_48, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/3.08  tff(c_3817, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3805, c_3805, c_3805, c_48])).
% 7.83/3.08  tff(c_3818, plain, ('#skF_11'='#skF_8'), inference(splitLeft, [status(thm)], [c_3817])).
% 7.83/3.08  tff(c_3811, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_11')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_3805, c_14])).
% 7.83/3.08  tff(c_3831, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_8')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_3818, c_3811])).
% 7.83/3.08  tff(c_3810, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_3805, c_3805, c_10])).
% 7.83/3.08  tff(c_3841, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3818, c_3818, c_3810])).
% 7.83/3.08  tff(c_3889, plain, (![A_436, B_437]: (r1_xboole_0(k3_xboole_0(A_436, B_437), k5_xboole_0(A_436, B_437)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.83/3.08  tff(c_3895, plain, (![A_10]: (r1_xboole_0('#skF_8', k5_xboole_0(A_10, '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_3841, c_3889])).
% 7.83/3.08  tff(c_3899, plain, (![A_10]: (r1_xboole_0('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3831, c_3895])).
% 7.83/3.08  tff(c_3806, plain, (![B_55]: (k3_xboole_0('#skF_11', B_55)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_3805, c_3805, c_82])).
% 7.83/3.08  tff(c_3854, plain, (![B_55]: (k3_xboole_0('#skF_8', B_55)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3818, c_3818, c_3806])).
% 7.83/3.08  tff(c_3906, plain, (![A_439, B_440, C_441]: (~r1_xboole_0(A_439, B_440) | ~r2_hidden(C_441, k3_xboole_0(A_439, B_440)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_3909, plain, (![B_55, C_441]: (~r1_xboole_0('#skF_8', B_55) | ~r2_hidden(C_441, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3854, c_3906])).
% 7.83/3.08  tff(c_3914, plain, (![C_441]: (~r2_hidden(C_441, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3899, c_3909])).
% 7.83/3.08  tff(c_4705, plain, (![A_532, C_533]: (r2_hidden('#skF_5'(A_532, '#skF_8', C_533), C_533) | k2_zfmisc_1(A_532, '#skF_8')=C_533)), inference(resolution, [status(thm)], [c_4012, c_3914])).
% 7.83/3.08  tff(c_4794, plain, (![A_532]: (k2_zfmisc_1(A_532, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_4705, c_3914])).
% 7.83/3.08  tff(c_3942, plain, (![A_458, B_459, D_460]: (r2_hidden('#skF_6'(A_458, B_459, k2_zfmisc_1(A_458, B_459), D_460), A_458) | ~r2_hidden(D_460, k2_zfmisc_1(A_458, B_459)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_3951, plain, (![D_460, B_459]: (~r2_hidden(D_460, k2_zfmisc_1('#skF_8', B_459)))), inference(resolution, [status(thm)], [c_3942, c_3914])).
% 7.83/3.08  tff(c_4793, plain, (![A_532, B_459]: (k2_zfmisc_1(A_532, '#skF_8')=k2_zfmisc_1('#skF_8', B_459))), inference(resolution, [status(thm)], [c_4705, c_3951])).
% 7.83/3.08  tff(c_4884, plain, (![B_459]: (k2_zfmisc_1('#skF_8', B_459)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4794, c_4793])).
% 7.83/3.08  tff(c_3820, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3818, c_3805])).
% 7.83/3.08  tff(c_3804, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 7.83/3.08  tff(c_3853, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3820, c_3804])).
% 7.83/3.08  tff(c_4898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4884, c_3853])).
% 7.83/3.08  tff(c_4899, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_3817])).
% 7.83/3.08  tff(c_4912, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_4899, c_3810])).
% 7.83/3.08  tff(c_4926, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_9')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_3811])).
% 7.83/3.08  tff(c_4972, plain, (![A_545, B_546]: (r1_xboole_0(k3_xboole_0(A_545, B_546), k5_xboole_0(A_545, B_546)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.83/3.08  tff(c_4978, plain, (![A_12]: (r1_xboole_0(k3_xboole_0(A_12, '#skF_9'), A_12))), inference(superposition, [status(thm), theory('equality')], [c_4926, c_4972])).
% 7.83/3.08  tff(c_4982, plain, (![A_12]: (r1_xboole_0('#skF_9', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_4912, c_4978])).
% 7.83/3.08  tff(c_4938, plain, (![B_55]: (k3_xboole_0('#skF_9', B_55)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_4899, c_3806])).
% 7.83/3.08  tff(c_4990, plain, (![A_548, B_549, C_550]: (~r1_xboole_0(A_548, B_549) | ~r2_hidden(C_550, k3_xboole_0(A_548, B_549)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_4993, plain, (![B_55, C_550]: (~r1_xboole_0('#skF_9', B_55) | ~r2_hidden(C_550, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4938, c_4990])).
% 7.83/3.08  tff(c_4998, plain, (![C_550]: (~r2_hidden(C_550, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_4982, c_4993])).
% 7.83/3.08  tff(c_5771, plain, (![A_638, C_639]: (r2_hidden('#skF_5'(A_638, '#skF_9', C_639), C_639) | k2_zfmisc_1(A_638, '#skF_9')=C_639)), inference(resolution, [status(thm)], [c_5300, c_4998])).
% 7.83/3.08  tff(c_5860, plain, (![A_638]: (k2_zfmisc_1(A_638, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_5771, c_4998])).
% 7.83/3.08  tff(c_4902, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4899, c_3805])).
% 7.83/3.08  tff(c_4937, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4902, c_3804])).
% 7.83/3.08  tff(c_5890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5860, c_4937])).
% 7.83/3.08  tff(c_5892, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 7.83/3.08  tff(c_5891, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 7.83/3.08  tff(c_5902, plain, ('#skF_10'='#skF_8' | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5892, c_5892, c_5891])).
% 7.83/3.08  tff(c_5903, plain, ('#skF_10'='#skF_9'), inference(splitLeft, [status(thm)], [c_5902])).
% 7.83/3.08  tff(c_5895, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_5892, c_5892, c_10])).
% 7.83/3.08  tff(c_5915, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5903, c_5903, c_5895])).
% 7.83/3.08  tff(c_5896, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_10')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_5892, c_14])).
% 7.83/3.08  tff(c_5927, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_9')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_5903, c_5896])).
% 7.83/3.08  tff(c_5975, plain, (![A_649, B_650]: (r1_xboole_0(k3_xboole_0(A_649, B_650), k5_xboole_0(A_649, B_650)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.83/3.08  tff(c_5981, plain, (![A_12]: (r1_xboole_0(k3_xboole_0(A_12, '#skF_9'), A_12))), inference(superposition, [status(thm), theory('equality')], [c_5927, c_5975])).
% 7.83/3.08  tff(c_5985, plain, (![A_12]: (r1_xboole_0('#skF_9', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_5915, c_5981])).
% 7.83/3.08  tff(c_5905, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5903, c_5892])).
% 7.83/3.08  tff(c_5939, plain, (![B_55]: (k3_xboole_0('#skF_9', B_55)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5905, c_5905, c_82])).
% 7.83/3.08  tff(c_5992, plain, (![A_652, B_653, C_654]: (~r1_xboole_0(A_652, B_653) | ~r2_hidden(C_654, k3_xboole_0(A_652, B_653)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_5995, plain, (![B_55, C_654]: (~r1_xboole_0('#skF_9', B_55) | ~r2_hidden(C_654, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5939, c_5992])).
% 7.83/3.08  tff(c_6000, plain, (![C_654]: (~r2_hidden(C_654, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5985, c_5995])).
% 7.83/3.08  tff(c_6791, plain, (![A_745, C_746]: (r2_hidden('#skF_5'(A_745, '#skF_9', C_746), C_746) | k2_zfmisc_1(A_745, '#skF_9')=C_746)), inference(resolution, [status(thm)], [c_6130, c_6000])).
% 7.83/3.08  tff(c_6880, plain, (![A_745]: (k2_zfmisc_1(A_745, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_6791, c_6000])).
% 7.83/3.08  tff(c_50, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.83/3.08  tff(c_5938, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_5905, c_5903, c_5905, c_50])).
% 7.83/3.08  tff(c_6892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6880, c_5938])).
% 7.83/3.08  tff(c_6893, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_5902])).
% 7.83/3.08  tff(c_6906, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6893, c_6893, c_5895])).
% 7.83/3.08  tff(c_6919, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_8')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_6893, c_5896])).
% 7.83/3.08  tff(c_6968, plain, (![A_752, B_753]: (r1_xboole_0(k3_xboole_0(A_752, B_753), k5_xboole_0(A_752, B_753)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.83/3.08  tff(c_6974, plain, (![A_12]: (r1_xboole_0(k3_xboole_0(A_12, '#skF_8'), A_12))), inference(superposition, [status(thm), theory('equality')], [c_6919, c_6968])).
% 7.83/3.08  tff(c_6978, plain, (![A_12]: (r1_xboole_0('#skF_8', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_6906, c_6974])).
% 7.83/3.08  tff(c_6896, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6893, c_5892])).
% 7.83/3.08  tff(c_6931, plain, (![B_55]: (k3_xboole_0('#skF_8', B_55)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6896, c_6896, c_82])).
% 7.83/3.08  tff(c_6986, plain, (![A_755, B_756, C_757]: (~r1_xboole_0(A_755, B_756) | ~r2_hidden(C_757, k3_xboole_0(A_755, B_756)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.83/3.08  tff(c_6989, plain, (![B_55, C_757]: (~r1_xboole_0('#skF_8', B_55) | ~r2_hidden(C_757, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6931, c_6986])).
% 7.83/3.08  tff(c_6994, plain, (![C_757]: (~r2_hidden(C_757, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_6978, c_6989])).
% 7.83/3.08  tff(c_7785, plain, (![A_848, C_849]: (r2_hidden('#skF_5'(A_848, '#skF_8', C_849), C_849) | k2_zfmisc_1(A_848, '#skF_8')=C_849)), inference(resolution, [status(thm)], [c_7124, c_6994])).
% 7.83/3.08  tff(c_7874, plain, (![A_848]: (k2_zfmisc_1(A_848, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_7785, c_6994])).
% 7.83/3.08  tff(c_7022, plain, (![A_774, B_775, D_776]: (r2_hidden('#skF_6'(A_774, B_775, k2_zfmisc_1(A_774, B_775), D_776), A_774) | ~r2_hidden(D_776, k2_zfmisc_1(A_774, B_775)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/3.08  tff(c_7031, plain, (![D_776, B_775]: (~r2_hidden(D_776, k2_zfmisc_1('#skF_8', B_775)))), inference(resolution, [status(thm)], [c_7022, c_6994])).
% 7.83/3.08  tff(c_7873, plain, (![A_848, B_775]: (k2_zfmisc_1(A_848, '#skF_8')=k2_zfmisc_1('#skF_8', B_775))), inference(resolution, [status(thm)], [c_7785, c_7031])).
% 7.83/3.08  tff(c_7963, plain, (![B_775]: (k2_zfmisc_1('#skF_8', B_775)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7874, c_7873])).
% 7.83/3.08  tff(c_6930, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6896, c_6893, c_6896, c_50])).
% 7.83/3.08  tff(c_7977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7963, c_6930])).
% 7.83/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.83/3.08  
% 7.83/3.08  Inference rules
% 7.83/3.08  ----------------------
% 7.83/3.08  #Ref     : 0
% 7.83/3.08  #Sup     : 1561
% 7.83/3.08  #Fact    : 0
% 7.83/3.08  #Define  : 0
% 7.83/3.08  #Split   : 9
% 7.83/3.08  #Chain   : 0
% 7.83/3.08  #Close   : 0
% 7.83/3.08  
% 7.83/3.08  Ordering : KBO
% 7.83/3.08  
% 7.83/3.08  Simplification rules
% 7.83/3.08  ----------------------
% 7.83/3.08  #Subsume      : 466
% 7.83/3.08  #Demod        : 409
% 7.83/3.08  #Tautology    : 185
% 7.83/3.08  #SimpNegUnit  : 33
% 7.83/3.08  #BackRed      : 115
% 7.83/3.08  
% 7.83/3.08  #Partial instantiations: 0
% 7.83/3.08  #Strategies tried      : 1
% 7.83/3.08  
% 7.83/3.08  Timing (in seconds)
% 7.83/3.08  ----------------------
% 7.90/3.08  Preprocessing        : 0.48
% 7.90/3.08  Parsing              : 0.23
% 7.90/3.08  CNF conversion       : 0.04
% 7.90/3.08  Main loop            : 1.65
% 7.90/3.08  Inferencing          : 0.70
% 7.90/3.08  Reduction            : 0.44
% 7.90/3.08  Demodulation         : 0.25
% 7.90/3.08  BG Simplification    : 0.07
% 7.90/3.08  Subsumption          : 0.29
% 7.90/3.08  Abstraction          : 0.11
% 7.90/3.08  MUC search           : 0.00
% 7.90/3.08  Cooper               : 0.00
% 7.90/3.08  Total                : 2.22
% 7.90/3.08  Index Insertion      : 0.00
% 7.90/3.09  Index Deletion       : 0.00
% 7.90/3.09  Index Matching       : 0.00
% 7.90/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
