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
% DateTime   : Thu Dec  3 09:53:21 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 609 expanded)
%              Number of leaves         :   17 ( 173 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 (1618 expanded)
%              Number of equality atoms :  195 (1492 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_30,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_170,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_171,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_36,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_173,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_178,plain,(
    ! [B_32,C_33,A_34] :
      ( k2_tarski(B_32,C_33) = A_34
      | k1_tarski(C_33) = A_34
      | k1_tarski(B_32) = A_34
      | k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k2_tarski(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_235,plain,(
    ! [B_39,C_40,A_41] :
      ( k2_tarski(B_39,C_40) = A_41
      | k1_tarski(C_40) = A_41
      | k1_tarski(B_39) = A_41
      | k1_xboole_0 = A_41
      | k4_xboole_0(A_41,k2_tarski(B_39,C_40)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_178])).

tff(c_238,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_235])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_170,c_135,c_171,c_238])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_260,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_261,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_172])).

tff(c_10,plain,(
    ! [B_5,C_6] : r1_tarski(k2_tarski(B_5,C_6),k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_279,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_10])).

tff(c_295,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_279])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_301,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_295,c_4])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_301])).

tff(c_316,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_318,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_16,plain,(
    ! [B_5,C_6] : r1_tarski(k1_xboole_0,k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [B_5,C_6] : k4_xboole_0(k1_xboole_0,k2_tarski(B_5,C_6)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_325,plain,(
    ! [B_5,C_6] : k4_xboole_0('#skF_1',k2_tarski(B_5,C_6)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_318,c_98])).

tff(c_320,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_172])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_320])).

tff(c_351,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_353,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_12,plain,(
    ! [C_6,B_5] : r1_tarski(k1_tarski(C_6),k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,(
    ! [C_6,B_5] : k4_xboole_0(k1_tarski(C_6),k2_tarski(B_5,C_6)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_360,plain,(
    ! [B_5] : k4_xboole_0('#skF_1',k2_tarski(B_5,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_94])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_172])).

tff(c_487,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_14,plain,(
    ! [B_5,C_6] : r1_tarski(k1_tarski(B_5),k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [B_5,C_6] : k4_xboole_0(k1_tarski(B_5),k2_tarski(B_5,C_6)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_70])).

tff(c_492,plain,(
    ! [C_6] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_96])).

tff(c_642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_172])).

tff(c_643,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_653,plain,(
    ! [B_60,C_61,A_62] :
      ( k2_tarski(B_60,C_61) = A_62
      | k1_tarski(C_61) = A_62
      | k1_tarski(B_60) = A_62
      | k1_xboole_0 = A_62
      | ~ r1_tarski(A_62,k2_tarski(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_711,plain,(
    ! [B_67,C_68,A_69] :
      ( k2_tarski(B_67,C_68) = A_69
      | k1_tarski(C_68) = A_69
      | k1_tarski(B_67) = A_69
      | k1_xboole_0 = A_69
      | k4_xboole_0(A_69,k2_tarski(B_67,C_68)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_653])).

tff(c_717,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_711])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_170,c_135,c_171,c_717])).

tff(c_738,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_739,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_816,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_20])).

tff(c_817,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_828,plain,(
    ! [B_5,C_6] : k4_xboole_0('#skF_1',k2_tarski(B_5,C_6)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_817,c_98])).

tff(c_740,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_822,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_740])).

tff(c_873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_822])).

tff(c_874,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_876,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_877,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_740])).

tff(c_895,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_10])).

tff(c_911,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_895])).

tff(c_917,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_911,c_4])).

tff(c_933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_877,c_917])).

tff(c_934,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_936,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_934])).

tff(c_940,plain,(
    ! [C_6] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_96])).

tff(c_1110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_940,c_740])).

tff(c_1111,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_934])).

tff(c_1205,plain,(
    ! [B_84] : r1_tarski('#skF_1',k2_tarski(B_84,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_12])).

tff(c_1219,plain,(
    ! [B_84] : k4_xboole_0('#skF_1',k2_tarski(B_84,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1205,c_4])).

tff(c_1239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_740])).

tff(c_1241,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_1241])).

tff(c_1319,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1432,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_28])).

tff(c_1433,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1432])).

tff(c_1444,plain,(
    ! [B_5,C_6] : k4_xboole_0('#skF_1',k2_tarski(B_5,C_6)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1433,c_98])).

tff(c_1318,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1438,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1318])).

tff(c_1484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1438])).

tff(c_1485,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1432])).

tff(c_1487,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1485])).

tff(c_1488,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1318])).

tff(c_1506,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_10])).

tff(c_1522,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1506])).

tff(c_1527,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1522,c_4])).

tff(c_1531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1488,c_1527])).

tff(c_1532,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1485])).

tff(c_1534,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1532])).

tff(c_1652,plain,(
    ! [C_98] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1534,c_14])).

tff(c_1666,plain,(
    ! [C_98] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_98)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1652,c_4])).

tff(c_1682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1666,c_1318])).

tff(c_1683,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1532])).

tff(c_1691,plain,(
    ! [B_5] : k4_xboole_0('#skF_1',k2_tarski(B_5,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1683,c_94])).

tff(c_1833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1318])).

tff(c_1835,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_24,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1982,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_24])).

tff(c_1983,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1982])).

tff(c_1994,plain,(
    ! [B_5,C_6] : k4_xboole_0('#skF_1',k2_tarski(B_5,C_6)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1983,c_98])).

tff(c_1834,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1991,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1834])).

tff(c_2034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_1991])).

tff(c_2035,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1982])).

tff(c_2037,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2035])).

tff(c_2038,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_1834])).

tff(c_2056,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_10])).

tff(c_2072,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_2056])).

tff(c_2078,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2072,c_4])).

tff(c_2100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2038,c_2078])).

tff(c_2101,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2035])).

tff(c_2105,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2101])).

tff(c_2109,plain,(
    ! [C_6] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2105,c_96])).

tff(c_2254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2109,c_1834])).

tff(c_2255,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2101])).

tff(c_2375,plain,(
    ! [B_128] : r1_tarski('#skF_1',k2_tarski(B_128,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_12])).

tff(c_2389,plain,(
    ! [B_128] : k4_xboole_0('#skF_1',k2_tarski(B_128,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2375,c_4])).

tff(c_2405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_1834])).

tff(c_2407,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2432,plain,(
    ! [B_5,C_6] : k4_xboole_0('#skF_4',k2_tarski(B_5,C_6)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_2407,c_98])).

tff(c_32,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2537,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_2407,c_32])).

tff(c_2538,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2537])).

tff(c_2406,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2431,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_2406])).

tff(c_2539,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_2431])).

tff(c_2542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_2539])).

tff(c_2543,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2537])).

tff(c_2545,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2543])).

tff(c_2548,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2545,c_2431])).

tff(c_2451,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(A_137,B_138) = '#skF_4'
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_4])).

tff(c_2474,plain,(
    ! [B_5,C_6] : k4_xboole_0(k2_tarski(B_5,C_6),k2_tarski(B_5,C_6)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_2451])).

tff(c_2555,plain,(
    k4_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2545,c_2474])).

tff(c_2581,plain,(
    k4_xboole_0('#skF_1','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2545,c_2555])).

tff(c_2611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2548,c_2581])).

tff(c_2612,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2543])).

tff(c_2614,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2612])).

tff(c_2478,plain,(
    ! [B_5,C_6] : k4_xboole_0(k1_tarski(B_5),k2_tarski(B_5,C_6)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_2451])).

tff(c_2618,plain,(
    ! [C_6] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_6)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2614,c_2478])).

tff(c_2713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2431])).

tff(c_2714,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2612])).

tff(c_2776,plain,(
    ! [B_150] : r1_tarski('#skF_1',k2_tarski(B_150,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2714,c_12])).

tff(c_2408,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = '#skF_4'
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_4])).

tff(c_2784,plain,(
    ! [B_150] : k4_xboole_0('#skF_1',k2_tarski(B_150,'#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2776,c_2408])).

tff(c_2800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_2431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.73  
% 3.77/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.73  %$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.77/1.73  
% 3.77/1.73  %Foreground sorts:
% 3.77/1.73  
% 3.77/1.73  
% 3.77/1.73  %Background operators:
% 3.77/1.73  
% 3.77/1.73  
% 3.77/1.73  %Foreground operators:
% 3.77/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.73  
% 3.77/1.75  tff(f_62, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 3.77/1.75  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.77/1.75  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.77/1.75  tff(c_30, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_99, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_30])).
% 3.77/1.75  tff(c_26, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_170, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 3.77/1.75  tff(c_22, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_135, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_22])).
% 3.77/1.75  tff(c_18, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_171, plain, (k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 3.77/1.75  tff(c_36, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_173, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.77/1.75  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.75  tff(c_178, plain, (![B_32, C_33, A_34]: (k2_tarski(B_32, C_33)=A_34 | k1_tarski(C_33)=A_34 | k1_tarski(B_32)=A_34 | k1_xboole_0=A_34 | ~r1_tarski(A_34, k2_tarski(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.75  tff(c_235, plain, (![B_39, C_40, A_41]: (k2_tarski(B_39, C_40)=A_41 | k1_tarski(C_40)=A_41 | k1_tarski(B_39)=A_41 | k1_xboole_0=A_41 | k4_xboole_0(A_41, k2_tarski(B_39, C_40))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_178])).
% 3.77/1.75  tff(c_238, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_173, c_235])).
% 3.77/1.75  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_170, c_135, c_171, c_238])).
% 3.77/1.75  tff(c_258, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 3.77/1.75  tff(c_260, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_258])).
% 3.77/1.75  tff(c_34, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_172, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.77/1.75  tff(c_261, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_172])).
% 3.77/1.75  tff(c_10, plain, (![B_5, C_6]: (r1_tarski(k2_tarski(B_5, C_6), k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.75  tff(c_279, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_10])).
% 3.77/1.75  tff(c_295, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_279])).
% 3.77/1.75  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.75  tff(c_301, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_295, c_4])).
% 3.77/1.75  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_301])).
% 3.77/1.75  tff(c_316, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_258])).
% 3.77/1.75  tff(c_318, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_316])).
% 3.77/1.75  tff(c_16, plain, (![B_5, C_6]: (r1_tarski(k1_xboole_0, k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.75  tff(c_70, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.75  tff(c_98, plain, (![B_5, C_6]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_5, C_6))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_70])).
% 3.77/1.75  tff(c_325, plain, (![B_5, C_6]: (k4_xboole_0('#skF_1', k2_tarski(B_5, C_6))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_318, c_98])).
% 3.77/1.75  tff(c_320, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_318, c_172])).
% 3.77/1.75  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_325, c_320])).
% 3.77/1.75  tff(c_351, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_316])).
% 3.77/1.75  tff(c_353, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_351])).
% 3.77/1.75  tff(c_12, plain, (![C_6, B_5]: (r1_tarski(k1_tarski(C_6), k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.75  tff(c_94, plain, (![C_6, B_5]: (k4_xboole_0(k1_tarski(C_6), k2_tarski(B_5, C_6))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_70])).
% 3.77/1.75  tff(c_360, plain, (![B_5]: (k4_xboole_0('#skF_1', k2_tarski(B_5, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_353, c_94])).
% 3.77/1.75  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_360, c_172])).
% 3.77/1.75  tff(c_487, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_351])).
% 3.77/1.75  tff(c_14, plain, (![B_5, C_6]: (r1_tarski(k1_tarski(B_5), k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.75  tff(c_96, plain, (![B_5, C_6]: (k4_xboole_0(k1_tarski(B_5), k2_tarski(B_5, C_6))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_70])).
% 3.77/1.75  tff(c_492, plain, (![C_6]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_487, c_96])).
% 3.77/1.75  tff(c_642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_172])).
% 3.77/1.75  tff(c_643, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.77/1.75  tff(c_653, plain, (![B_60, C_61, A_62]: (k2_tarski(B_60, C_61)=A_62 | k1_tarski(C_61)=A_62 | k1_tarski(B_60)=A_62 | k1_xboole_0=A_62 | ~r1_tarski(A_62, k2_tarski(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.77/1.75  tff(c_711, plain, (![B_67, C_68, A_69]: (k2_tarski(B_67, C_68)=A_69 | k1_tarski(C_68)=A_69 | k1_tarski(B_67)=A_69 | k1_xboole_0=A_69 | k4_xboole_0(A_69, k2_tarski(B_67, C_68))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_653])).
% 3.77/1.75  tff(c_717, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_643, c_711])).
% 3.77/1.75  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_170, c_135, c_171, c_717])).
% 3.77/1.75  tff(c_738, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 3.77/1.75  tff(c_739, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 3.77/1.75  tff(c_20, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_816, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_739, c_20])).
% 3.77/1.75  tff(c_817, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_816])).
% 3.77/1.75  tff(c_828, plain, (![B_5, C_6]: (k4_xboole_0('#skF_1', k2_tarski(B_5, C_6))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_817, c_98])).
% 3.77/1.75  tff(c_740, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.77/1.75  tff(c_822, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_740])).
% 3.77/1.75  tff(c_873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_828, c_822])).
% 3.77/1.75  tff(c_874, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_816])).
% 3.77/1.75  tff(c_876, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_874])).
% 3.77/1.75  tff(c_877, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_876, c_740])).
% 3.77/1.75  tff(c_895, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_876, c_10])).
% 3.77/1.75  tff(c_911, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_876, c_895])).
% 3.77/1.75  tff(c_917, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_911, c_4])).
% 3.77/1.75  tff(c_933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_877, c_917])).
% 3.77/1.75  tff(c_934, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_874])).
% 3.77/1.75  tff(c_936, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_934])).
% 3.77/1.75  tff(c_940, plain, (![C_6]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_936, c_96])).
% 3.77/1.75  tff(c_1110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_940, c_740])).
% 3.77/1.75  tff(c_1111, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_934])).
% 3.77/1.75  tff(c_1205, plain, (![B_84]: (r1_tarski('#skF_1', k2_tarski(B_84, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_12])).
% 3.77/1.75  tff(c_1219, plain, (![B_84]: (k4_xboole_0('#skF_1', k2_tarski(B_84, '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1205, c_4])).
% 3.77/1.75  tff(c_1239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1219, c_740])).
% 3.77/1.75  tff(c_1241, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.77/1.75  tff(c_1317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_738, c_1241])).
% 3.77/1.75  tff(c_1319, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 3.77/1.75  tff(c_28, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_1432, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_28])).
% 3.77/1.75  tff(c_1433, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1432])).
% 3.77/1.75  tff(c_1444, plain, (![B_5, C_6]: (k4_xboole_0('#skF_1', k2_tarski(B_5, C_6))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_1433, c_98])).
% 3.77/1.75  tff(c_1318, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 3.77/1.75  tff(c_1438, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_1318])).
% 3.77/1.75  tff(c_1484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1438])).
% 3.77/1.75  tff(c_1485, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1432])).
% 3.77/1.75  tff(c_1487, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1485])).
% 3.77/1.75  tff(c_1488, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1318])).
% 3.77/1.75  tff(c_1506, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1487, c_10])).
% 3.77/1.75  tff(c_1522, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1506])).
% 3.77/1.75  tff(c_1527, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_1522, c_4])).
% 3.77/1.75  tff(c_1531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1488, c_1527])).
% 3.77/1.75  tff(c_1532, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1485])).
% 3.77/1.75  tff(c_1534, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1532])).
% 3.77/1.75  tff(c_1652, plain, (![C_98]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_98)))), inference(superposition, [status(thm), theory('equality')], [c_1534, c_14])).
% 3.77/1.75  tff(c_1666, plain, (![C_98]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_98))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1652, c_4])).
% 3.77/1.75  tff(c_1682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1666, c_1318])).
% 3.77/1.75  tff(c_1683, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1532])).
% 3.77/1.75  tff(c_1691, plain, (![B_5]: (k4_xboole_0('#skF_1', k2_tarski(B_5, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1683, c_94])).
% 3.77/1.75  tff(c_1833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1691, c_1318])).
% 3.77/1.75  tff(c_1835, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_22])).
% 3.77/1.75  tff(c_24, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_1982, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_24])).
% 3.77/1.75  tff(c_1983, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1982])).
% 3.77/1.75  tff(c_1994, plain, (![B_5, C_6]: (k4_xboole_0('#skF_1', k2_tarski(B_5, C_6))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1983, c_98])).
% 3.77/1.75  tff(c_1834, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_22])).
% 3.77/1.75  tff(c_1991, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1834])).
% 3.77/1.75  tff(c_2034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1994, c_1991])).
% 3.77/1.75  tff(c_2035, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1982])).
% 3.77/1.75  tff(c_2037, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2035])).
% 3.77/1.75  tff(c_2038, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_1834])).
% 3.77/1.75  tff(c_2056, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2037, c_10])).
% 3.77/1.75  tff(c_2072, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_2056])).
% 3.77/1.75  tff(c_2078, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_2072, c_4])).
% 3.77/1.75  tff(c_2100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2038, c_2078])).
% 3.77/1.75  tff(c_2101, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2035])).
% 3.77/1.75  tff(c_2105, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_2101])).
% 3.77/1.75  tff(c_2109, plain, (![C_6]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2105, c_96])).
% 3.77/1.75  tff(c_2254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2109, c_1834])).
% 3.77/1.75  tff(c_2255, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2101])).
% 3.77/1.75  tff(c_2375, plain, (![B_128]: (r1_tarski('#skF_1', k2_tarski(B_128, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2255, c_12])).
% 3.77/1.75  tff(c_2389, plain, (![B_128]: (k4_xboole_0('#skF_1', k2_tarski(B_128, '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2375, c_4])).
% 3.77/1.75  tff(c_2405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2389, c_1834])).
% 3.77/1.75  tff(c_2407, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 3.77/1.75  tff(c_2432, plain, (![B_5, C_6]: (k4_xboole_0('#skF_4', k2_tarski(B_5, C_6))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_2407, c_98])).
% 3.77/1.75  tff(c_32, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.75  tff(c_2537, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_2407, c_32])).
% 3.77/1.75  tff(c_2538, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_2537])).
% 3.77/1.75  tff(c_2406, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 3.77/1.75  tff(c_2431, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_2406])).
% 3.77/1.75  tff(c_2539, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_2431])).
% 3.77/1.75  tff(c_2542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2432, c_2539])).
% 3.77/1.75  tff(c_2543, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2537])).
% 3.77/1.75  tff(c_2545, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2543])).
% 3.77/1.75  tff(c_2548, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2545, c_2431])).
% 3.77/1.75  tff(c_2451, plain, (![A_137, B_138]: (k4_xboole_0(A_137, B_138)='#skF_4' | ~r1_tarski(A_137, B_138))), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_4])).
% 3.77/1.75  tff(c_2474, plain, (![B_5, C_6]: (k4_xboole_0(k2_tarski(B_5, C_6), k2_tarski(B_5, C_6))='#skF_4')), inference(resolution, [status(thm)], [c_10, c_2451])).
% 3.77/1.75  tff(c_2555, plain, (k4_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2545, c_2474])).
% 3.77/1.75  tff(c_2581, plain, (k4_xboole_0('#skF_1', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2545, c_2555])).
% 3.77/1.75  tff(c_2611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2548, c_2581])).
% 3.77/1.75  tff(c_2612, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2543])).
% 3.77/1.75  tff(c_2614, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_2612])).
% 3.77/1.75  tff(c_2478, plain, (![B_5, C_6]: (k4_xboole_0(k1_tarski(B_5), k2_tarski(B_5, C_6))='#skF_4')), inference(resolution, [status(thm)], [c_14, c_2451])).
% 3.77/1.75  tff(c_2618, plain, (![C_6]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_6))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2614, c_2478])).
% 3.77/1.75  tff(c_2713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2618, c_2431])).
% 3.77/1.75  tff(c_2714, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2612])).
% 3.77/1.75  tff(c_2776, plain, (![B_150]: (r1_tarski('#skF_1', k2_tarski(B_150, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2714, c_12])).
% 3.77/1.75  tff(c_2408, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)='#skF_4' | ~r1_tarski(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_4])).
% 3.77/1.75  tff(c_2784, plain, (![B_150]: (k4_xboole_0('#skF_1', k2_tarski(B_150, '#skF_3'))='#skF_4')), inference(resolution, [status(thm)], [c_2776, c_2408])).
% 3.77/1.75  tff(c_2800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2784, c_2431])).
% 3.77/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.75  
% 3.77/1.75  Inference rules
% 3.77/1.75  ----------------------
% 3.77/1.75  #Ref     : 0
% 3.77/1.75  #Sup     : 669
% 3.77/1.75  #Fact    : 0
% 3.77/1.75  #Define  : 0
% 3.77/1.75  #Split   : 25
% 3.77/1.75  #Chain   : 0
% 3.77/1.75  #Close   : 0
% 3.77/1.75  
% 3.77/1.75  Ordering : KBO
% 3.77/1.75  
% 3.77/1.75  Simplification rules
% 3.77/1.75  ----------------------
% 3.77/1.75  #Subsume      : 30
% 3.77/1.75  #Demod        : 470
% 3.77/1.75  #Tautology    : 451
% 3.77/1.75  #SimpNegUnit  : 60
% 3.77/1.75  #BackRed      : 88
% 3.77/1.75  
% 3.77/1.75  #Partial instantiations: 0
% 3.77/1.75  #Strategies tried      : 1
% 3.77/1.75  
% 3.77/1.75  Timing (in seconds)
% 3.77/1.75  ----------------------
% 3.77/1.75  Preprocessing        : 0.27
% 3.77/1.75  Parsing              : 0.13
% 3.77/1.75  CNF conversion       : 0.02
% 3.77/1.75  Main loop            : 0.65
% 3.77/1.75  Inferencing          : 0.22
% 3.77/1.75  Reduction            : 0.24
% 3.77/1.75  Demodulation         : 0.17
% 3.77/1.75  BG Simplification    : 0.03
% 3.77/1.75  Subsumption          : 0.11
% 3.77/1.75  Abstraction          : 0.03
% 3.77/1.75  MUC search           : 0.00
% 3.77/1.75  Cooper               : 0.00
% 3.77/1.75  Total                : 0.97
% 3.77/1.75  Index Insertion      : 0.00
% 3.77/1.75  Index Deletion       : 0.00
% 3.77/1.75  Index Matching       : 0.00
% 3.77/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
