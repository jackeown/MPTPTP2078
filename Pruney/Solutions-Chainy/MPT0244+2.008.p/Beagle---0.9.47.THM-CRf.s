%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:57 EST 2020

% Result     : Theorem 13.77s
% Output     : CNFRefutation 13.89s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 546 expanded)
%              Number of leaves         :   27 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 (1112 expanded)
%              Number of equality atoms :  117 ( 590 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_6',k1_tarski('#skF_7'))
    | k1_tarski('#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_87,plain,(
    k1_tarski('#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_6',k1_tarski('#skF_7'))
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_200,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_209,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_200,c_28])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_220,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_50,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_4])).

tff(c_32,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_225,plain,(
    ! [D_51] :
      ( D_51 = '#skF_9'
      | ~ r2_hidden(D_51,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_220,c_32])).

tff(c_229,plain,
    ( '#skF_3'('#skF_8') = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_225])).

tff(c_232,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_229])).

tff(c_236,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_20])).

tff(c_239,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_236])).

tff(c_1405,plain,(
    ! [A_944,B_945] :
      ( '#skF_4'(A_944,B_945) = A_944
      | r2_hidden('#skF_5'(A_944,B_945),B_945)
      | k1_tarski(A_944) = B_945 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_224,plain,(
    ! [D_50] :
      ( D_50 = '#skF_9'
      | ~ r2_hidden(D_50,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_220,c_32])).

tff(c_1431,plain,(
    ! [A_946] :
      ( '#skF_5'(A_946,'#skF_8') = '#skF_9'
      | '#skF_4'(A_946,'#skF_8') = A_946
      | k1_tarski(A_946) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1405,c_224])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_202,plain,
    ( k1_tarski('#skF_9') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_200,c_22])).

tff(c_208,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_202])).

tff(c_1452,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1431,c_208])).

tff(c_1477,plain,
    ( '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1452])).

tff(c_1482,plain,(
    '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1477])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15),B_15)
      | '#skF_5'(A_14,B_15) != A_14
      | k1_tarski(A_14) = B_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1486,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | '#skF_5'('#skF_9','#skF_8') != '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_36])).

tff(c_1490,plain,
    ( '#skF_5'('#skF_9','#skF_8') != '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_1486])).

tff(c_1491,plain,(
    '#skF_5'('#skF_9','#skF_8') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1490])).

tff(c_1499,plain,(
    ! [A_947,B_948] :
      ( ~ r2_hidden('#skF_4'(A_947,B_948),B_948)
      | r2_hidden('#skF_5'(A_947,B_948),B_948)
      | k1_tarski(A_947) = B_948 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1579,plain,(
    ! [A_952] :
      ( '#skF_5'(A_952,'#skF_8') = '#skF_9'
      | ~ r2_hidden('#skF_4'(A_952,'#skF_8'),'#skF_8')
      | k1_tarski(A_952) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1499,c_224])).

tff(c_1582,plain,
    ( '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | ~ r2_hidden('#skF_9','#skF_8')
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_1579])).

tff(c_1584,plain,
    ( '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_1582])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1491,c_1584])).

tff(c_1588,plain,(
    '#skF_4'('#skF_9','#skF_8') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1477])).

tff(c_1587,plain,(
    '#skF_5'('#skF_9','#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1477])).

tff(c_38,plain,(
    ! [A_14,B_15] :
      ( '#skF_4'(A_14,B_15) = A_14
      | '#skF_5'(A_14,B_15) != A_14
      | k1_tarski(A_14) = B_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1594,plain,
    ( '#skF_4'('#skF_9','#skF_8') = '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_38])).

tff(c_1601,plain,(
    '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1594])).

tff(c_1603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1588,c_1601])).

tff(c_1604,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1606,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1604])).

tff(c_58,plain,
    ( ~ r1_tarski('#skF_6',k1_tarski('#skF_7'))
    | r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_169,plain,(
    ~ r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1607,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_169])).

tff(c_1610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1607])).

tff(c_1611,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1604])).

tff(c_30,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1619,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_30])).

tff(c_1635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_169])).

tff(c_1636,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1646,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1636,c_28])).

tff(c_1682,plain,(
    ! [D_959,B_960,A_961] :
      ( r2_hidden(D_959,B_960)
      | ~ r2_hidden(D_959,k3_xboole_0(A_961,B_960)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46547,plain,(
    ! [D_12331] :
      ( r2_hidden(D_12331,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_12331,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_1682])).

tff(c_46552,plain,(
    ! [D_12332] :
      ( D_12332 = '#skF_9'
      | ~ r2_hidden(D_12332,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46547,c_32])).

tff(c_46556,plain,
    ( '#skF_3'('#skF_8') = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_46552])).

tff(c_46559,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_46556])).

tff(c_46563,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_46559,c_20])).

tff(c_46566,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_46563])).

tff(c_47911,plain,(
    ! [A_13416,B_13417] :
      ( '#skF_4'(A_13416,B_13417) = A_13416
      | r2_hidden('#skF_5'(A_13416,B_13417),B_13417)
      | k1_tarski(A_13416) = B_13417 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46551,plain,(
    ! [D_12331] :
      ( D_12331 = '#skF_9'
      | ~ r2_hidden(D_12331,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46547,c_32])).

tff(c_49039,plain,(
    ! [A_13452] :
      ( '#skF_5'(A_13452,'#skF_8') = '#skF_9'
      | '#skF_4'(A_13452,'#skF_8') = A_13452
      | k1_tarski(A_13452) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_47911,c_46551])).

tff(c_1639,plain,
    ( k1_tarski('#skF_9') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1636,c_22])).

tff(c_1645,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1639])).

tff(c_49075,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_49039,c_1645])).

tff(c_49106,plain,
    ( '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_49075])).

tff(c_49112,plain,(
    '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_49106])).

tff(c_49117,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | '#skF_5'('#skF_9','#skF_8') != '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_49112,c_36])).

tff(c_49121,plain,
    ( '#skF_5'('#skF_9','#skF_8') != '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46566,c_49117])).

tff(c_49122,plain,(
    '#skF_5'('#skF_9','#skF_8') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_49121])).

tff(c_47954,plain,(
    ! [A_13419,B_13420] :
      ( ~ r2_hidden('#skF_4'(A_13419,B_13420),B_13420)
      | r2_hidden('#skF_5'(A_13419,B_13420),B_13420)
      | k1_tarski(A_13419) = B_13420 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53086,plain,(
    ! [A_13544,A_13545,B_13546] :
      ( r2_hidden('#skF_5'(A_13544,k3_xboole_0(A_13545,B_13546)),B_13546)
      | ~ r2_hidden('#skF_4'(A_13544,k3_xboole_0(A_13545,B_13546)),k3_xboole_0(A_13545,B_13546))
      | k3_xboole_0(A_13545,B_13546) = k1_tarski(A_13544) ) ),
    inference(resolution,[status(thm)],[c_47954,c_4])).

tff(c_53204,plain,(
    ! [A_13544] :
      ( r2_hidden('#skF_5'(A_13544,k3_xboole_0('#skF_8',k1_tarski('#skF_9'))),k1_tarski('#skF_9'))
      | ~ r2_hidden('#skF_4'(A_13544,k3_xboole_0('#skF_8',k1_tarski('#skF_9'))),'#skF_8')
      | k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = k1_tarski(A_13544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_53086])).

tff(c_53736,plain,(
    ! [A_13552] :
      ( r2_hidden('#skF_5'(A_13552,'#skF_8'),k1_tarski('#skF_9'))
      | ~ r2_hidden('#skF_4'(A_13552,'#skF_8'),'#skF_8')
      | k1_tarski(A_13552) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_1646,c_1646,c_53204])).

tff(c_89695,plain,(
    ! [A_23909] :
      ( '#skF_5'(A_23909,'#skF_8') = '#skF_9'
      | ~ r2_hidden('#skF_4'(A_23909,'#skF_8'),'#skF_8')
      | k1_tarski(A_23909) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_53736,c_32])).

tff(c_89704,plain,
    ( '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | ~ r2_hidden('#skF_9','#skF_8')
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_49112,c_89695])).

tff(c_89707,plain,
    ( '#skF_5'('#skF_9','#skF_8') = '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46566,c_89704])).

tff(c_89709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_49122,c_89707])).

tff(c_89711,plain,(
    '#skF_4'('#skF_9','#skF_8') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_49106])).

tff(c_89710,plain,(
    '#skF_5'('#skF_9','#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_49106])).

tff(c_89755,plain,
    ( '#skF_4'('#skF_9','#skF_8') = '#skF_9'
    | k1_tarski('#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_89710,c_38])).

tff(c_89764,plain,(
    '#skF_4'('#skF_9','#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_89755])).

tff(c_89796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89711,c_89764])).

tff(c_89798,plain,(
    k1_tarski('#skF_9') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89799,plain,(
    k1_tarski('#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_89811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89798,c_89799])).

tff(c_89812,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_89825,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_89812])).

tff(c_89797,plain,(
    ~ r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_89826,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89825,c_89797])).

tff(c_89829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89826])).

tff(c_89830,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_89812])).

tff(c_89834,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89830,c_30])).

tff(c_89842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89834,c_89797])).

tff(c_89844,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_89845,plain,(
    ! [A_13] : r1_tarski('#skF_8',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89844,c_30])).

tff(c_56,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89865,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89844,c_89844,c_56])).

tff(c_89866,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_89865])).

tff(c_89843,plain,(
    ~ r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_89867,plain,(
    ~ r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89866,c_89843])).

tff(c_89870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89845,c_89867])).

tff(c_89871,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_89865])).

tff(c_89873,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89871,c_89843])).

tff(c_89876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.77/5.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.77/5.97  
% 13.77/5.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.77/5.98  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 13.77/5.98  
% 13.77/5.98  %Foreground sorts:
% 13.77/5.98  
% 13.77/5.98  
% 13.77/5.98  %Background operators:
% 13.77/5.98  
% 13.77/5.98  
% 13.77/5.98  %Foreground operators:
% 13.77/5.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.77/5.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.77/5.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.77/5.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.77/5.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.77/5.98  tff('#skF_7', type, '#skF_7': $i).
% 13.77/5.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.77/5.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.77/5.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.77/5.98  tff('#skF_6', type, '#skF_6': $i).
% 13.77/5.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.77/5.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.77/5.98  tff('#skF_9', type, '#skF_9': $i).
% 13.77/5.98  tff('#skF_8', type, '#skF_8': $i).
% 13.77/5.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.77/5.98  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.77/5.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.77/5.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.77/5.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.77/5.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.77/5.98  
% 13.89/5.99  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.89/5.99  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 13.89/5.99  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.89/5.99  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.89/5.99  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 13.89/5.99  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 13.89/5.99  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.89/5.99  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.89/5.99  tff(c_50, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7')) | k1_tarski('#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.89/5.99  tff(c_87, plain, (k1_tarski('#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_50])).
% 13.89/5.99  tff(c_54, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7')) | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.89/5.99  tff(c_74, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_54])).
% 13.89/5.99  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.89/5.99  tff(c_60, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6' | r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.89/5.99  tff(c_200, plain, (r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_60])).
% 13.89/5.99  tff(c_28, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.89/5.99  tff(c_209, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(resolution, [status(thm)], [c_200, c_28])).
% 13.89/5.99  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.89/5.99  tff(c_220, plain, (![D_50]: (r2_hidden(D_50, k1_tarski('#skF_9')) | ~r2_hidden(D_50, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_4])).
% 13.89/5.99  tff(c_32, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/5.99  tff(c_225, plain, (![D_51]: (D_51='#skF_9' | ~r2_hidden(D_51, '#skF_8'))), inference(resolution, [status(thm)], [c_220, c_32])).
% 13.89/5.99  tff(c_229, plain, ('#skF_3'('#skF_8')='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_225])).
% 13.89/5.99  tff(c_232, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_74, c_229])).
% 13.89/5.99  tff(c_236, plain, (r2_hidden('#skF_9', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_232, c_20])).
% 13.89/5.99  tff(c_239, plain, (r2_hidden('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_74, c_236])).
% 13.89/5.99  tff(c_1405, plain, (![A_944, B_945]: ('#skF_4'(A_944, B_945)=A_944 | r2_hidden('#skF_5'(A_944, B_945), B_945) | k1_tarski(A_944)=B_945)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/5.99  tff(c_224, plain, (![D_50]: (D_50='#skF_9' | ~r2_hidden(D_50, '#skF_8'))), inference(resolution, [status(thm)], [c_220, c_32])).
% 13.89/5.99  tff(c_1431, plain, (![A_946]: ('#skF_5'(A_946, '#skF_8')='#skF_9' | '#skF_4'(A_946, '#skF_8')=A_946 | k1_tarski(A_946)='#skF_8')), inference(resolution, [status(thm)], [c_1405, c_224])).
% 13.89/5.99  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.89/5.99  tff(c_202, plain, (k1_tarski('#skF_9')='#skF_8' | ~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_200, c_22])).
% 13.89/5.99  tff(c_208, plain, (~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_87, c_202])).
% 13.89/5.99  tff(c_1452, plain, (~r1_tarski('#skF_8', '#skF_8') | '#skF_5'('#skF_9', '#skF_8')='#skF_9' | '#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1431, c_208])).
% 13.89/5.99  tff(c_1477, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9' | '#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1452])).
% 13.89/5.99  tff(c_1482, plain, ('#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_1477])).
% 13.89/5.99  tff(c_36, plain, (![A_14, B_15]: (~r2_hidden('#skF_4'(A_14, B_15), B_15) | '#skF_5'(A_14, B_15)!=A_14 | k1_tarski(A_14)=B_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/5.99  tff(c_1486, plain, (~r2_hidden('#skF_9', '#skF_8') | '#skF_5'('#skF_9', '#skF_8')!='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1482, c_36])).
% 13.89/6.00  tff(c_1490, plain, ('#skF_5'('#skF_9', '#skF_8')!='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_1486])).
% 13.89/6.00  tff(c_1491, plain, ('#skF_5'('#skF_9', '#skF_8')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_87, c_1490])).
% 13.89/6.00  tff(c_1499, plain, (![A_947, B_948]: (~r2_hidden('#skF_4'(A_947, B_948), B_948) | r2_hidden('#skF_5'(A_947, B_948), B_948) | k1_tarski(A_947)=B_948)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/6.00  tff(c_1579, plain, (![A_952]: ('#skF_5'(A_952, '#skF_8')='#skF_9' | ~r2_hidden('#skF_4'(A_952, '#skF_8'), '#skF_8') | k1_tarski(A_952)='#skF_8')), inference(resolution, [status(thm)], [c_1499, c_224])).
% 13.89/6.00  tff(c_1582, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9' | ~r2_hidden('#skF_9', '#skF_8') | k1_tarski('#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1482, c_1579])).
% 13.89/6.00  tff(c_1584, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_1582])).
% 13.89/6.00  tff(c_1586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_1491, c_1584])).
% 13.89/6.00  tff(c_1588, plain, ('#skF_4'('#skF_9', '#skF_8')!='#skF_9'), inference(splitRight, [status(thm)], [c_1477])).
% 13.89/6.00  tff(c_1587, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_1477])).
% 13.89/6.00  tff(c_38, plain, (![A_14, B_15]: ('#skF_4'(A_14, B_15)=A_14 | '#skF_5'(A_14, B_15)!=A_14 | k1_tarski(A_14)=B_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/6.00  tff(c_1594, plain, ('#skF_4'('#skF_9', '#skF_8')='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1587, c_38])).
% 13.89/6.00  tff(c_1601, plain, ('#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_87, c_1594])).
% 13.89/6.00  tff(c_1603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1588, c_1601])).
% 13.89/6.00  tff(c_1604, plain, (k1_xboole_0='#skF_6' | k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 13.89/6.00  tff(c_1606, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_1604])).
% 13.89/6.00  tff(c_58, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7')) | r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.89/6.00  tff(c_169, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_58])).
% 13.89/6.00  tff(c_1607, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_169])).
% 13.89/6.00  tff(c_1610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1607])).
% 13.89/6.00  tff(c_1611, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1604])).
% 13.89/6.00  tff(c_30, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.89/6.00  tff(c_1619, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_30])).
% 13.89/6.00  tff(c_1635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1619, c_169])).
% 13.89/6.00  tff(c_1636, plain, (r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_58])).
% 13.89/6.00  tff(c_1646, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(resolution, [status(thm)], [c_1636, c_28])).
% 13.89/6.00  tff(c_1682, plain, (![D_959, B_960, A_961]: (r2_hidden(D_959, B_960) | ~r2_hidden(D_959, k3_xboole_0(A_961, B_960)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.89/6.00  tff(c_46547, plain, (![D_12331]: (r2_hidden(D_12331, k1_tarski('#skF_9')) | ~r2_hidden(D_12331, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_1682])).
% 13.89/6.00  tff(c_46552, plain, (![D_12332]: (D_12332='#skF_9' | ~r2_hidden(D_12332, '#skF_8'))), inference(resolution, [status(thm)], [c_46547, c_32])).
% 13.89/6.00  tff(c_46556, plain, ('#skF_3'('#skF_8')='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_46552])).
% 13.89/6.00  tff(c_46559, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_74, c_46556])).
% 13.89/6.00  tff(c_46563, plain, (r2_hidden('#skF_9', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_46559, c_20])).
% 13.89/6.00  tff(c_46566, plain, (r2_hidden('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_74, c_46563])).
% 13.89/6.00  tff(c_47911, plain, (![A_13416, B_13417]: ('#skF_4'(A_13416, B_13417)=A_13416 | r2_hidden('#skF_5'(A_13416, B_13417), B_13417) | k1_tarski(A_13416)=B_13417)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/6.00  tff(c_46551, plain, (![D_12331]: (D_12331='#skF_9' | ~r2_hidden(D_12331, '#skF_8'))), inference(resolution, [status(thm)], [c_46547, c_32])).
% 13.89/6.00  tff(c_49039, plain, (![A_13452]: ('#skF_5'(A_13452, '#skF_8')='#skF_9' | '#skF_4'(A_13452, '#skF_8')=A_13452 | k1_tarski(A_13452)='#skF_8')), inference(resolution, [status(thm)], [c_47911, c_46551])).
% 13.89/6.00  tff(c_1639, plain, (k1_tarski('#skF_9')='#skF_8' | ~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1636, c_22])).
% 13.89/6.00  tff(c_1645, plain, (~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_87, c_1639])).
% 13.89/6.00  tff(c_49075, plain, (~r1_tarski('#skF_8', '#skF_8') | '#skF_5'('#skF_9', '#skF_8')='#skF_9' | '#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_49039, c_1645])).
% 13.89/6.00  tff(c_49106, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9' | '#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_49075])).
% 13.89/6.00  tff(c_49112, plain, ('#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_49106])).
% 13.89/6.00  tff(c_49117, plain, (~r2_hidden('#skF_9', '#skF_8') | '#skF_5'('#skF_9', '#skF_8')!='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_49112, c_36])).
% 13.89/6.00  tff(c_49121, plain, ('#skF_5'('#skF_9', '#skF_8')!='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46566, c_49117])).
% 13.89/6.00  tff(c_49122, plain, ('#skF_5'('#skF_9', '#skF_8')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_87, c_49121])).
% 13.89/6.00  tff(c_47954, plain, (![A_13419, B_13420]: (~r2_hidden('#skF_4'(A_13419, B_13420), B_13420) | r2_hidden('#skF_5'(A_13419, B_13420), B_13420) | k1_tarski(A_13419)=B_13420)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.89/6.00  tff(c_53086, plain, (![A_13544, A_13545, B_13546]: (r2_hidden('#skF_5'(A_13544, k3_xboole_0(A_13545, B_13546)), B_13546) | ~r2_hidden('#skF_4'(A_13544, k3_xboole_0(A_13545, B_13546)), k3_xboole_0(A_13545, B_13546)) | k3_xboole_0(A_13545, B_13546)=k1_tarski(A_13544))), inference(resolution, [status(thm)], [c_47954, c_4])).
% 13.89/6.00  tff(c_53204, plain, (![A_13544]: (r2_hidden('#skF_5'(A_13544, k3_xboole_0('#skF_8', k1_tarski('#skF_9'))), k1_tarski('#skF_9')) | ~r2_hidden('#skF_4'(A_13544, k3_xboole_0('#skF_8', k1_tarski('#skF_9'))), '#skF_8') | k3_xboole_0('#skF_8', k1_tarski('#skF_9'))=k1_tarski(A_13544))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_53086])).
% 13.89/6.00  tff(c_53736, plain, (![A_13552]: (r2_hidden('#skF_5'(A_13552, '#skF_8'), k1_tarski('#skF_9')) | ~r2_hidden('#skF_4'(A_13552, '#skF_8'), '#skF_8') | k1_tarski(A_13552)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1646, c_1646, c_53204])).
% 13.89/6.00  tff(c_89695, plain, (![A_23909]: ('#skF_5'(A_23909, '#skF_8')='#skF_9' | ~r2_hidden('#skF_4'(A_23909, '#skF_8'), '#skF_8') | k1_tarski(A_23909)='#skF_8')), inference(resolution, [status(thm)], [c_53736, c_32])).
% 13.89/6.00  tff(c_89704, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9' | ~r2_hidden('#skF_9', '#skF_8') | k1_tarski('#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_49112, c_89695])).
% 13.89/6.00  tff(c_89707, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46566, c_89704])).
% 13.89/6.00  tff(c_89709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_49122, c_89707])).
% 13.89/6.00  tff(c_89711, plain, ('#skF_4'('#skF_9', '#skF_8')!='#skF_9'), inference(splitRight, [status(thm)], [c_49106])).
% 13.89/6.00  tff(c_89710, plain, ('#skF_5'('#skF_9', '#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_49106])).
% 13.89/6.00  tff(c_89755, plain, ('#skF_4'('#skF_9', '#skF_8')='#skF_9' | k1_tarski('#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_89710, c_38])).
% 13.89/6.00  tff(c_89764, plain, ('#skF_4'('#skF_9', '#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_87, c_89755])).
% 13.89/6.00  tff(c_89796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89711, c_89764])).
% 13.89/6.00  tff(c_89798, plain, (k1_tarski('#skF_9')='#skF_8'), inference(splitRight, [status(thm)], [c_50])).
% 13.89/6.00  tff(c_52, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6' | k1_tarski('#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.89/6.00  tff(c_89799, plain, (k1_tarski('#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_52])).
% 13.89/6.00  tff(c_89811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89798, c_89799])).
% 13.89/6.00  tff(c_89812, plain, (k1_xboole_0='#skF_6' | k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 13.89/6.00  tff(c_89825, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_89812])).
% 13.89/6.00  tff(c_89797, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 13.89/6.00  tff(c_89826, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_89825, c_89797])).
% 13.89/6.00  tff(c_89829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_89826])).
% 13.89/6.00  tff(c_89830, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_89812])).
% 13.89/6.00  tff(c_89834, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_89830, c_30])).
% 13.89/6.00  tff(c_89842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89834, c_89797])).
% 13.89/6.00  tff(c_89844, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 13.89/6.00  tff(c_89845, plain, (![A_13]: (r1_tarski('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_89844, c_30])).
% 13.89/6.00  tff(c_56, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.89/6.00  tff(c_89865, plain, (k1_tarski('#skF_7')='#skF_6' | '#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89844, c_89844, c_56])).
% 13.89/6.00  tff(c_89866, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_89865])).
% 13.89/6.00  tff(c_89843, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 13.89/6.00  tff(c_89867, plain, (~r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_89866, c_89843])).
% 13.89/6.00  tff(c_89870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89845, c_89867])).
% 13.89/6.00  tff(c_89871, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_89865])).
% 13.89/6.00  tff(c_89873, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_89871, c_89843])).
% 13.89/6.00  tff(c_89876, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_89873])).
% 13.89/6.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.89/6.00  
% 13.89/6.00  Inference rules
% 13.89/6.00  ----------------------
% 13.89/6.00  #Ref     : 0
% 13.89/6.00  #Sup     : 12339
% 13.89/6.00  #Fact    : 13
% 13.89/6.00  #Define  : 0
% 13.89/6.00  #Split   : 46
% 13.89/6.00  #Chain   : 0
% 13.89/6.00  #Close   : 0
% 13.89/6.00  
% 13.89/6.00  Ordering : KBO
% 13.89/6.00  
% 13.89/6.00  Simplification rules
% 13.89/6.00  ----------------------
% 13.89/6.00  #Subsume      : 3591
% 13.89/6.00  #Demod        : 5788
% 13.89/6.00  #Tautology    : 3134
% 13.89/6.00  #SimpNegUnit  : 672
% 13.89/6.00  #BackRed      : 31
% 13.89/6.00  
% 13.89/6.00  #Partial instantiations: 15225
% 13.89/6.00  #Strategies tried      : 1
% 13.89/6.00  
% 13.89/6.00  Timing (in seconds)
% 13.89/6.00  ----------------------
% 13.89/6.00  Preprocessing        : 0.29
% 13.89/6.00  Parsing              : 0.14
% 13.89/6.00  CNF conversion       : 0.02
% 13.89/6.00  Main loop            : 4.88
% 13.89/6.00  Inferencing          : 1.47
% 13.89/6.00  Reduction            : 1.48
% 13.89/6.00  Demodulation         : 1.04
% 13.89/6.00  BG Simplification    : 0.18
% 13.89/6.00  Subsumption          : 1.39
% 13.89/6.00  Abstraction          : 0.25
% 13.89/6.00  MUC search           : 0.00
% 13.89/6.00  Cooper               : 0.00
% 13.89/6.00  Total                : 5.21
% 13.89/6.00  Index Insertion      : 0.00
% 13.89/6.00  Index Deletion       : 0.00
% 13.89/6.00  Index Matching       : 0.00
% 13.89/6.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
