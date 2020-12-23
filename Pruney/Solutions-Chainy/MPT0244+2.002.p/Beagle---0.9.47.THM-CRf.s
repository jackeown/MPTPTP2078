%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 211 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  133 ( 347 expanded)
%              Number of equality atoms :   69 ( 189 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1229,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(A_100,B_101) = k1_xboole_0
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1244,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1229])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_tarski(A_19),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_132,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_46,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_316,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_318,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_4])).

tff(c_324,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_318])).

tff(c_332,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_324])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = A_35
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_506,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(k1_tarski(A_67),B_68) = k1_tarski(A_67)
      | r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_18,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_521,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(k1_tarski(A_67),k1_tarski(A_67)) = k3_xboole_0(k1_tarski(A_67),B_68)
      | r2_hidden(A_67,B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_18])).

tff(c_560,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(k1_tarski(A_69),B_70) = k1_xboole_0
      | r2_hidden(A_69,B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_521])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_603,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(B_71,k1_tarski(A_72)) = k1_xboole_0
      | r2_hidden(A_72,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_2])).

tff(c_16,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_325,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_316,c_12])).

tff(c_337,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_18])).

tff(c_340,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_337])).

tff(c_613,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_340])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_101,c_613])).

tff(c_658,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_664,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_658])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_170,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_665,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_170])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_665])).

tff(c_670,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_658])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_681,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_14])).

tff(c_688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_166])).

tff(c_689,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_741,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_745,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_689,c_741])).

tff(c_757,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_745])).

tff(c_772,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_757])).

tff(c_1032,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(k1_tarski(A_93),B_94) = k1_tarski(A_93)
      | r2_hidden(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_1047,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(k1_tarski(A_93),k1_tarski(A_93)) = k3_xboole_0(k1_tarski(A_93),B_94)
      | r2_hidden(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_18])).

tff(c_1090,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(k1_tarski(A_95),B_96) = k1_xboole_0
      | r2_hidden(A_95,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1047])).

tff(c_1133,plain,(
    ! [B_97,A_98] :
      ( k3_xboole_0(B_97,k1_tarski(A_98)) = k1_xboole_0
      | r2_hidden(A_98,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_2])).

tff(c_694,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_689,c_12])).

tff(c_799,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_821,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_799])).

tff(c_838,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_821])).

tff(c_1146,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_838])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_101,c_1146])).

tff(c_1196,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1428,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_38])).

tff(c_1429,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1428])).

tff(c_1439,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_14])).

tff(c_1195,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1195])).

tff(c_1447,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1428])).

tff(c_1216,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1195])).

tff(c_1449,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_1216])).

tff(c_1453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1449])).

tff(c_1455,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1473,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1455,c_1455,c_42])).

tff(c_1474,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1473])).

tff(c_1457,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1455,c_14])).

tff(c_1476,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_1457])).

tff(c_1454,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_1454])).

tff(c_1489,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1473])).

tff(c_1491,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_1454])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.51  
% 3.12/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.12/1.51  
% 3.12/1.51  %Foreground sorts:
% 3.12/1.51  
% 3.12/1.51  
% 3.12/1.51  %Background operators:
% 3.12/1.51  
% 3.12/1.51  
% 3.12/1.51  %Foreground operators:
% 3.12/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.12/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.51  
% 3.27/1.53  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.27/1.53  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.27/1.53  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.27/1.53  tff(f_69, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.27/1.53  tff(f_62, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.27/1.53  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.27/1.53  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.27/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.27/1.53  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.27/1.53  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.27/1.53  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.53  tff(c_1229, plain, (![A_100, B_101]: (k4_xboole_0(A_100, B_101)=k1_xboole_0 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.53  tff(c_1244, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1229])).
% 3.27/1.53  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.53  tff(c_36, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.53  tff(c_131, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 3.27/1.53  tff(c_132, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.53  tff(c_147, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_132])).
% 3.27/1.53  tff(c_46, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.53  tff(c_316, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.27/1.53  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.53  tff(c_318, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_316, c_4])).
% 3.27/1.53  tff(c_324, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_131, c_318])).
% 3.27/1.53  tff(c_332, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_324])).
% 3.27/1.53  tff(c_40, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.53  tff(c_101, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_40])).
% 3.27/1.53  tff(c_34, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.53  tff(c_105, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=A_35 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.53  tff(c_506, plain, (![A_67, B_68]: (k4_xboole_0(k1_tarski(A_67), B_68)=k1_tarski(A_67) | r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_34, c_105])).
% 3.27/1.53  tff(c_18, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.53  tff(c_521, plain, (![A_67, B_68]: (k4_xboole_0(k1_tarski(A_67), k1_tarski(A_67))=k3_xboole_0(k1_tarski(A_67), B_68) | r2_hidden(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_506, c_18])).
% 3.27/1.53  tff(c_560, plain, (![A_69, B_70]: (k3_xboole_0(k1_tarski(A_69), B_70)=k1_xboole_0 | r2_hidden(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_521])).
% 3.27/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.53  tff(c_603, plain, (![B_71, A_72]: (k3_xboole_0(B_71, k1_tarski(A_72))=k1_xboole_0 | r2_hidden(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_560, c_2])).
% 3.27/1.53  tff(c_16, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.53  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.53  tff(c_325, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_316, c_12])).
% 3.27/1.53  tff(c_337, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_325, c_18])).
% 3.27/1.53  tff(c_340, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_337])).
% 3.27/1.53  tff(c_613, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_603, c_340])).
% 3.27/1.53  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_101, c_613])).
% 3.27/1.53  tff(c_658, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 3.27/1.53  tff(c_664, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_658])).
% 3.27/1.53  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.53  tff(c_44, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.53  tff(c_166, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.27/1.53  tff(c_170, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_166])).
% 3.27/1.53  tff(c_665, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_664, c_170])).
% 3.27/1.53  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_665])).
% 3.27/1.53  tff(c_670, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_658])).
% 3.27/1.53  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.53  tff(c_681, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_14])).
% 3.27/1.53  tff(c_688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_681, c_166])).
% 3.27/1.53  tff(c_689, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.27/1.53  tff(c_741, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.53  tff(c_745, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_689, c_741])).
% 3.27/1.53  tff(c_757, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_131, c_745])).
% 3.27/1.53  tff(c_772, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_757])).
% 3.27/1.53  tff(c_1032, plain, (![A_93, B_94]: (k4_xboole_0(k1_tarski(A_93), B_94)=k1_tarski(A_93) | r2_hidden(A_93, B_94))), inference(resolution, [status(thm)], [c_34, c_105])).
% 3.27/1.53  tff(c_1047, plain, (![A_93, B_94]: (k4_xboole_0(k1_tarski(A_93), k1_tarski(A_93))=k3_xboole_0(k1_tarski(A_93), B_94) | r2_hidden(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_18])).
% 3.27/1.53  tff(c_1090, plain, (![A_95, B_96]: (k3_xboole_0(k1_tarski(A_95), B_96)=k1_xboole_0 | r2_hidden(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1047])).
% 3.27/1.53  tff(c_1133, plain, (![B_97, A_98]: (k3_xboole_0(B_97, k1_tarski(A_98))=k1_xboole_0 | r2_hidden(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_1090, c_2])).
% 3.27/1.53  tff(c_694, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_689, c_12])).
% 3.27/1.53  tff(c_799, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.53  tff(c_821, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_694, c_799])).
% 3.27/1.53  tff(c_838, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_821])).
% 3.27/1.53  tff(c_1146, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1133, c_838])).
% 3.27/1.53  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_772, c_101, c_1146])).
% 3.27/1.53  tff(c_1196, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.27/1.53  tff(c_38, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.53  tff(c_1428, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_38])).
% 3.27/1.53  tff(c_1429, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1428])).
% 3.27/1.53  tff(c_1439, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1429, c_14])).
% 3.27/1.53  tff(c_1195, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 3.27/1.53  tff(c_1446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1195])).
% 3.27/1.53  tff(c_1447, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1428])).
% 3.27/1.53  tff(c_1216, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1195])).
% 3.27/1.53  tff(c_1449, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_1216])).
% 3.27/1.53  tff(c_1453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1449])).
% 3.27/1.53  tff(c_1455, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.27/1.53  tff(c_42, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.53  tff(c_1473, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1455, c_1455, c_42])).
% 3.27/1.53  tff(c_1474, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_1473])).
% 3.27/1.53  tff(c_1457, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1455, c_14])).
% 3.27/1.53  tff(c_1476, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_1457])).
% 3.27/1.53  tff(c_1454, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 3.27/1.53  tff(c_1488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1476, c_1454])).
% 3.27/1.53  tff(c_1489, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1473])).
% 3.27/1.53  tff(c_1491, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1489, c_1454])).
% 3.27/1.53  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1491])).
% 3.27/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.53  
% 3.27/1.53  Inference rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Ref     : 0
% 3.27/1.53  #Sup     : 330
% 3.27/1.53  #Fact    : 0
% 3.27/1.53  #Define  : 0
% 3.27/1.53  #Split   : 8
% 3.27/1.53  #Chain   : 0
% 3.27/1.53  #Close   : 0
% 3.27/1.53  
% 3.27/1.53  Ordering : KBO
% 3.27/1.53  
% 3.27/1.53  Simplification rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Subsume      : 13
% 3.27/1.53  #Demod        : 114
% 3.27/1.53  #Tautology    : 201
% 3.27/1.53  #SimpNegUnit  : 9
% 3.27/1.53  #BackRed      : 33
% 3.27/1.53  
% 3.27/1.53  #Partial instantiations: 0
% 3.27/1.53  #Strategies tried      : 1
% 3.27/1.53  
% 3.27/1.53  Timing (in seconds)
% 3.27/1.53  ----------------------
% 3.27/1.53  Preprocessing        : 0.33
% 3.27/1.53  Parsing              : 0.17
% 3.27/1.53  CNF conversion       : 0.02
% 3.27/1.53  Main loop            : 0.38
% 3.27/1.53  Inferencing          : 0.14
% 3.27/1.53  Reduction            : 0.12
% 3.27/1.53  Demodulation         : 0.09
% 3.27/1.53  BG Simplification    : 0.02
% 3.27/1.53  Subsumption          : 0.06
% 3.27/1.53  Abstraction          : 0.02
% 3.27/1.53  MUC search           : 0.00
% 3.27/1.53  Cooper               : 0.00
% 3.27/1.53  Total                : 0.76
% 3.27/1.53  Index Insertion      : 0.00
% 3.27/1.53  Index Deletion       : 0.00
% 3.27/1.54  Index Matching       : 0.00
% 3.27/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
