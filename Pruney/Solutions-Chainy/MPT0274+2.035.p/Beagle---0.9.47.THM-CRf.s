%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:16 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 160 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 304 expanded)
%              Number of equality atoms :   24 (  69 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
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

tff(c_20,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_92,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_151,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_210,plain,(
    ! [A_99,C_100,B_101] :
      ( r1_xboole_0(k2_tarski(A_99,C_100),B_101)
      | r2_hidden(C_100,B_101)
      | r2_hidden(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_497,plain,(
    ! [A_186,C_187,B_188] :
      ( k4_xboole_0(k2_tarski(A_186,C_187),B_188) = k2_tarski(A_186,C_187)
      | r2_hidden(C_187,B_188)
      | r2_hidden(A_186,B_188) ) ),
    inference(resolution,[status(thm)],[c_210,c_12])).

tff(c_48,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k2_tarski('#skF_4','#skF_5')
    | r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_238,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k2_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_555,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_238])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_151,c_555])).

tff(c_604,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_606,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_604])).

tff(c_18,plain,(
    ! [D_17,A_12] : r2_hidden(D_17,k2_tarski(A_12,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_605,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_54,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k2_tarski('#skF_4','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_669,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_54])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,B_75)
      | ~ r2_hidden(C_76,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [C_76,B_9,A_8] :
      ( ~ r2_hidden(C_76,B_9)
      | ~ r2_hidden(C_76,k4_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_10,c_144])).

tff(c_692,plain,(
    ! [C_191] :
      ( ~ r2_hidden(C_191,'#skF_9')
      | ~ r2_hidden(C_191,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_150])).

tff(c_704,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_692])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_704])).

tff(c_715,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_604])).

tff(c_758,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_54])).

tff(c_802,plain,(
    ! [C_194] :
      ( ~ r2_hidden(C_194,'#skF_9')
      | ~ r2_hidden(C_194,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_150])).

tff(c_818,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_802])).

tff(c_825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_818])).

tff(c_826,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_828,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_827,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_895,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_56])).

tff(c_918,plain,(
    ! [C_205] :
      ( ~ r2_hidden(C_205,'#skF_9')
      | ~ r2_hidden(C_205,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_150])).

tff(c_930,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_918])).

tff(c_940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_930])).

tff(c_941,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_992,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_56])).

tff(c_1032,plain,(
    ! [C_214] :
      ( ~ r2_hidden(C_214,'#skF_9')
      | ~ r2_hidden(C_214,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_150])).

tff(c_1048,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_1032])).

tff(c_1055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1048])).

tff(c_1056,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1058,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1056])).

tff(c_1057,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1168,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_58])).

tff(c_1089,plain,(
    ! [A_220,B_221,C_222] :
      ( ~ r1_xboole_0(A_220,B_221)
      | ~ r2_hidden(C_222,B_221)
      | ~ r2_hidden(C_222,A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1095,plain,(
    ! [C_222,B_9,A_8] :
      ( ~ r2_hidden(C_222,B_9)
      | ~ r2_hidden(C_222,k4_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1089])).

tff(c_1207,plain,(
    ! [C_234] :
      ( ~ r2_hidden(C_234,'#skF_9')
      | ~ r2_hidden(C_234,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_1095])).

tff(c_1219,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_1207])).

tff(c_1229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1219])).

tff(c_1230,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1056])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1262,plain,(
    ! [A_240,B_241,C_242] :
      ( ~ r1_xboole_0(A_240,B_241)
      | ~ r2_hidden(C_242,B_241)
      | ~ r2_hidden(C_242,A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1307,plain,(
    ! [C_249,B_250,A_251] :
      ( ~ r2_hidden(C_249,B_250)
      | ~ r2_hidden(C_249,A_251)
      | k4_xboole_0(A_251,B_250) != A_251 ) ),
    inference(resolution,[status(thm)],[c_14,c_1262])).

tff(c_1326,plain,(
    ! [A_252] :
      ( ~ r2_hidden('#skF_7',A_252)
      | k4_xboole_0(A_252,'#skF_9') != A_252 ) ),
    inference(resolution,[status(thm)],[c_1230,c_1307])).

tff(c_1340,plain,(
    ! [B_13] : k4_xboole_0(k2_tarski('#skF_7',B_13),'#skF_9') != k2_tarski('#skF_7',B_13) ),
    inference(resolution,[status(thm)],[c_20,c_1326])).

tff(c_1367,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_58])).

tff(c_1368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1340,c_1367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.52  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 3.36/1.52  
% 3.36/1.52  %Foreground sorts:
% 3.36/1.52  
% 3.36/1.52  
% 3.36/1.52  %Background operators:
% 3.36/1.52  
% 3.36/1.52  
% 3.36/1.52  %Foreground operators:
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.36/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.52  tff('#skF_9', type, '#skF_9': $i).
% 3.36/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.36/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.52  
% 3.36/1.53  tff(f_60, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.36/1.53  tff(f_91, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.36/1.53  tff(f_82, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 3.36/1.53  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.36/1.53  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.36/1.53  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.36/1.53  tff(c_20, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.53  tff(c_52, plain, (~r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.36/1.53  tff(c_92, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 3.36/1.53  tff(c_50, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.36/1.53  tff(c_151, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 3.36/1.53  tff(c_210, plain, (![A_99, C_100, B_101]: (r1_xboole_0(k2_tarski(A_99, C_100), B_101) | r2_hidden(C_100, B_101) | r2_hidden(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.36/1.53  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.53  tff(c_497, plain, (![A_186, C_187, B_188]: (k4_xboole_0(k2_tarski(A_186, C_187), B_188)=k2_tarski(A_186, C_187) | r2_hidden(C_187, B_188) | r2_hidden(A_186, B_188))), inference(resolution, [status(thm)], [c_210, c_12])).
% 3.36/1.53  tff(c_48, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k2_tarski('#skF_4', '#skF_5') | r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.36/1.53  tff(c_238, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k2_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.36/1.53  tff(c_555, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_497, c_238])).
% 3.36/1.53  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_151, c_555])).
% 3.36/1.53  tff(c_604, plain, (r2_hidden('#skF_7', '#skF_9') | r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_48])).
% 3.36/1.53  tff(c_606, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_604])).
% 3.36/1.53  tff(c_18, plain, (![D_17, A_12]: (r2_hidden(D_17, k2_tarski(A_12, D_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.53  tff(c_605, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.36/1.53  tff(c_54, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k2_tarski('#skF_4', '#skF_5') | k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.36/1.53  tff(c_669, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_54])).
% 3.36/1.53  tff(c_10, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_144, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, B_75) | ~r2_hidden(C_76, A_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.53  tff(c_150, plain, (![C_76, B_9, A_8]: (~r2_hidden(C_76, B_9) | ~r2_hidden(C_76, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_10, c_144])).
% 3.36/1.53  tff(c_692, plain, (![C_191]: (~r2_hidden(C_191, '#skF_9') | ~r2_hidden(C_191, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_669, c_150])).
% 3.36/1.53  tff(c_704, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_18, c_692])).
% 3.36/1.53  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_606, c_704])).
% 3.36/1.53  tff(c_715, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_604])).
% 3.36/1.53  tff(c_758, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_54])).
% 3.36/1.53  tff(c_802, plain, (![C_194]: (~r2_hidden(C_194, '#skF_9') | ~r2_hidden(C_194, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_758, c_150])).
% 3.36/1.53  tff(c_818, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_20, c_802])).
% 3.36/1.53  tff(c_825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_715, c_818])).
% 3.36/1.53  tff(c_826, plain, (r2_hidden('#skF_7', '#skF_9') | r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_50])).
% 3.36/1.53  tff(c_828, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_826])).
% 3.36/1.53  tff(c_827, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 3.36/1.53  tff(c_56, plain, (~r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.36/1.53  tff(c_895, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_827, c_56])).
% 3.36/1.53  tff(c_918, plain, (![C_205]: (~r2_hidden(C_205, '#skF_9') | ~r2_hidden(C_205, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_895, c_150])).
% 3.36/1.53  tff(c_930, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_18, c_918])).
% 3.36/1.53  tff(c_940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_828, c_930])).
% 3.36/1.53  tff(c_941, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_826])).
% 3.36/1.53  tff(c_992, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_827, c_56])).
% 3.36/1.53  tff(c_1032, plain, (![C_214]: (~r2_hidden(C_214, '#skF_9') | ~r2_hidden(C_214, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_992, c_150])).
% 3.36/1.53  tff(c_1048, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_20, c_1032])).
% 3.36/1.53  tff(c_1055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_941, c_1048])).
% 3.36/1.53  tff(c_1056, plain, (r2_hidden('#skF_7', '#skF_9') | r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.53  tff(c_1058, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_1056])).
% 3.36/1.53  tff(c_1057, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.53  tff(c_58, plain, (~r2_hidden('#skF_4', '#skF_6') | k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.36/1.53  tff(c_1168, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_58])).
% 3.36/1.53  tff(c_1089, plain, (![A_220, B_221, C_222]: (~r1_xboole_0(A_220, B_221) | ~r2_hidden(C_222, B_221) | ~r2_hidden(C_222, A_220))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.53  tff(c_1095, plain, (![C_222, B_9, A_8]: (~r2_hidden(C_222, B_9) | ~r2_hidden(C_222, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_10, c_1089])).
% 3.36/1.53  tff(c_1207, plain, (![C_234]: (~r2_hidden(C_234, '#skF_9') | ~r2_hidden(C_234, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1168, c_1095])).
% 3.36/1.53  tff(c_1219, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_18, c_1207])).
% 3.36/1.53  tff(c_1229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1219])).
% 3.36/1.53  tff(c_1230, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_1056])).
% 3.36/1.53  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.53  tff(c_1262, plain, (![A_240, B_241, C_242]: (~r1_xboole_0(A_240, B_241) | ~r2_hidden(C_242, B_241) | ~r2_hidden(C_242, A_240))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.53  tff(c_1307, plain, (![C_249, B_250, A_251]: (~r2_hidden(C_249, B_250) | ~r2_hidden(C_249, A_251) | k4_xboole_0(A_251, B_250)!=A_251)), inference(resolution, [status(thm)], [c_14, c_1262])).
% 3.36/1.53  tff(c_1326, plain, (![A_252]: (~r2_hidden('#skF_7', A_252) | k4_xboole_0(A_252, '#skF_9')!=A_252)), inference(resolution, [status(thm)], [c_1230, c_1307])).
% 3.36/1.53  tff(c_1340, plain, (![B_13]: (k4_xboole_0(k2_tarski('#skF_7', B_13), '#skF_9')!=k2_tarski('#skF_7', B_13))), inference(resolution, [status(thm)], [c_20, c_1326])).
% 3.36/1.53  tff(c_1367, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_58])).
% 3.36/1.53  tff(c_1368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1340, c_1367])).
% 3.36/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  Inference rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Ref     : 0
% 3.36/1.53  #Sup     : 296
% 3.36/1.53  #Fact    : 0
% 3.36/1.53  #Define  : 0
% 3.36/1.53  #Split   : 8
% 3.36/1.53  #Chain   : 0
% 3.36/1.53  #Close   : 0
% 3.36/1.53  
% 3.36/1.53  Ordering : KBO
% 3.36/1.53  
% 3.36/1.53  Simplification rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Subsume      : 38
% 3.36/1.53  #Demod        : 70
% 3.36/1.53  #Tautology    : 89
% 3.36/1.53  #SimpNegUnit  : 5
% 3.36/1.53  #BackRed      : 0
% 3.36/1.53  
% 3.36/1.53  #Partial instantiations: 0
% 3.36/1.53  #Strategies tried      : 1
% 3.36/1.53  
% 3.36/1.53  Timing (in seconds)
% 3.36/1.53  ----------------------
% 3.36/1.53  Preprocessing        : 0.34
% 3.36/1.53  Parsing              : 0.18
% 3.36/1.53  CNF conversion       : 0.03
% 3.36/1.54  Main loop            : 0.42
% 3.36/1.54  Inferencing          : 0.16
% 3.36/1.54  Reduction            : 0.12
% 3.36/1.54  Demodulation         : 0.09
% 3.36/1.54  BG Simplification    : 0.03
% 3.36/1.54  Subsumption          : 0.08
% 3.36/1.54  Abstraction          : 0.03
% 3.36/1.54  MUC search           : 0.00
% 3.36/1.54  Cooper               : 0.00
% 3.36/1.54  Total                : 0.80
% 3.36/1.54  Index Insertion      : 0.00
% 3.36/1.54  Index Deletion       : 0.00
% 3.36/1.54  Index Matching       : 0.00
% 3.36/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
