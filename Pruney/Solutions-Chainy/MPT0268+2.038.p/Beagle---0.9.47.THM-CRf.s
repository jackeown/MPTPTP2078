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
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 154 expanded)
%              Number of leaves         :   37 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 166 expanded)
%              Number of equality atoms :   64 ( 118 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1568,plain,(
    ! [B_164,A_165] : k5_xboole_0(B_164,A_165) = k5_xboole_0(A_165,B_164) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1584,plain,(
    ! [A_165] : k5_xboole_0(k1_xboole_0,A_165) = A_165 ),
    inference(superposition,[status(thm),theory(equality)],[c_1568,c_14])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1903,plain,(
    ! [A_197,B_198] : k5_xboole_0(k5_xboole_0(A_197,B_198),k2_xboole_0(A_197,B_198)) = k3_xboole_0(A_197,B_198) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1942,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1903])).

tff(c_1953,plain,(
    ! [A_199] : k3_xboole_0(A_199,A_199) = A_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_20,c_1942])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1963,plain,(
    ! [A_199] : k5_xboole_0(A_199,A_199) = k4_xboole_0(A_199,A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_8])).

tff(c_1975,plain,(
    ! [A_199] : k4_xboole_0(A_199,A_199) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1963])).

tff(c_44,plain,(
    ! [B_58] : k4_xboole_0(k1_tarski(B_58),k1_tarski(B_58)) != k1_tarski(B_58) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1981,plain,(
    ! [B_58] : k1_tarski(B_58) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1975,c_44])).

tff(c_101,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_14])).

tff(c_1019,plain,(
    ! [A_123,B_124] : k5_xboole_0(k5_xboole_0(A_123,B_124),k2_xboole_0(A_123,B_124)) = k3_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1098,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1019])).

tff(c_1109,plain,(
    ! [A_125] : k3_xboole_0(A_125,A_125) = A_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_20,c_1098])).

tff(c_1119,plain,(
    ! [A_125] : k5_xboole_0(A_125,A_125) = k4_xboole_0(A_125,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_1109,c_8])).

tff(c_1131,plain,(
    ! [A_125] : k4_xboole_0(A_125,A_125) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1119])).

tff(c_1137,plain,(
    ! [B_58] : k1_tarski(B_58) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_44])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_201,plain,(
    ! [A_71,B_72] :
      ( r1_xboole_0(k1_tarski(A_71),B_72)
      | r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    ! [B_78,A_79] :
      ( r1_xboole_0(B_78,k1_tarski(A_79))
      | r2_hidden(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_201,c_6])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_301,plain,(
    ! [B_87,A_88] :
      ( k4_xboole_0(B_87,k1_tarski(A_88)) = B_87
      | r2_hidden(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_241,c_55])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_315,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_240])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_315])).

tff(c_336,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_337,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_338,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_338])).

tff(c_345,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_586,plain,(
    ! [A_112,B_113,C_114] : k5_xboole_0(k5_xboole_0(A_112,B_113),C_114) = k5_xboole_0(A_112,k5_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_650,plain,(
    ! [A_20,C_114] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_114)) = k5_xboole_0(k1_xboole_0,C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_586])).

tff(c_664,plain,(
    ! [A_115,C_116] : k5_xboole_0(A_115,k5_xboole_0(A_115,C_116)) = C_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_650])).

tff(c_1468,plain,(
    ! [A_160,B_161] : k5_xboole_0(A_160,k4_xboole_0(A_160,B_161)) = k3_xboole_0(A_160,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_664])).

tff(c_1528,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1468])).

tff(c_1546,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1528])).

tff(c_40,plain,(
    ! [B_54,A_53] :
      ( k3_xboole_0(B_54,k1_tarski(A_53)) = k1_tarski(A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1552,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1546,c_40])).

tff(c_1562,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_1552])).

tff(c_1564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1137,c_1562])).

tff(c_1565,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1566,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1669,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_54])).

tff(c_2141,plain,(
    ! [A_208,B_209,C_210] : k5_xboole_0(k5_xboole_0(A_208,B_209),C_210) = k5_xboole_0(A_208,k5_xboole_0(B_209,C_210)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2229,plain,(
    ! [A_20,C_210] : k5_xboole_0(A_20,k5_xboole_0(A_20,C_210)) = k5_xboole_0(k1_xboole_0,C_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2141])).

tff(c_2243,plain,(
    ! [A_211,C_212] : k5_xboole_0(A_211,k5_xboole_0(A_211,C_212)) = C_212 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_2229])).

tff(c_2746,plain,(
    ! [A_246,B_247] : k5_xboole_0(A_246,k4_xboole_0(A_246,B_247)) = k3_xboole_0(A_246,B_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2243])).

tff(c_2806,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_2746])).

tff(c_2821,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2806])).

tff(c_2826,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2821,c_40])).

tff(c_2836,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_2826])).

tff(c_2838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1981,c_2836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:34:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.59  
% 3.73/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.59  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.73/1.59  
% 3.73/1.59  %Foreground sorts:
% 3.73/1.59  
% 3.73/1.59  
% 3.73/1.59  %Background operators:
% 3.73/1.59  
% 3.73/1.59  
% 3.73/1.59  %Foreground operators:
% 3.73/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.73/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.73/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.59  
% 3.73/1.61  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.73/1.61  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.73/1.61  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.73/1.61  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.73/1.61  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.73/1.61  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.73/1.61  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.73/1.61  tff(f_87, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.73/1.61  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.73/1.61  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.73/1.61  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.73/1.61  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.73/1.61  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.73/1.61  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.73/1.61  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.73/1.61  tff(c_1568, plain, (![B_164, A_165]: (k5_xboole_0(B_164, A_165)=k5_xboole_0(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.61  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.61  tff(c_1584, plain, (![A_165]: (k5_xboole_0(k1_xboole_0, A_165)=A_165)), inference(superposition, [status(thm), theory('equality')], [c_1568, c_14])).
% 3.73/1.61  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.61  tff(c_1903, plain, (![A_197, B_198]: (k5_xboole_0(k5_xboole_0(A_197, B_198), k2_xboole_0(A_197, B_198))=k3_xboole_0(A_197, B_198))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.73/1.61  tff(c_1942, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1903])).
% 3.73/1.61  tff(c_1953, plain, (![A_199]: (k3_xboole_0(A_199, A_199)=A_199)), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_20, c_1942])).
% 3.73/1.61  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.61  tff(c_1963, plain, (![A_199]: (k5_xboole_0(A_199, A_199)=k4_xboole_0(A_199, A_199))), inference(superposition, [status(thm), theory('equality')], [c_1953, c_8])).
% 3.73/1.61  tff(c_1975, plain, (![A_199]: (k4_xboole_0(A_199, A_199)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1963])).
% 3.73/1.61  tff(c_44, plain, (![B_58]: (k4_xboole_0(k1_tarski(B_58), k1_tarski(B_58))!=k1_tarski(B_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.73/1.61  tff(c_1981, plain, (![B_58]: (k1_tarski(B_58)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1975, c_44])).
% 3.73/1.61  tff(c_101, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.61  tff(c_117, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_101, c_14])).
% 3.73/1.61  tff(c_1019, plain, (![A_123, B_124]: (k5_xboole_0(k5_xboole_0(A_123, B_124), k2_xboole_0(A_123, B_124))=k3_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.73/1.61  tff(c_1098, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1019])).
% 3.73/1.61  tff(c_1109, plain, (![A_125]: (k3_xboole_0(A_125, A_125)=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_20, c_1098])).
% 3.73/1.61  tff(c_1119, plain, (![A_125]: (k5_xboole_0(A_125, A_125)=k4_xboole_0(A_125, A_125))), inference(superposition, [status(thm), theory('equality')], [c_1109, c_8])).
% 3.73/1.61  tff(c_1131, plain, (![A_125]: (k4_xboole_0(A_125, A_125)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1119])).
% 3.73/1.61  tff(c_1137, plain, (![B_58]: (k1_tarski(B_58)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_44])).
% 3.73/1.61  tff(c_50, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.73/1.61  tff(c_100, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 3.73/1.61  tff(c_201, plain, (![A_71, B_72]: (r1_xboole_0(k1_tarski(A_71), B_72) | r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.73/1.61  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.73/1.61  tff(c_241, plain, (![B_78, A_79]: (r1_xboole_0(B_78, k1_tarski(A_79)) | r2_hidden(A_79, B_78))), inference(resolution, [status(thm)], [c_201, c_6])).
% 3.73/1.61  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.73/1.61  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.73/1.61  tff(c_55, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 3.73/1.61  tff(c_301, plain, (![B_87, A_88]: (k4_xboole_0(B_87, k1_tarski(A_88))=B_87 | r2_hidden(A_88, B_87))), inference(resolution, [status(thm)], [c_241, c_55])).
% 3.73/1.61  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.73/1.61  tff(c_240, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_48])).
% 3.73/1.61  tff(c_315, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_301, c_240])).
% 3.73/1.61  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_315])).
% 3.73/1.61  tff(c_336, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.73/1.61  tff(c_337, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 3.73/1.61  tff(c_52, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.73/1.61  tff(c_338, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_52])).
% 3.73/1.61  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_337, c_338])).
% 3.73/1.61  tff(c_345, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 3.73/1.61  tff(c_586, plain, (![A_112, B_113, C_114]: (k5_xboole_0(k5_xboole_0(A_112, B_113), C_114)=k5_xboole_0(A_112, k5_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.61  tff(c_650, plain, (![A_20, C_114]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_114))=k5_xboole_0(k1_xboole_0, C_114))), inference(superposition, [status(thm), theory('equality')], [c_20, c_586])).
% 3.73/1.61  tff(c_664, plain, (![A_115, C_116]: (k5_xboole_0(A_115, k5_xboole_0(A_115, C_116))=C_116)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_650])).
% 3.73/1.61  tff(c_1468, plain, (![A_160, B_161]: (k5_xboole_0(A_160, k4_xboole_0(A_160, B_161))=k3_xboole_0(A_160, B_161))), inference(superposition, [status(thm), theory('equality')], [c_8, c_664])).
% 3.73/1.61  tff(c_1528, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_345, c_1468])).
% 3.73/1.61  tff(c_1546, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1528])).
% 3.73/1.61  tff(c_40, plain, (![B_54, A_53]: (k3_xboole_0(B_54, k1_tarski(A_53))=k1_tarski(A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.73/1.61  tff(c_1552, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1546, c_40])).
% 3.73/1.61  tff(c_1562, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_336, c_1552])).
% 3.73/1.61  tff(c_1564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1137, c_1562])).
% 3.73/1.61  tff(c_1565, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.73/1.61  tff(c_1566, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.73/1.61  tff(c_54, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.73/1.61  tff(c_1669, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_54])).
% 3.73/1.61  tff(c_2141, plain, (![A_208, B_209, C_210]: (k5_xboole_0(k5_xboole_0(A_208, B_209), C_210)=k5_xboole_0(A_208, k5_xboole_0(B_209, C_210)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.61  tff(c_2229, plain, (![A_20, C_210]: (k5_xboole_0(A_20, k5_xboole_0(A_20, C_210))=k5_xboole_0(k1_xboole_0, C_210))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2141])).
% 3.73/1.61  tff(c_2243, plain, (![A_211, C_212]: (k5_xboole_0(A_211, k5_xboole_0(A_211, C_212))=C_212)), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_2229])).
% 3.73/1.61  tff(c_2746, plain, (![A_246, B_247]: (k5_xboole_0(A_246, k4_xboole_0(A_246, B_247))=k3_xboole_0(A_246, B_247))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2243])).
% 3.73/1.61  tff(c_2806, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1669, c_2746])).
% 3.73/1.61  tff(c_2821, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2806])).
% 3.73/1.61  tff(c_2826, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2821, c_40])).
% 3.73/1.61  tff(c_2836, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_2826])).
% 3.73/1.61  tff(c_2838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1981, c_2836])).
% 3.73/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.61  
% 3.73/1.61  Inference rules
% 3.73/1.61  ----------------------
% 3.73/1.61  #Ref     : 0
% 3.73/1.61  #Sup     : 672
% 3.73/1.61  #Fact    : 0
% 3.73/1.61  #Define  : 0
% 3.73/1.61  #Split   : 3
% 3.73/1.61  #Chain   : 0
% 3.73/1.61  #Close   : 0
% 3.73/1.61  
% 3.73/1.61  Ordering : KBO
% 3.73/1.61  
% 3.73/1.61  Simplification rules
% 3.73/1.61  ----------------------
% 3.73/1.61  #Subsume      : 16
% 3.73/1.61  #Demod        : 317
% 3.73/1.61  #Tautology    : 436
% 3.73/1.61  #SimpNegUnit  : 9
% 3.73/1.61  #BackRed      : 2
% 3.73/1.61  
% 3.73/1.61  #Partial instantiations: 0
% 3.73/1.61  #Strategies tried      : 1
% 3.73/1.61  
% 3.73/1.61  Timing (in seconds)
% 3.73/1.61  ----------------------
% 3.73/1.61  Preprocessing        : 0.31
% 3.73/1.61  Parsing              : 0.16
% 3.73/1.61  CNF conversion       : 0.02
% 3.73/1.61  Main loop            : 0.54
% 3.73/1.61  Inferencing          : 0.20
% 3.73/1.61  Reduction            : 0.21
% 3.73/1.61  Demodulation         : 0.16
% 3.73/1.61  BG Simplification    : 0.03
% 3.73/1.61  Subsumption          : 0.07
% 3.73/1.61  Abstraction          : 0.03
% 3.73/1.61  MUC search           : 0.00
% 3.73/1.61  Cooper               : 0.00
% 3.73/1.61  Total                : 0.89
% 3.73/1.61  Index Insertion      : 0.00
% 3.73/1.61  Index Deletion       : 0.00
% 3.73/1.61  Index Matching       : 0.00
% 3.73/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
