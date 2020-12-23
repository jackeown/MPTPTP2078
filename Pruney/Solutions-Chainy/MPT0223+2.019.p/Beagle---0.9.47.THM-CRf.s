%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:19 EST 2020

% Result     : Theorem 10.77s
% Output     : CNFRefutation 10.92s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 196 expanded)
%              Number of equality atoms :   40 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_78,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    ! [C_33] : r2_hidden(C_33,k1_tarski(C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_266,plain,(
    ! [A_85,B_86] :
      ( k2_xboole_0(k1_tarski(A_85),B_86) = B_86
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1053,plain,(
    ! [A_153,B_154] :
      ( k3_xboole_0(k1_tarski(A_153),B_154) = k1_tarski(A_153)
      | ~ r2_hidden(A_153,B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_28])).

tff(c_429,plain,(
    ! [A_110,B_111,C_112] : k3_xboole_0(k3_xboole_0(A_110,B_111),C_112) = k3_xboole_0(A_110,k3_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_480,plain,(
    ! [C_112] : k3_xboole_0(k1_tarski('#skF_6'),k3_xboole_0(k1_tarski('#skF_7'),C_112)) = k3_xboole_0(k1_tarski('#skF_6'),C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_429])).

tff(c_1062,plain,(
    ! [B_154] :
      ( k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k3_xboole_0(k1_tarski('#skF_6'),B_154)
      | ~ r2_hidden('#skF_7',B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_480])).

tff(c_1149,plain,(
    ! [B_158] :
      ( k3_xboole_0(k1_tarski('#skF_6'),B_158) = k1_tarski('#skF_6')
      | ~ r2_hidden('#skF_7',B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1062])).

tff(c_1224,plain,(
    ! [A_1] :
      ( k3_xboole_0(A_1,k1_tarski('#skF_6')) = k1_tarski('#skF_6')
      | ~ r2_hidden('#skF_7',A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1149])).

tff(c_15585,plain,(
    ! [C_25520] :
      ( k3_xboole_0(k1_tarski('#skF_6'),C_25520) = k1_tarski('#skF_6')
      | ~ r2_hidden('#skF_6',k3_xboole_0(k1_tarski('#skF_7'),C_25520)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_480])).

tff(c_15669,plain,
    ( k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6')
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_15585])).

tff(c_15697,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_15669])).

tff(c_13657,plain,(
    ! [A_22987,B_22988,C_22989] : k3_xboole_0(k3_xboole_0(A_22987,B_22988),C_22989) = k3_xboole_0(B_22988,k3_xboole_0(A_22987,C_22989)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_429])).

tff(c_14050,plain,(
    ! [C_23286] : k3_xboole_0(k1_tarski('#skF_7'),k3_xboole_0(k1_tarski('#skF_6'),C_23286)) = k3_xboole_0(k1_tarski('#skF_6'),C_23286) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_13657])).

tff(c_14290,plain,(
    ! [B_2] : k3_xboole_0(k1_tarski('#skF_7'),k3_xboole_0(B_2,k1_tarski('#skF_6'))) = k3_xboole_0(k1_tarski('#skF_6'),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14050])).

tff(c_15705,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_6')) = k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15697,c_14290])).

tff(c_15863,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15697,c_15705])).

tff(c_24,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1660,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden(A_179,B_180)
      | ~ r2_hidden(A_179,C_181)
      | r2_hidden(A_179,k5_xboole_0(B_180,C_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19742,plain,(
    ! [A_30153,A_30154,B_30155] :
      ( r2_hidden(A_30153,A_30154)
      | ~ r2_hidden(A_30153,k3_xboole_0(A_30154,B_30155))
      | r2_hidden(A_30153,k4_xboole_0(A_30154,B_30155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1660])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_373,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,k2_xboole_0(A_96,B_97))
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_217])).

tff(c_378,plain,(
    ! [C_98,A_3,B_97] :
      ( ~ r2_hidden(C_98,A_3)
      | k3_xboole_0(A_3,k2_xboole_0(A_3,B_97)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_391,plain,(
    ! [C_102,A_103] :
      ( ~ r2_hidden(C_102,A_103)
      | k1_xboole_0 != A_103 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_378])).

tff(c_415,plain,(
    ! [C_33] : k1_tarski(C_33) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_391])).

tff(c_30,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_73,B_74] : k3_xboole_0(k4_xboole_0(A_73,B_74),B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_176])).

tff(c_186,plain,(
    ! [B_74,A_73] : k3_xboole_0(B_74,k4_xboole_0(A_73,B_74)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_2])).

tff(c_1087,plain,(
    ! [A_153,A_73] :
      ( k1_tarski(A_153) = k1_xboole_0
      | ~ r2_hidden(A_153,k4_xboole_0(A_73,k1_tarski(A_153))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_186])).

tff(c_1128,plain,(
    ! [A_153,A_73] : ~ r2_hidden(A_153,k4_xboole_0(A_73,k1_tarski(A_153))) ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_1087])).

tff(c_19894,plain,(
    ! [A_30453,A_30454] :
      ( r2_hidden(A_30453,A_30454)
      | ~ r2_hidden(A_30453,k3_xboole_0(A_30454,k1_tarski(A_30453))) ) ),
    inference(resolution,[status(thm)],[c_19742,c_1128])).

tff(c_19897,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15863,c_19894])).

tff(c_19962,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_19897])).

tff(c_56,plain,(
    ! [C_33,A_29] :
      ( C_33 = A_29
      | ~ r2_hidden(C_33,k1_tarski(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_19982,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_19962,c_56])).

tff(c_20023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_19982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.77/4.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.77/4.43  
% 10.77/4.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.77/4.44  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 10.77/4.44  
% 10.77/4.44  %Foreground sorts:
% 10.77/4.44  
% 10.77/4.44  
% 10.77/4.44  %Background operators:
% 10.77/4.44  
% 10.77/4.44  
% 10.77/4.44  %Foreground operators:
% 10.77/4.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.77/4.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.77/4.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.77/4.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.77/4.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.77/4.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.77/4.44  tff('#skF_7', type, '#skF_7': $i).
% 10.77/4.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.77/4.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.77/4.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.77/4.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.77/4.44  tff('#skF_6', type, '#skF_6': $i).
% 10.77/4.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.77/4.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.77/4.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.77/4.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.77/4.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.77/4.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.77/4.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.77/4.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.77/4.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.77/4.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.77/4.44  
% 10.92/4.45  tff(f_99, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 10.92/4.45  tff(f_82, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 10.92/4.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.92/4.45  tff(f_94, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 10.92/4.45  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 10.92/4.45  tff(f_56, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 10.92/4.45  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.92/4.45  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 10.92/4.45  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.92/4.45  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.92/4.45  tff(f_60, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.92/4.45  tff(c_78, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.92/4.45  tff(c_58, plain, (![C_33]: (r2_hidden(C_33, k1_tarski(C_33)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.92/4.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.92/4.45  tff(c_80, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.92/4.45  tff(c_266, plain, (![A_85, B_86]: (k2_xboole_0(k1_tarski(A_85), B_86)=B_86 | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.92/4.45  tff(c_28, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.92/4.45  tff(c_1053, plain, (![A_153, B_154]: (k3_xboole_0(k1_tarski(A_153), B_154)=k1_tarski(A_153) | ~r2_hidden(A_153, B_154))), inference(superposition, [status(thm), theory('equality')], [c_266, c_28])).
% 10.92/4.45  tff(c_429, plain, (![A_110, B_111, C_112]: (k3_xboole_0(k3_xboole_0(A_110, B_111), C_112)=k3_xboole_0(A_110, k3_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.92/4.45  tff(c_480, plain, (![C_112]: (k3_xboole_0(k1_tarski('#skF_6'), k3_xboole_0(k1_tarski('#skF_7'), C_112))=k3_xboole_0(k1_tarski('#skF_6'), C_112))), inference(superposition, [status(thm), theory('equality')], [c_80, c_429])).
% 10.92/4.45  tff(c_1062, plain, (![B_154]: (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k3_xboole_0(k1_tarski('#skF_6'), B_154) | ~r2_hidden('#skF_7', B_154))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_480])).
% 10.92/4.45  tff(c_1149, plain, (![B_158]: (k3_xboole_0(k1_tarski('#skF_6'), B_158)=k1_tarski('#skF_6') | ~r2_hidden('#skF_7', B_158))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1062])).
% 10.92/4.45  tff(c_1224, plain, (![A_1]: (k3_xboole_0(A_1, k1_tarski('#skF_6'))=k1_tarski('#skF_6') | ~r2_hidden('#skF_7', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1149])).
% 10.92/4.45  tff(c_15585, plain, (![C_25520]: (k3_xboole_0(k1_tarski('#skF_6'), C_25520)=k1_tarski('#skF_6') | ~r2_hidden('#skF_6', k3_xboole_0(k1_tarski('#skF_7'), C_25520)))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_480])).
% 10.92/4.45  tff(c_15669, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6') | ~r2_hidden('#skF_6', k1_tarski('#skF_6')) | ~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1224, c_15585])).
% 10.92/4.45  tff(c_15697, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_15669])).
% 10.92/4.45  tff(c_13657, plain, (![A_22987, B_22988, C_22989]: (k3_xboole_0(k3_xboole_0(A_22987, B_22988), C_22989)=k3_xboole_0(B_22988, k3_xboole_0(A_22987, C_22989)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_429])).
% 10.92/4.45  tff(c_14050, plain, (![C_23286]: (k3_xboole_0(k1_tarski('#skF_7'), k3_xboole_0(k1_tarski('#skF_6'), C_23286))=k3_xboole_0(k1_tarski('#skF_6'), C_23286))), inference(superposition, [status(thm), theory('equality')], [c_80, c_13657])).
% 10.92/4.45  tff(c_14290, plain, (![B_2]: (k3_xboole_0(k1_tarski('#skF_7'), k3_xboole_0(B_2, k1_tarski('#skF_6')))=k3_xboole_0(k1_tarski('#skF_6'), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14050])).
% 10.92/4.45  tff(c_15705, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_6'))=k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15697, c_14290])).
% 10.92/4.45  tff(c_15863, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_15697, c_15705])).
% 10.92/4.45  tff(c_24, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.92/4.45  tff(c_1660, plain, (![A_179, B_180, C_181]: (r2_hidden(A_179, B_180) | ~r2_hidden(A_179, C_181) | r2_hidden(A_179, k5_xboole_0(B_180, C_181)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.92/4.45  tff(c_19742, plain, (![A_30153, A_30154, B_30155]: (r2_hidden(A_30153, A_30154) | ~r2_hidden(A_30153, k3_xboole_0(A_30154, B_30155)) | r2_hidden(A_30153, k4_xboole_0(A_30154, B_30155)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1660])).
% 10.92/4.45  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.92/4.45  tff(c_217, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.92/4.45  tff(c_373, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, k2_xboole_0(A_96, B_97)) | ~r2_hidden(C_98, A_96))), inference(superposition, [status(thm), theory('equality')], [c_28, c_217])).
% 10.92/4.45  tff(c_378, plain, (![C_98, A_3, B_97]: (~r2_hidden(C_98, A_3) | k3_xboole_0(A_3, k2_xboole_0(A_3, B_97))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_373])).
% 10.92/4.45  tff(c_391, plain, (![C_102, A_103]: (~r2_hidden(C_102, A_103) | k1_xboole_0!=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_378])).
% 10.92/4.45  tff(c_415, plain, (![C_33]: (k1_tarski(C_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_391])).
% 10.92/4.45  tff(c_30, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.92/4.45  tff(c_176, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.92/4.45  tff(c_181, plain, (![A_73, B_74]: (k3_xboole_0(k4_xboole_0(A_73, B_74), B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_176])).
% 10.92/4.45  tff(c_186, plain, (![B_74, A_73]: (k3_xboole_0(B_74, k4_xboole_0(A_73, B_74))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_181, c_2])).
% 10.92/4.45  tff(c_1087, plain, (![A_153, A_73]: (k1_tarski(A_153)=k1_xboole_0 | ~r2_hidden(A_153, k4_xboole_0(A_73, k1_tarski(A_153))))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_186])).
% 10.92/4.45  tff(c_1128, plain, (![A_153, A_73]: (~r2_hidden(A_153, k4_xboole_0(A_73, k1_tarski(A_153))))), inference(negUnitSimplification, [status(thm)], [c_415, c_1087])).
% 10.92/4.45  tff(c_19894, plain, (![A_30453, A_30454]: (r2_hidden(A_30453, A_30454) | ~r2_hidden(A_30453, k3_xboole_0(A_30454, k1_tarski(A_30453))))), inference(resolution, [status(thm)], [c_19742, c_1128])).
% 10.92/4.45  tff(c_19897, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7')) | ~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15863, c_19894])).
% 10.92/4.45  tff(c_19962, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_19897])).
% 10.92/4.45  tff(c_56, plain, (![C_33, A_29]: (C_33=A_29 | ~r2_hidden(C_33, k1_tarski(A_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.92/4.45  tff(c_19982, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_19962, c_56])).
% 10.92/4.45  tff(c_20023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_19982])).
% 10.92/4.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.92/4.45  
% 10.92/4.45  Inference rules
% 10.92/4.45  ----------------------
% 10.92/4.45  #Ref     : 0
% 10.92/4.45  #Sup     : 3160
% 10.92/4.45  #Fact    : 18
% 10.92/4.45  #Define  : 0
% 10.92/4.45  #Split   : 5
% 10.92/4.45  #Chain   : 0
% 10.92/4.45  #Close   : 0
% 10.92/4.45  
% 10.92/4.45  Ordering : KBO
% 10.92/4.45  
% 10.92/4.45  Simplification rules
% 10.92/4.45  ----------------------
% 10.92/4.45  #Subsume      : 530
% 10.92/4.45  #Demod        : 1763
% 10.92/4.45  #Tautology    : 1048
% 10.92/4.45  #SimpNegUnit  : 136
% 10.92/4.45  #BackRed      : 2
% 10.92/4.45  
% 10.92/4.45  #Partial instantiations: 13940
% 10.92/4.45  #Strategies tried      : 1
% 10.92/4.45  
% 10.92/4.45  Timing (in seconds)
% 10.92/4.45  ----------------------
% 10.92/4.45  Preprocessing        : 0.56
% 10.92/4.45  Parsing              : 0.27
% 10.92/4.45  CNF conversion       : 0.05
% 10.92/4.45  Main loop            : 2.97
% 10.92/4.45  Inferencing          : 1.10
% 10.92/4.45  Reduction            : 1.24
% 10.92/4.45  Demodulation         : 1.04
% 10.92/4.45  BG Simplification    : 0.09
% 10.92/4.45  Subsumption          : 0.40
% 10.92/4.45  Abstraction          : 0.10
% 10.92/4.45  MUC search           : 0.00
% 10.92/4.45  Cooper               : 0.00
% 10.92/4.45  Total                : 3.56
% 10.92/4.45  Index Insertion      : 0.00
% 10.92/4.45  Index Deletion       : 0.00
% 10.92/4.45  Index Matching       : 0.00
% 10.92/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
