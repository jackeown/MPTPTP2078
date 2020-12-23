%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:52 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 152 expanded)
%              Number of leaves         :   39 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :   65 ( 147 expanded)
%              Number of equality atoms :   45 ( 117 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_30,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_194,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_204,plain,(
    ! [A_18,C_80] :
      ( ~ r1_xboole_0(A_18,k1_xboole_0)
      | ~ r2_hidden(C_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_194])).

tff(c_207,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_204])).

tff(c_64,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_208,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_226,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_208])).

tff(c_236,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_34,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_244,plain,(
    ! [A_84] : k5_xboole_0(A_84,k1_xboole_0) = k2_xboole_0(A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_34])).

tff(c_257,plain,(
    ! [A_84] : k5_xboole_0(A_84,k1_xboole_0) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_244])).

tff(c_229,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_16,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_340,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_357,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_340])).

tff(c_363,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_357])).

tff(c_156,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k4_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_165,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,A_21) = k2_xboole_0(k1_xboole_0,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_156])).

tff(c_439,plain,(
    ! [A_104,B_105,C_106] : k5_xboole_0(k5_xboole_0(A_104,B_105),C_106) = k5_xboole_0(A_104,k5_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_470,plain,(
    ! [B_13,C_106] : k5_xboole_0(B_13,k5_xboole_0(B_13,C_106)) = k5_xboole_0(k1_xboole_0,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_439])).

tff(c_820,plain,(
    ! [B_123,C_124] : k5_xboole_0(B_123,k5_xboole_0(B_123,C_124)) = k2_xboole_0(k1_xboole_0,C_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_470])).

tff(c_880,plain,(
    ! [B_13] : k5_xboole_0(B_13,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_820])).

tff(c_913,plain,(
    ! [B_13] : k2_xboole_0(k1_xboole_0,B_13) = B_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_880])).

tff(c_504,plain,(
    ! [B_13,C_106] : k5_xboole_0(B_13,k5_xboole_0(B_13,C_106)) = k2_xboole_0(k1_xboole_0,C_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_470])).

tff(c_1042,plain,(
    ! [B_132,C_133] : k5_xboole_0(B_132,k5_xboole_0(B_132,C_133)) = C_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_504])).

tff(c_2028,plain,(
    ! [A_173,B_174] : k5_xboole_0(A_173,k2_xboole_0(A_173,B_174)) = k4_xboole_0(B_174,A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1042])).

tff(c_2077,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) = k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2028])).

tff(c_2089,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_2077])).

tff(c_24,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2162,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_5','#skF_6')) = k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_24])).

tff(c_2171,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_2162])).

tff(c_38,plain,(
    ! [D_35,A_30] : r2_hidden(D_35,k2_tarski(A_30,D_35)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2192,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_38])).

tff(c_2202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_2192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:43:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.63  
% 3.59/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 3.59/1.63  
% 3.59/1.63  %Foreground sorts:
% 3.59/1.63  
% 3.59/1.63  
% 3.59/1.63  %Background operators:
% 3.59/1.63  
% 3.59/1.63  
% 3.59/1.63  %Foreground operators:
% 3.59/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.59/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.59/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.59/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.59/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.59/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.59/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.59/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.59/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.59/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.59/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.59/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.59/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.59/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.63  
% 3.59/1.65  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.59/1.65  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.59/1.65  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.59/1.65  tff(f_96, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.59/1.65  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.59/1.65  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.59/1.65  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.59/1.65  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.59/1.65  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.59/1.65  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.59/1.65  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.59/1.65  tff(f_71, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.59/1.65  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.59/1.65  tff(f_82, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.59/1.65  tff(c_30, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.59/1.65  tff(c_22, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.65  tff(c_194, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.65  tff(c_204, plain, (![A_18, C_80]: (~r1_xboole_0(A_18, k1_xboole_0) | ~r2_hidden(C_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_194])).
% 3.59/1.65  tff(c_207, plain, (![C_80]: (~r2_hidden(C_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_204])).
% 3.59/1.65  tff(c_64, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.59/1.65  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.59/1.65  tff(c_26, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.59/1.65  tff(c_208, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.59/1.65  tff(c_226, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_208])).
% 3.59/1.65  tff(c_236, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 3.59/1.65  tff(c_34, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.65  tff(c_244, plain, (![A_84]: (k5_xboole_0(A_84, k1_xboole_0)=k2_xboole_0(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_236, c_34])).
% 3.59/1.65  tff(c_257, plain, (![A_84]: (k5_xboole_0(A_84, k1_xboole_0)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_244])).
% 3.59/1.65  tff(c_229, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 3.59/1.65  tff(c_16, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.59/1.65  tff(c_123, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=A_68 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.59/1.65  tff(c_127, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_16, c_123])).
% 3.59/1.65  tff(c_340, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.59/1.65  tff(c_357, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_127, c_340])).
% 3.59/1.65  tff(c_363, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_357])).
% 3.59/1.65  tff(c_156, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k4_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.65  tff(c_165, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, A_21)=k2_xboole_0(k1_xboole_0, A_21))), inference(superposition, [status(thm), theory('equality')], [c_26, c_156])).
% 3.59/1.65  tff(c_439, plain, (![A_104, B_105, C_106]: (k5_xboole_0(k5_xboole_0(A_104, B_105), C_106)=k5_xboole_0(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.59/1.65  tff(c_470, plain, (![B_13, C_106]: (k5_xboole_0(B_13, k5_xboole_0(B_13, C_106))=k5_xboole_0(k1_xboole_0, C_106))), inference(superposition, [status(thm), theory('equality')], [c_363, c_439])).
% 3.59/1.65  tff(c_820, plain, (![B_123, C_124]: (k5_xboole_0(B_123, k5_xboole_0(B_123, C_124))=k2_xboole_0(k1_xboole_0, C_124))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_470])).
% 3.59/1.65  tff(c_880, plain, (![B_13]: (k5_xboole_0(B_13, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_13))), inference(superposition, [status(thm), theory('equality')], [c_363, c_820])).
% 3.59/1.65  tff(c_913, plain, (![B_13]: (k2_xboole_0(k1_xboole_0, B_13)=B_13)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_880])).
% 3.59/1.65  tff(c_504, plain, (![B_13, C_106]: (k5_xboole_0(B_13, k5_xboole_0(B_13, C_106))=k2_xboole_0(k1_xboole_0, C_106))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_470])).
% 3.59/1.65  tff(c_1042, plain, (![B_132, C_133]: (k5_xboole_0(B_132, k5_xboole_0(B_132, C_133))=C_133)), inference(demodulation, [status(thm), theory('equality')], [c_913, c_504])).
% 3.59/1.65  tff(c_2028, plain, (![A_173, B_174]: (k5_xboole_0(A_173, k2_xboole_0(A_173, B_174))=k4_xboole_0(B_174, A_173))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1042])).
% 3.59/1.65  tff(c_2077, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)=k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2028])).
% 3.59/1.65  tff(c_2089, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_2077])).
% 3.59/1.65  tff(c_24, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.59/1.65  tff(c_2162, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_5', '#skF_6'))=k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2089, c_24])).
% 3.59/1.65  tff(c_2171, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_2162])).
% 3.59/1.65  tff(c_38, plain, (![D_35, A_30]: (r2_hidden(D_35, k2_tarski(A_30, D_35)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.59/1.65  tff(c_2192, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2171, c_38])).
% 3.59/1.65  tff(c_2202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_2192])).
% 3.59/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.65  
% 3.59/1.65  Inference rules
% 3.59/1.65  ----------------------
% 3.59/1.65  #Ref     : 0
% 3.59/1.65  #Sup     : 489
% 3.59/1.65  #Fact    : 2
% 3.59/1.65  #Define  : 0
% 3.59/1.65  #Split   : 0
% 3.59/1.65  #Chain   : 0
% 3.59/1.65  #Close   : 0
% 3.59/1.65  
% 3.59/1.65  Ordering : KBO
% 3.59/1.65  
% 3.59/1.65  Simplification rules
% 3.59/1.65  ----------------------
% 3.59/1.65  #Subsume      : 17
% 3.59/1.65  #Demod        : 372
% 3.59/1.65  #Tautology    : 350
% 3.59/1.65  #SimpNegUnit  : 7
% 3.59/1.65  #BackRed      : 11
% 3.59/1.65  
% 3.59/1.65  #Partial instantiations: 0
% 3.59/1.65  #Strategies tried      : 1
% 3.59/1.65  
% 3.59/1.65  Timing (in seconds)
% 3.59/1.65  ----------------------
% 3.59/1.65  Preprocessing        : 0.34
% 3.59/1.65  Parsing              : 0.18
% 3.59/1.65  CNF conversion       : 0.02
% 3.59/1.65  Main loop            : 0.48
% 3.59/1.65  Inferencing          : 0.17
% 3.59/1.65  Reduction            : 0.18
% 3.59/1.65  Demodulation         : 0.14
% 3.59/1.65  BG Simplification    : 0.03
% 3.59/1.65  Subsumption          : 0.07
% 3.59/1.65  Abstraction          : 0.03
% 3.59/1.65  MUC search           : 0.00
% 3.59/1.65  Cooper               : 0.00
% 3.59/1.65  Total                : 0.85
% 3.59/1.65  Index Insertion      : 0.00
% 3.59/1.65  Index Deletion       : 0.00
% 3.59/1.65  Index Matching       : 0.00
% 3.59/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
