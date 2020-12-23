%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:05 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :   79 ( 140 expanded)
%              Number of equality atoms :   37 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_80,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_135,plain,(
    ! [A_48,B_49] : k1_enumset1(A_48,A_48,B_49) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [E_25,A_19,B_20] : r2_hidden(E_25,k1_enumset1(A_19,B_20,E_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,(
    ! [B_53,A_54] : r2_hidden(B_53,k2_tarski(A_54,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_46])).

tff(c_157,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_154])).

tff(c_22,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,k4_xboole_0(A_9,B_10))
      | r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_685,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_3'(A_113,B_114,C_115),A_113)
      | r2_hidden('#skF_4'(A_113,B_114,C_115),C_115)
      | k4_xboole_0(A_113,B_114) = C_115 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),B_10)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_952,plain,(
    ! [A_126,C_127] :
      ( r2_hidden('#skF_4'(A_126,A_126,C_127),C_127)
      | k4_xboole_0(A_126,A_126) = C_127 ) ),
    inference(resolution,[status(thm)],[c_685,c_36])).

tff(c_176,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_xboole_0
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_252,plain,(
    ! [D_79,B_80,A_81] :
      ( ~ r2_hidden(D_79,B_80)
      | ~ r2_hidden(D_79,k1_xboole_0)
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_24])).

tff(c_299,plain,(
    ! [A_85,A_86] :
      ( ~ r2_hidden(A_85,k1_xboole_0)
      | ~ r2_hidden(A_86,k1_tarski(A_85)) ) ),
    inference(resolution,[status(thm)],[c_157,c_252])).

tff(c_303,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_157,c_299])).

tff(c_983,plain,(
    ! [A_126] : k4_xboole_0(A_126,A_126) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_952,c_303])).

tff(c_40,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_206,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_421,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k3_xboole_0(A_101,k4_xboole_0(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_206])).

tff(c_457,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k4_xboole_0(A_15,k2_xboole_0(A_15,B_16))) = k4_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_421])).

tff(c_990,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k4_xboole_0(A_15,k2_xboole_0(A_15,B_16))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_457])).

tff(c_74,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | k4_xboole_0(k1_tarski(A_32),B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2072,plain,(
    ! [A_175,B_176] :
      ( r2_hidden(A_175,k4_xboole_0(k1_tarski(A_175),B_176))
      | k3_xboole_0(k1_tarski(A_175),B_176) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_74])).

tff(c_2167,plain,(
    ! [A_182,B_183] :
      ( ~ r2_hidden(A_182,B_183)
      | k3_xboole_0(k1_tarski(A_182),B_183) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2072,c_24])).

tff(c_2273,plain,(
    ! [A_189,B_190] : ~ r2_hidden(A_189,k4_xboole_0(k1_tarski(A_189),k2_xboole_0(k1_tarski(A_189),B_190))) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_2167])).

tff(c_2281,plain,(
    ! [D_14,B_190] :
      ( r2_hidden(D_14,k2_xboole_0(k1_tarski(D_14),B_190))
      | ~ r2_hidden(D_14,k1_tarski(D_14)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2273])).

tff(c_2290,plain,(
    ! [D_14,B_190] : r2_hidden(D_14,k2_xboole_0(k1_tarski(D_14),B_190)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_2281])).

tff(c_76,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(k1_tarski(A_32),B_33) = k1_xboole_0
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2663,plain,(
    ! [A_210,B_211] :
      ( k4_xboole_0(k1_tarski(A_210),k1_xboole_0) = k3_xboole_0(k1_tarski(A_210),B_211)
      | ~ r2_hidden(A_210,B_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_206])).

tff(c_2763,plain,(
    ! [A_210,B_16] :
      ( k4_xboole_0(k1_tarski(A_210),k1_xboole_0) = k1_tarski(A_210)
      | ~ r2_hidden(A_210,k2_xboole_0(k1_tarski(A_210),B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2663,c_40])).

tff(c_2835,plain,(
    ! [A_210] : k4_xboole_0(k1_tarski(A_210),k1_xboole_0) = k1_tarski(A_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2290,c_2763])).

tff(c_235,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(k1_tarski(A_32),k1_xboole_0) = k3_xboole_0(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_206])).

tff(c_2994,plain,(
    ! [A_218,B_219] :
      ( k3_xboole_0(k1_tarski(A_218),B_219) = k1_tarski(A_218)
      | ~ r2_hidden(A_218,B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_235])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3203,plain,(
    ! [B_225,A_226] :
      ( k3_xboole_0(B_225,k1_tarski(A_226)) = k1_tarski(A_226)
      | ~ r2_hidden(A_226,B_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2994,c_2])).

tff(c_78,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_7')) != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3268,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3203,c_78])).

tff(c_3307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.76  
% 4.03/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.76  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3
% 4.03/1.76  
% 4.03/1.76  %Foreground sorts:
% 4.03/1.76  
% 4.03/1.76  
% 4.03/1.76  %Background operators:
% 4.03/1.76  
% 4.03/1.76  
% 4.03/1.76  %Foreground operators:
% 4.03/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.03/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.03/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.03/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.03/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.03/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.03/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.03/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.03/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.03/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.03/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.03/1.76  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.03/1.76  tff('#skF_8', type, '#skF_8': $i).
% 4.03/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.76  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.03/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.03/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.03/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.03/1.76  
% 4.41/1.77  tff(f_80, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 4.41/1.77  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.41/1.77  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.41/1.77  tff(f_65, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.41/1.77  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.41/1.77  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 4.41/1.77  tff(f_48, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.41/1.77  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.41/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.41/1.77  tff(c_80, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.41/1.77  tff(c_68, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.41/1.77  tff(c_135, plain, (![A_48, B_49]: (k1_enumset1(A_48, A_48, B_49)=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.41/1.77  tff(c_46, plain, (![E_25, A_19, B_20]: (r2_hidden(E_25, k1_enumset1(A_19, B_20, E_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.41/1.77  tff(c_154, plain, (![B_53, A_54]: (r2_hidden(B_53, k2_tarski(A_54, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_46])).
% 4.41/1.77  tff(c_157, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_154])).
% 4.41/1.77  tff(c_22, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, k4_xboole_0(A_9, B_10)) | r2_hidden(D_14, B_10) | ~r2_hidden(D_14, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.41/1.77  tff(c_685, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_3'(A_113, B_114, C_115), A_113) | r2_hidden('#skF_4'(A_113, B_114, C_115), C_115) | k4_xboole_0(A_113, B_114)=C_115)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.41/1.77  tff(c_36, plain, (![A_9, B_10, C_11]: (~r2_hidden('#skF_3'(A_9, B_10, C_11), B_10) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.41/1.77  tff(c_952, plain, (![A_126, C_127]: (r2_hidden('#skF_4'(A_126, A_126, C_127), C_127) | k4_xboole_0(A_126, A_126)=C_127)), inference(resolution, [status(thm)], [c_685, c_36])).
% 4.41/1.77  tff(c_176, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_xboole_0 | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.41/1.77  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.41/1.77  tff(c_252, plain, (![D_79, B_80, A_81]: (~r2_hidden(D_79, B_80) | ~r2_hidden(D_79, k1_xboole_0) | ~r2_hidden(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_176, c_24])).
% 4.41/1.77  tff(c_299, plain, (![A_85, A_86]: (~r2_hidden(A_85, k1_xboole_0) | ~r2_hidden(A_86, k1_tarski(A_85)))), inference(resolution, [status(thm)], [c_157, c_252])).
% 4.41/1.77  tff(c_303, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_157, c_299])).
% 4.41/1.77  tff(c_983, plain, (![A_126]: (k4_xboole_0(A_126, A_126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_952, c_303])).
% 4.41/1.77  tff(c_40, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.41/1.77  tff(c_42, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.41/1.77  tff(c_206, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.41/1.77  tff(c_421, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k3_xboole_0(A_101, k4_xboole_0(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_206])).
% 4.41/1.77  tff(c_457, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k4_xboole_0(A_15, k2_xboole_0(A_15, B_16)))=k4_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_40, c_421])).
% 4.41/1.77  tff(c_990, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k4_xboole_0(A_15, k2_xboole_0(A_15, B_16)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_983, c_457])).
% 4.41/1.77  tff(c_74, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | k4_xboole_0(k1_tarski(A_32), B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.41/1.77  tff(c_2072, plain, (![A_175, B_176]: (r2_hidden(A_175, k4_xboole_0(k1_tarski(A_175), B_176)) | k3_xboole_0(k1_tarski(A_175), B_176)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_74])).
% 4.41/1.77  tff(c_2167, plain, (![A_182, B_183]: (~r2_hidden(A_182, B_183) | k3_xboole_0(k1_tarski(A_182), B_183)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2072, c_24])).
% 4.41/1.77  tff(c_2273, plain, (![A_189, B_190]: (~r2_hidden(A_189, k4_xboole_0(k1_tarski(A_189), k2_xboole_0(k1_tarski(A_189), B_190))))), inference(superposition, [status(thm), theory('equality')], [c_990, c_2167])).
% 4.41/1.77  tff(c_2281, plain, (![D_14, B_190]: (r2_hidden(D_14, k2_xboole_0(k1_tarski(D_14), B_190)) | ~r2_hidden(D_14, k1_tarski(D_14)))), inference(resolution, [status(thm)], [c_22, c_2273])).
% 4.41/1.77  tff(c_2290, plain, (![D_14, B_190]: (r2_hidden(D_14, k2_xboole_0(k1_tarski(D_14), B_190)))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_2281])).
% 4.41/1.77  tff(c_76, plain, (![A_32, B_33]: (k4_xboole_0(k1_tarski(A_32), B_33)=k1_xboole_0 | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.41/1.77  tff(c_2663, plain, (![A_210, B_211]: (k4_xboole_0(k1_tarski(A_210), k1_xboole_0)=k3_xboole_0(k1_tarski(A_210), B_211) | ~r2_hidden(A_210, B_211))), inference(superposition, [status(thm), theory('equality')], [c_76, c_206])).
% 4.41/1.77  tff(c_2763, plain, (![A_210, B_16]: (k4_xboole_0(k1_tarski(A_210), k1_xboole_0)=k1_tarski(A_210) | ~r2_hidden(A_210, k2_xboole_0(k1_tarski(A_210), B_16)))), inference(superposition, [status(thm), theory('equality')], [c_2663, c_40])).
% 4.41/1.77  tff(c_2835, plain, (![A_210]: (k4_xboole_0(k1_tarski(A_210), k1_xboole_0)=k1_tarski(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_2290, c_2763])).
% 4.41/1.77  tff(c_235, plain, (![A_32, B_33]: (k4_xboole_0(k1_tarski(A_32), k1_xboole_0)=k3_xboole_0(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_76, c_206])).
% 4.41/1.77  tff(c_2994, plain, (![A_218, B_219]: (k3_xboole_0(k1_tarski(A_218), B_219)=k1_tarski(A_218) | ~r2_hidden(A_218, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_2835, c_235])).
% 4.41/1.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.41/1.77  tff(c_3203, plain, (![B_225, A_226]: (k3_xboole_0(B_225, k1_tarski(A_226))=k1_tarski(A_226) | ~r2_hidden(A_226, B_225))), inference(superposition, [status(thm), theory('equality')], [c_2994, c_2])).
% 4.41/1.77  tff(c_78, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_7'))!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.41/1.77  tff(c_3268, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3203, c_78])).
% 4.41/1.77  tff(c_3307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_3268])).
% 4.41/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.77  
% 4.41/1.77  Inference rules
% 4.41/1.77  ----------------------
% 4.41/1.77  #Ref     : 0
% 4.41/1.77  #Sup     : 714
% 4.41/1.77  #Fact    : 0
% 4.41/1.77  #Define  : 0
% 4.41/1.77  #Split   : 1
% 4.41/1.77  #Chain   : 0
% 4.41/1.77  #Close   : 0
% 4.41/1.77  
% 4.41/1.77  Ordering : KBO
% 4.41/1.77  
% 4.41/1.77  Simplification rules
% 4.41/1.77  ----------------------
% 4.41/1.77  #Subsume      : 145
% 4.41/1.77  #Demod        : 285
% 4.41/1.77  #Tautology    : 243
% 4.41/1.77  #SimpNegUnit  : 67
% 4.41/1.77  #BackRed      : 6
% 4.41/1.77  
% 4.41/1.77  #Partial instantiations: 0
% 4.41/1.77  #Strategies tried      : 1
% 4.41/1.77  
% 4.41/1.77  Timing (in seconds)
% 4.41/1.77  ----------------------
% 4.41/1.78  Preprocessing        : 0.31
% 4.41/1.78  Parsing              : 0.15
% 4.41/1.78  CNF conversion       : 0.03
% 4.41/1.78  Main loop            : 0.69
% 4.41/1.78  Inferencing          : 0.22
% 4.41/1.78  Reduction            : 0.24
% 4.41/1.78  Demodulation         : 0.18
% 4.41/1.78  BG Simplification    : 0.03
% 4.41/1.78  Subsumption          : 0.14
% 4.41/1.78  Abstraction          : 0.04
% 4.41/1.78  MUC search           : 0.00
% 4.41/1.78  Cooper               : 0.00
% 4.41/1.78  Total                : 1.03
% 4.41/1.78  Index Insertion      : 0.00
% 4.41/1.78  Index Deletion       : 0.00
% 4.41/1.78  Index Matching       : 0.00
% 4.41/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
