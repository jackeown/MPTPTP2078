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
% DateTime   : Thu Dec  3 09:50:51 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 104 expanded)
%              Number of equality atoms :   44 (  78 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_62,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_134,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_317,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(B_70,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_134])).

tff(c_52,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_345,plain,(
    ! [B_71,A_72] : k2_xboole_0(B_71,A_72) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_52])).

tff(c_379,plain,(
    ! [A_72] : k2_xboole_0(k1_xboole_0,A_72) = A_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_28])).

tff(c_410,plain,(
    ! [A_73] : k2_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_28])).

tff(c_30,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_437,plain,(
    ! [B_15] : k3_xboole_0(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_30])).

tff(c_36,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_429,plain,(
    ! [A_73] : k4_xboole_0(k1_xboole_0,A_73) = k4_xboole_0(A_73,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_36])).

tff(c_792,plain,(
    ! [A_95,B_96] : k2_xboole_0(k3_xboole_0(A_95,B_96),k4_xboole_0(A_95,B_96)) = A_95 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_822,plain,(
    ! [A_73] : k2_xboole_0(k3_xboole_0(k1_xboole_0,A_73),k4_xboole_0(A_73,A_73)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_792])).

tff(c_846,plain,(
    ! [A_73] : k4_xboole_0(A_73,A_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_437,c_822])).

tff(c_24,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_186,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_198,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_24,c_186])).

tff(c_607,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_622,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_607])).

tff(c_848,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_622])).

tff(c_44,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1302,plain,(
    ! [A_134,B_135,C_136] :
      ( r1_tarski(k2_tarski(A_134,B_135),C_136)
      | ~ r2_hidden(B_135,C_136)
      | ~ r2_hidden(A_134,C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3154,plain,(
    ! [A_207,C_208] :
      ( r1_tarski(k1_tarski(A_207),C_208)
      | ~ r2_hidden(A_207,C_208)
      | ~ r2_hidden(A_207,C_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1302])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6557,plain,(
    ! [A_251,C_252] :
      ( k3_xboole_0(k1_tarski(A_251),C_252) = k1_tarski(A_251)
      | ~ r2_hidden(A_251,C_252) ) ),
    inference(resolution,[status(thm)],[c_3154,c_32])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6588,plain,(
    ! [A_251,C_252] :
      ( k5_xboole_0(k1_tarski(A_251),k1_tarski(A_251)) = k4_xboole_0(k1_tarski(A_251),C_252)
      | ~ r2_hidden(A_251,C_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6557,c_26])).

tff(c_6647,plain,(
    ! [A_253,C_254] :
      ( k4_xboole_0(k1_tarski(A_253),C_254) = k1_xboole_0
      | ~ r2_hidden(A_253,C_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_6588])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6720,plain,(
    ! [C_254,A_253] :
      ( k2_xboole_0(C_254,k1_tarski(A_253)) = k2_xboole_0(C_254,k1_xboole_0)
      | ~ r2_hidden(A_253,C_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6647,c_34])).

tff(c_6862,plain,(
    ! [C_257,A_258] :
      ( k2_xboole_0(C_257,k1_tarski(A_258)) = C_257
      | ~ r2_hidden(A_258,C_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6720])).

tff(c_323,plain,(
    ! [B_70,A_69] : k2_xboole_0(B_70,A_69) = k2_xboole_0(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_52])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_344,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_60])).

tff(c_6998,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6862,c_344])).

tff(c_7104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.08  
% 5.37/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.09  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.37/2.09  
% 5.37/2.09  %Foreground sorts:
% 5.37/2.09  
% 5.37/2.09  
% 5.37/2.09  %Background operators:
% 5.37/2.09  
% 5.37/2.09  
% 5.37/2.09  %Foreground operators:
% 5.37/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.37/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.37/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.37/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.37/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.37/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.37/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.37/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.37/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.37/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.37/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.37/2.09  
% 5.51/2.11  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.51/2.11  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.51/2.11  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.51/2.11  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.51/2.11  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.51/2.11  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.51/2.11  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.51/2.11  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.51/2.11  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.51/2.11  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.51/2.11  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.51/2.11  tff(f_81, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.51/2.11  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.51/2.11  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.51/2.11  tff(c_28, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.51/2.11  tff(c_42, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.51/2.11  tff(c_134, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.51/2.11  tff(c_317, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(B_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_42, c_134])).
% 5.51/2.11  tff(c_52, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.51/2.11  tff(c_345, plain, (![B_71, A_72]: (k2_xboole_0(B_71, A_72)=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_317, c_52])).
% 5.51/2.11  tff(c_379, plain, (![A_72]: (k2_xboole_0(k1_xboole_0, A_72)=A_72)), inference(superposition, [status(thm), theory('equality')], [c_345, c_28])).
% 5.51/2.11  tff(c_410, plain, (![A_73]: (k2_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_345, c_28])).
% 5.51/2.11  tff(c_30, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k3_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.51/2.11  tff(c_437, plain, (![B_15]: (k3_xboole_0(k1_xboole_0, B_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_410, c_30])).
% 5.51/2.11  tff(c_36, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.51/2.11  tff(c_429, plain, (![A_73]: (k4_xboole_0(k1_xboole_0, A_73)=k4_xboole_0(A_73, A_73))), inference(superposition, [status(thm), theory('equality')], [c_410, c_36])).
% 5.51/2.11  tff(c_792, plain, (![A_95, B_96]: (k2_xboole_0(k3_xboole_0(A_95, B_96), k4_xboole_0(A_95, B_96))=A_95)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.51/2.11  tff(c_822, plain, (![A_73]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, A_73), k4_xboole_0(A_73, A_73))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_429, c_792])).
% 5.51/2.11  tff(c_846, plain, (![A_73]: (k4_xboole_0(A_73, A_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_379, c_437, c_822])).
% 5.51/2.11  tff(c_24, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.51/2.11  tff(c_186, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.51/2.11  tff(c_198, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_24, c_186])).
% 5.51/2.11  tff(c_607, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.11  tff(c_622, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_198, c_607])).
% 5.51/2.11  tff(c_848, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_846, c_622])).
% 5.51/2.11  tff(c_44, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.51/2.11  tff(c_1302, plain, (![A_134, B_135, C_136]: (r1_tarski(k2_tarski(A_134, B_135), C_136) | ~r2_hidden(B_135, C_136) | ~r2_hidden(A_134, C_136))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.51/2.11  tff(c_3154, plain, (![A_207, C_208]: (r1_tarski(k1_tarski(A_207), C_208) | ~r2_hidden(A_207, C_208) | ~r2_hidden(A_207, C_208))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1302])).
% 5.51/2.11  tff(c_32, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.51/2.11  tff(c_6557, plain, (![A_251, C_252]: (k3_xboole_0(k1_tarski(A_251), C_252)=k1_tarski(A_251) | ~r2_hidden(A_251, C_252))), inference(resolution, [status(thm)], [c_3154, c_32])).
% 5.51/2.11  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.51/2.11  tff(c_6588, plain, (![A_251, C_252]: (k5_xboole_0(k1_tarski(A_251), k1_tarski(A_251))=k4_xboole_0(k1_tarski(A_251), C_252) | ~r2_hidden(A_251, C_252))), inference(superposition, [status(thm), theory('equality')], [c_6557, c_26])).
% 5.51/2.11  tff(c_6647, plain, (![A_253, C_254]: (k4_xboole_0(k1_tarski(A_253), C_254)=k1_xboole_0 | ~r2_hidden(A_253, C_254))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_6588])).
% 5.51/2.11  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.51/2.11  tff(c_6720, plain, (![C_254, A_253]: (k2_xboole_0(C_254, k1_tarski(A_253))=k2_xboole_0(C_254, k1_xboole_0) | ~r2_hidden(A_253, C_254))), inference(superposition, [status(thm), theory('equality')], [c_6647, c_34])).
% 5.51/2.11  tff(c_6862, plain, (![C_257, A_258]: (k2_xboole_0(C_257, k1_tarski(A_258))=C_257 | ~r2_hidden(A_258, C_257))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6720])).
% 5.51/2.11  tff(c_323, plain, (![B_70, A_69]: (k2_xboole_0(B_70, A_69)=k2_xboole_0(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_317, c_52])).
% 5.51/2.11  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.51/2.11  tff(c_344, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_60])).
% 5.51/2.11  tff(c_6998, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6862, c_344])).
% 5.51/2.11  tff(c_7104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_6998])).
% 5.51/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.11  
% 5.51/2.11  Inference rules
% 5.51/2.11  ----------------------
% 5.51/2.11  #Ref     : 0
% 5.51/2.11  #Sup     : 1738
% 5.51/2.11  #Fact    : 0
% 5.51/2.11  #Define  : 0
% 5.51/2.11  #Split   : 1
% 5.51/2.11  #Chain   : 0
% 5.51/2.11  #Close   : 0
% 5.51/2.11  
% 5.51/2.11  Ordering : KBO
% 5.51/2.11  
% 5.51/2.11  Simplification rules
% 5.51/2.11  ----------------------
% 5.51/2.11  #Subsume      : 185
% 5.51/2.11  #Demod        : 2011
% 5.51/2.11  #Tautology    : 1200
% 5.51/2.11  #SimpNegUnit  : 0
% 5.51/2.11  #BackRed      : 8
% 5.51/2.11  
% 5.51/2.11  #Partial instantiations: 0
% 5.51/2.11  #Strategies tried      : 1
% 5.51/2.11  
% 5.51/2.11  Timing (in seconds)
% 5.51/2.11  ----------------------
% 5.51/2.12  Preprocessing        : 0.31
% 5.51/2.12  Parsing              : 0.16
% 5.51/2.12  CNF conversion       : 0.02
% 5.51/2.12  Main loop            : 1.00
% 5.51/2.12  Inferencing          : 0.30
% 5.51/2.12  Reduction            : 0.47
% 5.51/2.12  Demodulation         : 0.39
% 5.51/2.12  BG Simplification    : 0.03
% 5.51/2.12  Subsumption          : 0.15
% 5.51/2.12  Abstraction          : 0.05
% 5.51/2.12  MUC search           : 0.00
% 5.51/2.12  Cooper               : 0.00
% 5.51/2.12  Total                : 1.35
% 5.51/2.12  Index Insertion      : 0.00
% 5.51/2.12  Index Deletion       : 0.00
% 5.51/2.12  Index Matching       : 0.00
% 5.51/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
