%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   68 (  86 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 113 expanded)
%              Number of equality atoms :   38 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_62,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_842,plain,(
    ! [A_141,B_142,C_143] :
      ( ~ r2_hidden('#skF_2'(A_141,B_142,C_143),B_142)
      | r2_hidden('#skF_3'(A_141,B_142,C_143),C_143)
      | k4_xboole_0(A_141,B_142) = C_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_849,plain,(
    ! [A_8,C_10] :
      ( r2_hidden('#skF_3'(A_8,A_8,C_10),C_10)
      | k4_xboole_0(A_8,A_8) = C_10 ) ),
    inference(resolution,[status(thm)],[c_26,c_842])).

tff(c_851,plain,(
    ! [A_144,C_145] :
      ( r2_hidden('#skF_3'(A_144,A_144,C_145),C_145)
      | k4_xboole_0(A_144,A_144) = C_145 ) ),
    inference(resolution,[status(thm)],[c_26,c_842])).

tff(c_85,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_36])).

tff(c_250,plain,(
    ! [A_60,B_61] : k2_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_257,plain,(
    ! [B_61] : k4_xboole_0(B_61,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_101])).

tff(c_269,plain,(
    ! [B_62] : k4_xboole_0(B_62,k1_xboole_0) = B_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_257])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_278,plain,(
    ! [D_13,B_62] :
      ( ~ r2_hidden(D_13,k1_xboole_0)
      | ~ r2_hidden(D_13,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_12])).

tff(c_908,plain,(
    ! [A_147,B_148] :
      ( ~ r2_hidden('#skF_3'(A_147,A_147,k1_xboole_0),B_148)
      | k4_xboole_0(A_147,A_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_851,c_278])).

tff(c_928,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_849,c_908])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_199,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_207,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_199])).

tff(c_357,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_366,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_357])).

tff(c_44,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_506,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(k2_tarski(A_98,B_99),C_100)
      | ~ r2_hidden(B_99,C_100)
      | ~ r2_hidden(A_98,C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_559,plain,(
    ! [A_107,C_108] :
      ( r1_tarski(k1_tarski(A_107),C_108)
      | ~ r2_hidden(A_107,C_108)
      | ~ r2_hidden(A_107,C_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_506])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_579,plain,(
    ! [A_109,C_110] :
      ( k3_xboole_0(k1_tarski(A_109),C_110) = k1_tarski(A_109)
      | ~ r2_hidden(A_109,C_110) ) ),
    inference(resolution,[status(thm)],[c_559,c_38])).

tff(c_34,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_585,plain,(
    ! [A_109,C_110] :
      ( k5_xboole_0(k1_tarski(A_109),k1_tarski(A_109)) = k4_xboole_0(k1_tarski(A_109),C_110)
      | ~ r2_hidden(A_109,C_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_34])).

tff(c_598,plain,(
    ! [A_109,C_110] :
      ( k4_xboole_0(k1_tarski(A_109),k1_tarski(A_109)) = k4_xboole_0(k1_tarski(A_109),C_110)
      | ~ r2_hidden(A_109,C_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_585])).

tff(c_1638,plain,(
    ! [A_200,C_201] :
      ( k4_xboole_0(k1_tarski(A_200),C_201) = k1_xboole_0
      | ~ r2_hidden(A_200,C_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_598])).

tff(c_42,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1687,plain,(
    ! [C_201,A_200] :
      ( k2_xboole_0(C_201,k1_tarski(A_200)) = k2_xboole_0(C_201,k1_xboole_0)
      | ~ r2_hidden(A_200,C_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_42])).

tff(c_1717,plain,(
    ! [C_202,A_203] :
      ( k2_xboole_0(C_202,k1_tarski(A_203)) = C_202
      | ~ r2_hidden(A_203,C_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1687])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_64,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_1737,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_64])).

tff(c_1764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:09:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.77  
% 3.48/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.77  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.48/1.77  
% 3.48/1.77  %Foreground sorts:
% 3.48/1.77  
% 3.48/1.77  
% 3.48/1.77  %Background operators:
% 3.48/1.77  
% 3.48/1.77  
% 3.48/1.77  %Foreground operators:
% 3.48/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.48/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.48/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.48/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.48/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.77  
% 3.87/1.79  tff(f_83, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.87/1.79  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.87/1.79  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.87/1.79  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.87/1.79  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.87/1.79  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.87/1.79  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.87/1.79  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.87/1.79  tff(f_64, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.87/1.79  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.87/1.79  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.87/1.79  tff(c_36, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.87/1.79  tff(c_26, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), A_8) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.79  tff(c_842, plain, (![A_141, B_142, C_143]: (~r2_hidden('#skF_2'(A_141, B_142, C_143), B_142) | r2_hidden('#skF_3'(A_141, B_142, C_143), C_143) | k4_xboole_0(A_141, B_142)=C_143)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.79  tff(c_849, plain, (![A_8, C_10]: (r2_hidden('#skF_3'(A_8, A_8, C_10), C_10) | k4_xboole_0(A_8, A_8)=C_10)), inference(resolution, [status(thm)], [c_26, c_842])).
% 3.87/1.79  tff(c_851, plain, (![A_144, C_145]: (r2_hidden('#skF_3'(A_144, A_144, C_145), C_145) | k4_xboole_0(A_144, A_144)=C_145)), inference(resolution, [status(thm)], [c_26, c_842])).
% 3.87/1.79  tff(c_85, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.79  tff(c_101, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_85, c_36])).
% 3.87/1.79  tff(c_250, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k4_xboole_0(B_61, A_60))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.87/1.79  tff(c_257, plain, (![B_61]: (k4_xboole_0(B_61, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_61))), inference(superposition, [status(thm), theory('equality')], [c_250, c_101])).
% 3.87/1.79  tff(c_269, plain, (![B_62]: (k4_xboole_0(B_62, k1_xboole_0)=B_62)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_257])).
% 3.87/1.79  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.79  tff(c_278, plain, (![D_13, B_62]: (~r2_hidden(D_13, k1_xboole_0) | ~r2_hidden(D_13, B_62))), inference(superposition, [status(thm), theory('equality')], [c_269, c_12])).
% 3.87/1.79  tff(c_908, plain, (![A_147, B_148]: (~r2_hidden('#skF_3'(A_147, A_147, k1_xboole_0), B_148) | k4_xboole_0(A_147, A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_851, c_278])).
% 3.87/1.79  tff(c_928, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_849, c_908])).
% 3.87/1.79  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.87/1.79  tff(c_199, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.87/1.79  tff(c_207, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_199])).
% 3.87/1.79  tff(c_357, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.87/1.79  tff(c_366, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_207, c_357])).
% 3.87/1.79  tff(c_44, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.87/1.79  tff(c_506, plain, (![A_98, B_99, C_100]: (r1_tarski(k2_tarski(A_98, B_99), C_100) | ~r2_hidden(B_99, C_100) | ~r2_hidden(A_98, C_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.79  tff(c_559, plain, (![A_107, C_108]: (r1_tarski(k1_tarski(A_107), C_108) | ~r2_hidden(A_107, C_108) | ~r2_hidden(A_107, C_108))), inference(superposition, [status(thm), theory('equality')], [c_44, c_506])).
% 3.87/1.79  tff(c_38, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.87/1.79  tff(c_579, plain, (![A_109, C_110]: (k3_xboole_0(k1_tarski(A_109), C_110)=k1_tarski(A_109) | ~r2_hidden(A_109, C_110))), inference(resolution, [status(thm)], [c_559, c_38])).
% 3.87/1.79  tff(c_34, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.87/1.79  tff(c_585, plain, (![A_109, C_110]: (k5_xboole_0(k1_tarski(A_109), k1_tarski(A_109))=k4_xboole_0(k1_tarski(A_109), C_110) | ~r2_hidden(A_109, C_110))), inference(superposition, [status(thm), theory('equality')], [c_579, c_34])).
% 3.87/1.79  tff(c_598, plain, (![A_109, C_110]: (k4_xboole_0(k1_tarski(A_109), k1_tarski(A_109))=k4_xboole_0(k1_tarski(A_109), C_110) | ~r2_hidden(A_109, C_110))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_585])).
% 3.87/1.79  tff(c_1638, plain, (![A_200, C_201]: (k4_xboole_0(k1_tarski(A_200), C_201)=k1_xboole_0 | ~r2_hidden(A_200, C_201))), inference(demodulation, [status(thm), theory('equality')], [c_928, c_598])).
% 3.87/1.79  tff(c_42, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.87/1.79  tff(c_1687, plain, (![C_201, A_200]: (k2_xboole_0(C_201, k1_tarski(A_200))=k2_xboole_0(C_201, k1_xboole_0) | ~r2_hidden(A_200, C_201))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_42])).
% 3.87/1.79  tff(c_1717, plain, (![C_202, A_203]: (k2_xboole_0(C_202, k1_tarski(A_203))=C_202 | ~r2_hidden(A_203, C_202))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1687])).
% 3.87/1.79  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.79  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.87/1.79  tff(c_64, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 3.87/1.79  tff(c_1737, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1717, c_64])).
% 3.87/1.79  tff(c_1764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1737])).
% 3.87/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.79  
% 3.87/1.79  Inference rules
% 3.87/1.79  ----------------------
% 3.87/1.79  #Ref     : 0
% 3.87/1.79  #Sup     : 383
% 3.87/1.79  #Fact    : 0
% 3.87/1.79  #Define  : 0
% 3.87/1.79  #Split   : 3
% 3.87/1.79  #Chain   : 0
% 3.87/1.79  #Close   : 0
% 3.87/1.79  
% 3.87/1.79  Ordering : KBO
% 3.87/1.79  
% 3.87/1.79  Simplification rules
% 3.87/1.79  ----------------------
% 3.87/1.79  #Subsume      : 74
% 3.87/1.79  #Demod        : 181
% 3.87/1.79  #Tautology    : 194
% 3.87/1.79  #SimpNegUnit  : 0
% 3.87/1.79  #BackRed      : 4
% 3.87/1.79  
% 3.87/1.79  #Partial instantiations: 0
% 3.87/1.79  #Strategies tried      : 1
% 3.87/1.79  
% 3.87/1.79  Timing (in seconds)
% 3.87/1.79  ----------------------
% 3.87/1.79  Preprocessing        : 0.41
% 3.87/1.79  Parsing              : 0.18
% 3.87/1.79  CNF conversion       : 0.04
% 3.87/1.79  Main loop            : 0.54
% 3.87/1.79  Inferencing          : 0.19
% 3.87/1.79  Reduction            : 0.17
% 3.87/1.79  Demodulation         : 0.13
% 3.87/1.79  BG Simplification    : 0.03
% 3.87/1.79  Subsumption          : 0.11
% 3.87/1.79  Abstraction          : 0.03
% 3.87/1.79  MUC search           : 0.00
% 3.87/1.79  Cooper               : 0.00
% 3.87/1.79  Total                : 0.99
% 3.87/1.79  Index Insertion      : 0.00
% 3.87/1.79  Index Deletion       : 0.00
% 3.87/1.79  Index Matching       : 0.00
% 3.87/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
