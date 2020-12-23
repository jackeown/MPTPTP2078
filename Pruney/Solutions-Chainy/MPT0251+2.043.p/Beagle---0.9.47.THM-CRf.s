%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 102 expanded)
%              Number of equality atoms :   44 (  67 expanded)
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

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

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

tff(c_36,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_170,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_177,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_231,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_343,plain,(
    ! [B_65] : k5_xboole_0(B_65,B_65) = k4_xboole_0(B_65,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_231])).

tff(c_32,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_178,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_170])).

tff(c_240,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_231])).

tff(c_349,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_240])).

tff(c_357,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_349])).

tff(c_42,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_205,plain,(
    ! [B_57,A_58] : k3_tarski(k2_tarski(B_57,A_58)) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_126])).

tff(c_52,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_247,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_52])).

tff(c_263,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_28])).

tff(c_378,plain,(
    ! [A_67,B_68] : k4_xboole_0(k2_xboole_0(A_67,B_68),B_68) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_391,plain,(
    ! [A_62] : k4_xboole_0(k1_xboole_0,A_62) = k4_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_378])).

tff(c_411,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_391])).

tff(c_243,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_231])).

tff(c_427,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_243])).

tff(c_44,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1289,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k2_tarski(A_126,B_127),C_128)
      | ~ r2_hidden(B_127,C_128)
      | ~ r2_hidden(A_126,C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3651,plain,(
    ! [A_187,C_188] :
      ( r1_tarski(k1_tarski(A_187),C_188)
      | ~ r2_hidden(A_187,C_188)
      | ~ r2_hidden(A_187,C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1289])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4553,plain,(
    ! [A_209,C_210] :
      ( k3_xboole_0(k1_tarski(A_209),C_210) = k1_tarski(A_209)
      | ~ r2_hidden(A_209,C_210) ) ),
    inference(resolution,[status(thm)],[c_3651,c_30])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4595,plain,(
    ! [A_209,C_210] :
      ( k5_xboole_0(k1_tarski(A_209),k1_tarski(A_209)) = k4_xboole_0(k1_tarski(A_209),C_210)
      | ~ r2_hidden(A_209,C_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4553,c_26])).

tff(c_4634,plain,(
    ! [A_211,C_212] :
      ( k4_xboole_0(k1_tarski(A_211),C_212) = k1_xboole_0
      | ~ r2_hidden(A_211,C_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_4595])).

tff(c_34,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4684,plain,(
    ! [C_212,A_211] :
      ( k2_xboole_0(C_212,k1_tarski(A_211)) = k2_xboole_0(C_212,k1_xboole_0)
      | ~ r2_hidden(A_211,C_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4634,c_34])).

tff(c_4736,plain,(
    ! [C_213,A_214] :
      ( k2_xboole_0(C_213,k1_tarski(A_214)) = C_213
      | ~ r2_hidden(A_214,C_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4684])).

tff(c_211,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_52])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_246,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_60])).

tff(c_4831,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4736,c_246])).

tff(c_4913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.87  
% 4.36/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.87  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.36/1.87  
% 4.36/1.87  %Foreground sorts:
% 4.36/1.87  
% 4.36/1.87  
% 4.36/1.87  %Background operators:
% 4.36/1.87  
% 4.36/1.87  
% 4.36/1.87  %Foreground operators:
% 4.36/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.36/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.36/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.36/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.36/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.36/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.36/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.36/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.36/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.36/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.36/1.87  
% 4.36/1.89  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.36/1.89  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.36/1.89  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.36/1.89  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.36/1.89  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.36/1.89  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.36/1.89  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.36/1.89  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.36/1.89  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.36/1.89  tff(f_61, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.36/1.89  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.36/1.89  tff(f_81, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.36/1.89  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.36/1.89  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.36/1.89  tff(c_28, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.89  tff(c_36, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.36/1.89  tff(c_24, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.36/1.89  tff(c_170, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.36/1.89  tff(c_177, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_24, c_170])).
% 4.36/1.89  tff(c_231, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.36/1.89  tff(c_343, plain, (![B_65]: (k5_xboole_0(B_65, B_65)=k4_xboole_0(B_65, B_65))), inference(superposition, [status(thm), theory('equality')], [c_177, c_231])).
% 4.36/1.89  tff(c_32, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.36/1.89  tff(c_178, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_170])).
% 4.36/1.89  tff(c_240, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_178, c_231])).
% 4.36/1.89  tff(c_349, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_343, c_240])).
% 4.36/1.89  tff(c_357, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_349])).
% 4.36/1.89  tff(c_42, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.36/1.89  tff(c_126, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.36/1.89  tff(c_205, plain, (![B_57, A_58]: (k3_tarski(k2_tarski(B_57, A_58))=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_42, c_126])).
% 4.36/1.89  tff(c_52, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.36/1.89  tff(c_247, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_205, c_52])).
% 4.36/1.89  tff(c_263, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_247, c_28])).
% 4.36/1.89  tff(c_378, plain, (![A_67, B_68]: (k4_xboole_0(k2_xboole_0(A_67, B_68), B_68)=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.36/1.89  tff(c_391, plain, (![A_62]: (k4_xboole_0(k1_xboole_0, A_62)=k4_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_263, c_378])).
% 4.36/1.89  tff(c_411, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_357, c_391])).
% 4.36/1.89  tff(c_243, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_177, c_231])).
% 4.36/1.89  tff(c_427, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_243])).
% 4.36/1.89  tff(c_44, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.36/1.89  tff(c_1289, plain, (![A_126, B_127, C_128]: (r1_tarski(k2_tarski(A_126, B_127), C_128) | ~r2_hidden(B_127, C_128) | ~r2_hidden(A_126, C_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.36/1.89  tff(c_3651, plain, (![A_187, C_188]: (r1_tarski(k1_tarski(A_187), C_188) | ~r2_hidden(A_187, C_188) | ~r2_hidden(A_187, C_188))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1289])).
% 4.36/1.89  tff(c_30, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.36/1.89  tff(c_4553, plain, (![A_209, C_210]: (k3_xboole_0(k1_tarski(A_209), C_210)=k1_tarski(A_209) | ~r2_hidden(A_209, C_210))), inference(resolution, [status(thm)], [c_3651, c_30])).
% 4.36/1.89  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.36/1.89  tff(c_4595, plain, (![A_209, C_210]: (k5_xboole_0(k1_tarski(A_209), k1_tarski(A_209))=k4_xboole_0(k1_tarski(A_209), C_210) | ~r2_hidden(A_209, C_210))), inference(superposition, [status(thm), theory('equality')], [c_4553, c_26])).
% 4.36/1.89  tff(c_4634, plain, (![A_211, C_212]: (k4_xboole_0(k1_tarski(A_211), C_212)=k1_xboole_0 | ~r2_hidden(A_211, C_212))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_4595])).
% 4.36/1.89  tff(c_34, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.36/1.89  tff(c_4684, plain, (![C_212, A_211]: (k2_xboole_0(C_212, k1_tarski(A_211))=k2_xboole_0(C_212, k1_xboole_0) | ~r2_hidden(A_211, C_212))), inference(superposition, [status(thm), theory('equality')], [c_4634, c_34])).
% 4.36/1.89  tff(c_4736, plain, (![C_213, A_214]: (k2_xboole_0(C_213, k1_tarski(A_214))=C_213 | ~r2_hidden(A_214, C_213))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4684])).
% 4.36/1.89  tff(c_211, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_205, c_52])).
% 4.36/1.89  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.36/1.89  tff(c_246, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_60])).
% 4.36/1.89  tff(c_4831, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4736, c_246])).
% 4.36/1.89  tff(c_4913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_4831])).
% 4.36/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.89  
% 4.36/1.89  Inference rules
% 4.36/1.89  ----------------------
% 4.36/1.89  #Ref     : 0
% 4.36/1.89  #Sup     : 1187
% 4.36/1.89  #Fact    : 0
% 4.36/1.89  #Define  : 0
% 4.36/1.89  #Split   : 1
% 4.36/1.89  #Chain   : 0
% 4.36/1.89  #Close   : 0
% 4.36/1.89  
% 4.36/1.89  Ordering : KBO
% 4.36/1.89  
% 4.36/1.89  Simplification rules
% 4.36/1.89  ----------------------
% 4.36/1.89  #Subsume      : 86
% 4.36/1.89  #Demod        : 1333
% 4.36/1.89  #Tautology    : 893
% 4.36/1.89  #SimpNegUnit  : 0
% 4.36/1.89  #BackRed      : 5
% 4.36/1.89  
% 4.36/1.89  #Partial instantiations: 0
% 4.36/1.89  #Strategies tried      : 1
% 4.36/1.89  
% 4.36/1.89  Timing (in seconds)
% 4.36/1.89  ----------------------
% 4.36/1.89  Preprocessing        : 0.33
% 4.36/1.89  Parsing              : 0.17
% 4.36/1.89  CNF conversion       : 0.02
% 4.36/1.89  Main loop            : 0.80
% 4.36/1.89  Inferencing          : 0.25
% 4.36/1.89  Reduction            : 0.37
% 4.36/1.89  Demodulation         : 0.31
% 4.36/1.89  BG Simplification    : 0.03
% 4.36/1.89  Subsumption          : 0.11
% 4.36/1.89  Abstraction          : 0.04
% 4.36/1.89  MUC search           : 0.00
% 4.36/1.89  Cooper               : 0.00
% 4.36/1.89  Total                : 1.16
% 4.36/1.89  Index Insertion      : 0.00
% 4.36/1.89  Index Deletion       : 0.00
% 4.36/1.89  Index Matching       : 0.00
% 4.36/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
