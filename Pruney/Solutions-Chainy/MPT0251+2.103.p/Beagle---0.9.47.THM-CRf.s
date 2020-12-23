%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 110 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 114 expanded)
%              Number of equality atoms :   40 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_50,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_520,plain,(
    ! [B_108,A_109] :
      ( k3_xboole_0(B_108,k1_tarski(A_109)) = k1_tarski(A_109)
      | ~ r2_hidden(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4598,plain,(
    ! [B_226,A_227] :
      ( k5_xboole_0(B_226,k1_tarski(A_227)) = k4_xboole_0(B_226,k1_tarski(A_227))
      | ~ r2_hidden(A_227,B_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_10])).

tff(c_22,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_738,plain,(
    ! [A_121,B_122,C_123] : k5_xboole_0(k5_xboole_0(A_121,B_122),C_123) = k5_xboole_0(A_121,k5_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_387,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_402,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k5_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_387])).

tff(c_413,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_402])).

tff(c_748,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k5_xboole_0(B_122,k5_xboole_0(A_121,B_122))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_413])).

tff(c_24,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_286,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_802,plain,(
    ! [A_124,B_125] :
      ( ~ r1_xboole_0(A_124,B_125)
      | k3_xboole_0(A_124,B_125) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_286])).

tff(c_806,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_802])).

tff(c_807,plain,(
    ! [A_126] : k3_xboole_0(A_126,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_802])).

tff(c_827,plain,(
    ! [A_126] : k5_xboole_0(A_126,k1_xboole_0) = k4_xboole_0(A_126,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_10])).

tff(c_882,plain,(
    ! [A_128] : k4_xboole_0(A_128,k1_xboole_0) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_827])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_900,plain,(
    ! [A_128] : k2_xboole_0(k3_xboole_0(A_128,k1_xboole_0),A_128) = A_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_20])).

tff(c_922,plain,(
    ! [A_128] : k2_xboole_0(k1_xboole_0,A_128) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_900])).

tff(c_903,plain,(
    ! [A_128] : k5_xboole_0(k1_xboole_0,A_128) = k2_xboole_0(k1_xboole_0,A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_28])).

tff(c_1180,plain,(
    ! [A_128] : k5_xboole_0(k1_xboole_0,A_128) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_903])).

tff(c_769,plain,(
    ! [A_14,C_123] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_123)) = k5_xboole_0(k1_xboole_0,C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_738])).

tff(c_2348,plain,(
    ! [A_193,C_194] : k5_xboole_0(A_193,k5_xboole_0(A_193,C_194)) = C_194 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_769])).

tff(c_2385,plain,(
    ! [B_122,A_121] : k5_xboole_0(B_122,k5_xboole_0(A_121,B_122)) = k5_xboole_0(A_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_2348])).

tff(c_2429,plain,(
    ! [B_122,A_121] : k5_xboole_0(B_122,k5_xboole_0(A_121,B_122)) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2385])).

tff(c_4624,plain,(
    ! [A_227,B_226] :
      ( k5_xboole_0(k1_tarski(A_227),k4_xboole_0(B_226,k1_tarski(A_227))) = B_226
      | ~ r2_hidden(A_227,B_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4598,c_2429])).

tff(c_6047,plain,(
    ! [A_255,B_256] :
      ( k2_xboole_0(k1_tarski(A_255),B_256) = B_256
      | ~ r2_hidden(A_255,B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4624])).

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6105,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6047,c_48])).

tff(c_6139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:30:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.04  
% 5.02/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.02/2.04  
% 5.02/2.04  %Foreground sorts:
% 5.02/2.04  
% 5.02/2.04  
% 5.02/2.04  %Background operators:
% 5.02/2.04  
% 5.02/2.04  
% 5.02/2.04  %Foreground operators:
% 5.02/2.04  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.02/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.02/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.02/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/2.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.02/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.02/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/2.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.02/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.02/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.02/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.02/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.02/2.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.02/2.04  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.02/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/2.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.02/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.02/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.02/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.02/2.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.02/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.02/2.04  
% 5.02/2.06  tff(f_96, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.02/2.06  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.02/2.06  tff(f_89, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.02/2.06  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.02/2.06  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.02/2.06  tff(f_69, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.02/2.06  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.02/2.06  tff(f_55, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.02/2.06  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.02/2.06  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.02/2.06  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.02/2.06  tff(f_63, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.02/2.06  tff(c_50, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.02/2.06  tff(c_28, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.02/2.06  tff(c_520, plain, (![B_108, A_109]: (k3_xboole_0(B_108, k1_tarski(A_109))=k1_tarski(A_109) | ~r2_hidden(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.02/2.06  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.02/2.06  tff(c_4598, plain, (![B_226, A_227]: (k5_xboole_0(B_226, k1_tarski(A_227))=k4_xboole_0(B_226, k1_tarski(A_227)) | ~r2_hidden(A_227, B_226))), inference(superposition, [status(thm), theory('equality')], [c_520, c_10])).
% 5.02/2.06  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.02/2.06  tff(c_738, plain, (![A_121, B_122, C_123]: (k5_xboole_0(k5_xboole_0(A_121, B_122), C_123)=k5_xboole_0(A_121, k5_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.02/2.06  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.02/2.06  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/2.06  tff(c_387, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.02/2.06  tff(c_402, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k5_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_387])).
% 5.02/2.06  tff(c_413, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_402])).
% 5.02/2.06  tff(c_748, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k5_xboole_0(B_122, k5_xboole_0(A_121, B_122)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_738, c_413])).
% 5.02/2.06  tff(c_24, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.02/2.06  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.02/2.06  tff(c_286, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.02/2.06  tff(c_802, plain, (![A_124, B_125]: (~r1_xboole_0(A_124, B_125) | k3_xboole_0(A_124, B_125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_286])).
% 5.02/2.06  tff(c_806, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_802])).
% 5.02/2.06  tff(c_807, plain, (![A_126]: (k3_xboole_0(A_126, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_802])).
% 5.02/2.06  tff(c_827, plain, (![A_126]: (k5_xboole_0(A_126, k1_xboole_0)=k4_xboole_0(A_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_807, c_10])).
% 5.02/2.06  tff(c_882, plain, (![A_128]: (k4_xboole_0(A_128, k1_xboole_0)=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_827])).
% 5.02/2.06  tff(c_20, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/2.06  tff(c_900, plain, (![A_128]: (k2_xboole_0(k3_xboole_0(A_128, k1_xboole_0), A_128)=A_128)), inference(superposition, [status(thm), theory('equality')], [c_882, c_20])).
% 5.02/2.06  tff(c_922, plain, (![A_128]: (k2_xboole_0(k1_xboole_0, A_128)=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_806, c_900])).
% 5.02/2.06  tff(c_903, plain, (![A_128]: (k5_xboole_0(k1_xboole_0, A_128)=k2_xboole_0(k1_xboole_0, A_128))), inference(superposition, [status(thm), theory('equality')], [c_882, c_28])).
% 5.02/2.06  tff(c_1180, plain, (![A_128]: (k5_xboole_0(k1_xboole_0, A_128)=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_922, c_903])).
% 5.02/2.06  tff(c_769, plain, (![A_14, C_123]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_123))=k5_xboole_0(k1_xboole_0, C_123))), inference(superposition, [status(thm), theory('equality')], [c_413, c_738])).
% 5.02/2.06  tff(c_2348, plain, (![A_193, C_194]: (k5_xboole_0(A_193, k5_xboole_0(A_193, C_194))=C_194)), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_769])).
% 5.02/2.06  tff(c_2385, plain, (![B_122, A_121]: (k5_xboole_0(B_122, k5_xboole_0(A_121, B_122))=k5_xboole_0(A_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_748, c_2348])).
% 5.02/2.06  tff(c_2429, plain, (![B_122, A_121]: (k5_xboole_0(B_122, k5_xboole_0(A_121, B_122))=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2385])).
% 5.02/2.06  tff(c_4624, plain, (![A_227, B_226]: (k5_xboole_0(k1_tarski(A_227), k4_xboole_0(B_226, k1_tarski(A_227)))=B_226 | ~r2_hidden(A_227, B_226))), inference(superposition, [status(thm), theory('equality')], [c_4598, c_2429])).
% 5.02/2.06  tff(c_6047, plain, (![A_255, B_256]: (k2_xboole_0(k1_tarski(A_255), B_256)=B_256 | ~r2_hidden(A_255, B_256))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4624])).
% 5.02/2.06  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.02/2.06  tff(c_6105, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6047, c_48])).
% 5.02/2.06  tff(c_6139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_6105])).
% 5.02/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/2.06  
% 5.02/2.06  Inference rules
% 5.02/2.06  ----------------------
% 5.02/2.06  #Ref     : 0
% 5.02/2.06  #Sup     : 1522
% 5.02/2.06  #Fact    : 0
% 5.02/2.06  #Define  : 0
% 5.02/2.06  #Split   : 0
% 5.02/2.06  #Chain   : 0
% 5.02/2.06  #Close   : 0
% 5.02/2.06  
% 5.02/2.06  Ordering : KBO
% 5.02/2.06  
% 5.02/2.06  Simplification rules
% 5.02/2.06  ----------------------
% 5.02/2.06  #Subsume      : 161
% 5.02/2.06  #Demod        : 1442
% 5.02/2.06  #Tautology    : 1001
% 5.02/2.06  #SimpNegUnit  : 4
% 5.02/2.06  #BackRed      : 5
% 5.02/2.06  
% 5.02/2.06  #Partial instantiations: 0
% 5.02/2.06  #Strategies tried      : 1
% 5.02/2.06  
% 5.02/2.06  Timing (in seconds)
% 5.02/2.06  ----------------------
% 5.02/2.06  Preprocessing        : 0.36
% 5.02/2.06  Parsing              : 0.19
% 5.02/2.06  CNF conversion       : 0.02
% 5.02/2.06  Main loop            : 0.90
% 5.02/2.06  Inferencing          : 0.29
% 5.02/2.06  Reduction            : 0.41
% 5.02/2.06  Demodulation         : 0.34
% 5.02/2.06  BG Simplification    : 0.04
% 5.02/2.06  Subsumption          : 0.12
% 5.02/2.06  Abstraction          : 0.05
% 5.02/2.06  MUC search           : 0.00
% 5.02/2.06  Cooper               : 0.00
% 5.02/2.06  Total                : 1.29
% 5.02/2.06  Index Insertion      : 0.00
% 5.02/2.06  Index Deletion       : 0.00
% 5.02/2.06  Index Matching       : 0.00
% 5.02/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
