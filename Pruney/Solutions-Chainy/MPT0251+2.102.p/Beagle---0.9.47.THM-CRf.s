%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 337 expanded)
%              Number of leaves         :   37 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :   70 ( 364 expanded)
%              Number of equality atoms :   46 ( 284 expanded)
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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_252,plain,(
    ! [A_86,B_87] :
      ( ~ r1_xboole_0(A_86,B_87)
      | k3_xboole_0(A_86,B_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_234])).

tff(c_256,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_252])).

tff(c_347,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_363,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_347])).

tff(c_384,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_363])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_373,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_347])).

tff(c_387,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_373])).

tff(c_582,plain,(
    ! [A_104,B_105,C_106] : k5_xboole_0(k5_xboole_0(A_104,B_105),C_106) = k5_xboole_0(A_104,k5_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_624,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k5_xboole_0(B_105,k5_xboole_0(A_104,B_105))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_582])).

tff(c_197,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_212,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = k2_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_197])).

tff(c_620,plain,(
    ! [A_12,C_106] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_106)) = k5_xboole_0(k1_xboole_0,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_582])).

tff(c_1019,plain,(
    ! [A_152,C_153] : k5_xboole_0(A_152,k5_xboole_0(A_152,C_153)) = k2_xboole_0(k1_xboole_0,C_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_620])).

tff(c_1079,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_1019])).

tff(c_1106,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_1079])).

tff(c_649,plain,(
    ! [A_12,C_106] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_106)) = k2_xboole_0(k1_xboole_0,C_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_620])).

tff(c_1306,plain,(
    ! [A_158,C_159] : k5_xboole_0(A_158,k5_xboole_0(A_158,C_159)) = C_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_649])).

tff(c_1350,plain,(
    ! [B_105,A_104] : k5_xboole_0(B_105,k5_xboole_0(A_104,B_105)) = k5_xboole_0(A_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_1306])).

tff(c_1398,plain,(
    ! [B_160,A_161] : k5_xboole_0(B_160,k5_xboole_0(A_161,B_160)) = A_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_1350])).

tff(c_1108,plain,(
    ! [A_12,C_106] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_106)) = C_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_649])).

tff(c_1407,plain,(
    ! [B_160,A_161] : k5_xboole_0(B_160,A_161) = k5_xboole_0(A_161,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_1398,c_1108])).

tff(c_42,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tarski(A_53),B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_192,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_196,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(k1_tarski(A_53),B_54) = k1_tarski(A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_42,c_192])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_376,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_347])).

tff(c_2060,plain,(
    ! [A_178,B_179] : k5_xboole_0(A_178,k4_xboole_0(A_178,B_179)) = k3_xboole_0(B_179,A_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_1306])).

tff(c_1389,plain,(
    ! [B_105,A_104] : k5_xboole_0(B_105,k5_xboole_0(A_104,B_105)) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_1350])).

tff(c_2360,plain,(
    ! [A_186,B_187] : k5_xboole_0(k4_xboole_0(A_186,B_187),k3_xboole_0(B_187,A_186)) = A_186 ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_1389])).

tff(c_2402,plain,(
    ! [B_54,A_53] :
      ( k5_xboole_0(k4_xboole_0(B_54,k1_tarski(A_53)),k1_tarski(A_53)) = B_54
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2360])).

tff(c_2783,plain,(
    ! [A_196,B_197] :
      ( k2_xboole_0(k1_tarski(A_196),B_197) = B_197
      | ~ r2_hidden(A_196,B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1407,c_2402])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2826,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2783,c_46])).

tff(c_2849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  
% 3.64/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.64/1.66  
% 3.64/1.66  %Foreground sorts:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Background operators:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Foreground operators:
% 3.64/1.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.64/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.64/1.66  
% 3.80/1.69  tff(f_92, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.80/1.69  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.80/1.69  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.80/1.69  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.80/1.69  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.80/1.69  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.80/1.69  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.80/1.69  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.80/1.69  tff(f_53, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.80/1.69  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.80/1.69  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.80/1.69  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.80/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.80/1.69  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.80/1.69  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.80/1.69  tff(c_16, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.80/1.69  tff(c_20, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.80/1.69  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.80/1.69  tff(c_234, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.69  tff(c_252, plain, (![A_86, B_87]: (~r1_xboole_0(A_86, B_87) | k3_xboole_0(A_86, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_234])).
% 3.80/1.69  tff(c_256, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_252])).
% 3.80/1.69  tff(c_347, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.69  tff(c_363, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_256, c_347])).
% 3.80/1.69  tff(c_384, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_363])).
% 3.80/1.69  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.80/1.69  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.80/1.69  tff(c_373, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k5_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_347])).
% 3.80/1.69  tff(c_387, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_373])).
% 3.80/1.69  tff(c_582, plain, (![A_104, B_105, C_106]: (k5_xboole_0(k5_xboole_0(A_104, B_105), C_106)=k5_xboole_0(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.80/1.69  tff(c_624, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k5_xboole_0(B_105, k5_xboole_0(A_104, B_105)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_387, c_582])).
% 3.80/1.69  tff(c_197, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.80/1.69  tff(c_212, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=k2_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_16, c_197])).
% 3.80/1.69  tff(c_620, plain, (![A_12, C_106]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_106))=k5_xboole_0(k1_xboole_0, C_106))), inference(superposition, [status(thm), theory('equality')], [c_387, c_582])).
% 3.80/1.69  tff(c_1019, plain, (![A_152, C_153]: (k5_xboole_0(A_152, k5_xboole_0(A_152, C_153))=k2_xboole_0(k1_xboole_0, C_153))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_620])).
% 3.80/1.69  tff(c_1079, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_387, c_1019])).
% 3.80/1.69  tff(c_1106, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_384, c_1079])).
% 3.80/1.69  tff(c_649, plain, (![A_12, C_106]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_106))=k2_xboole_0(k1_xboole_0, C_106))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_620])).
% 3.80/1.69  tff(c_1306, plain, (![A_158, C_159]: (k5_xboole_0(A_158, k5_xboole_0(A_158, C_159))=C_159)), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_649])).
% 3.80/1.69  tff(c_1350, plain, (![B_105, A_104]: (k5_xboole_0(B_105, k5_xboole_0(A_104, B_105))=k5_xboole_0(A_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_624, c_1306])).
% 3.80/1.69  tff(c_1398, plain, (![B_160, A_161]: (k5_xboole_0(B_160, k5_xboole_0(A_161, B_160))=A_161)), inference(demodulation, [status(thm), theory('equality')], [c_384, c_1350])).
% 3.80/1.69  tff(c_1108, plain, (![A_12, C_106]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_106))=C_106)), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_649])).
% 3.80/1.69  tff(c_1407, plain, (![B_160, A_161]: (k5_xboole_0(B_160, A_161)=k5_xboole_0(A_161, B_160))), inference(superposition, [status(thm), theory('equality')], [c_1398, c_1108])).
% 3.80/1.69  tff(c_42, plain, (![A_53, B_54]: (r1_tarski(k1_tarski(A_53), B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.80/1.69  tff(c_192, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.80/1.69  tff(c_196, plain, (![A_53, B_54]: (k3_xboole_0(k1_tarski(A_53), B_54)=k1_tarski(A_53) | ~r2_hidden(A_53, B_54))), inference(resolution, [status(thm)], [c_42, c_192])).
% 3.80/1.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.80/1.69  tff(c_376, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_347])).
% 3.80/1.69  tff(c_2060, plain, (![A_178, B_179]: (k5_xboole_0(A_178, k4_xboole_0(A_178, B_179))=k3_xboole_0(B_179, A_178))), inference(superposition, [status(thm), theory('equality')], [c_376, c_1306])).
% 3.80/1.69  tff(c_1389, plain, (![B_105, A_104]: (k5_xboole_0(B_105, k5_xboole_0(A_104, B_105))=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_384, c_1350])).
% 3.80/1.69  tff(c_2360, plain, (![A_186, B_187]: (k5_xboole_0(k4_xboole_0(A_186, B_187), k3_xboole_0(B_187, A_186))=A_186)), inference(superposition, [status(thm), theory('equality')], [c_2060, c_1389])).
% 3.80/1.69  tff(c_2402, plain, (![B_54, A_53]: (k5_xboole_0(k4_xboole_0(B_54, k1_tarski(A_53)), k1_tarski(A_53))=B_54 | ~r2_hidden(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_196, c_2360])).
% 3.80/1.69  tff(c_2783, plain, (![A_196, B_197]: (k2_xboole_0(k1_tarski(A_196), B_197)=B_197 | ~r2_hidden(A_196, B_197))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1407, c_2402])).
% 3.80/1.69  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.80/1.69  tff(c_2826, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2783, c_46])).
% 3.80/1.69  tff(c_2849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2826])).
% 3.80/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.69  
% 3.80/1.69  Inference rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Ref     : 0
% 3.80/1.69  #Sup     : 684
% 3.80/1.69  #Fact    : 0
% 3.80/1.69  #Define  : 0
% 3.80/1.69  #Split   : 0
% 3.80/1.69  #Chain   : 0
% 3.80/1.69  #Close   : 0
% 3.80/1.69  
% 3.80/1.69  Ordering : KBO
% 3.80/1.69  
% 3.80/1.69  Simplification rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Subsume      : 53
% 3.80/1.69  #Demod        : 471
% 3.80/1.69  #Tautology    : 452
% 3.80/1.69  #SimpNegUnit  : 4
% 3.80/1.69  #BackRed      : 7
% 3.80/1.69  
% 3.80/1.69  #Partial instantiations: 0
% 3.80/1.69  #Strategies tried      : 1
% 3.80/1.69  
% 3.80/1.69  Timing (in seconds)
% 3.80/1.69  ----------------------
% 3.80/1.69  Preprocessing        : 0.32
% 3.80/1.69  Parsing              : 0.17
% 3.80/1.69  CNF conversion       : 0.02
% 3.80/1.69  Main loop            : 0.56
% 3.80/1.70  Inferencing          : 0.21
% 3.80/1.70  Reduction            : 0.21
% 3.80/1.70  Demodulation         : 0.17
% 3.80/1.70  BG Simplification    : 0.03
% 3.80/1.70  Subsumption          : 0.08
% 3.80/1.70  Abstraction          : 0.03
% 3.80/1.70  MUC search           : 0.00
% 3.80/1.70  Cooper               : 0.00
% 3.80/1.70  Total                : 0.94
% 3.80/1.70  Index Insertion      : 0.00
% 3.80/1.70  Index Deletion       : 0.00
% 3.80/1.70  Index Matching       : 0.00
% 3.80/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
