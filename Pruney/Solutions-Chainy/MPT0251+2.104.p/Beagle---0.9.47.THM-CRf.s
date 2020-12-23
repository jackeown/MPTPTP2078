%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 107 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 (  99 expanded)
%              Number of equality atoms :   42 (  77 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_866,plain,(
    ! [B_103,A_104] :
      ( k3_xboole_0(B_103,k1_tarski(A_104)) = k1_tarski(A_104)
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4280,plain,(
    ! [B_190,A_191] :
      ( k5_xboole_0(B_190,k1_tarski(A_191)) = k4_xboole_0(B_190,k1_tarski(A_191))
      | ~ r2_hidden(A_191,B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_4])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_999,plain,(
    ! [A_108,B_109,C_110] : k5_xboole_0(k5_xboole_0(A_108,B_109),C_110) = k5_xboole_0(A_108,k5_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_341,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_356,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_341])).

tff(c_370,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_356])).

tff(c_1013,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k5_xboole_0(B_109,k5_xboole_0(A_108,B_109))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_370])).

tff(c_83,plain,(
    ! [B_58,A_59] : k3_xboole_0(B_58,A_59) = k3_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),A_54) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [B_55] : k3_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_10])).

tff(c_99,plain,(
    ! [B_58] : k3_xboole_0(B_58,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_58])).

tff(c_353,plain,(
    ! [B_58] : k5_xboole_0(B_58,k1_xboole_0) = k4_xboole_0(B_58,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_341])).

tff(c_369,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = B_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_353])).

tff(c_545,plain,(
    ! [A_89,B_90] : k2_xboole_0(k3_xboole_0(A_89,B_90),k4_xboole_0(A_89,B_90)) = A_89 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_584,plain,(
    ! [B_58] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_58,k1_xboole_0)) = B_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_545])).

tff(c_607,plain,(
    ! [B_58] : k2_xboole_0(k1_xboole_0,B_58) = B_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_584])).

tff(c_433,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_353])).

tff(c_439,plain,(
    ! [B_85] : k5_xboole_0(k1_xboole_0,B_85) = k2_xboole_0(k1_xboole_0,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_20])).

tff(c_1064,plain,(
    ! [B_85] : k5_xboole_0(k1_xboole_0,B_85) = B_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_439])).

tff(c_1037,plain,(
    ! [A_7,C_110] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_110)) = k5_xboole_0(k1_xboole_0,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_999])).

tff(c_1602,plain,(
    ! [A_141,C_142] : k5_xboole_0(A_141,k5_xboole_0(A_141,C_142)) = C_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_1037])).

tff(c_1639,plain,(
    ! [B_109,A_108] : k5_xboole_0(B_109,k5_xboole_0(A_108,B_109)) = k5_xboole_0(A_108,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_1602])).

tff(c_1683,plain,(
    ! [B_109,A_108] : k5_xboole_0(B_109,k5_xboole_0(A_108,B_109)) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1639])).

tff(c_4306,plain,(
    ! [A_191,B_190] :
      ( k5_xboole_0(k1_tarski(A_191),k4_xboole_0(B_190,k1_tarski(A_191))) = B_190
      | ~ r2_hidden(A_191,B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4280,c_1683])).

tff(c_6902,plain,(
    ! [A_233,B_234] :
      ( k2_xboole_0(k1_tarski(A_233),B_234) = B_234
      | ~ r2_hidden(A_233,B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4306])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6959,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6902,c_40])).

tff(c_6993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/2.07  
% 5.07/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/2.07  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.07/2.07  
% 5.07/2.07  %Foreground sorts:
% 5.07/2.07  
% 5.07/2.07  
% 5.07/2.07  %Background operators:
% 5.07/2.07  
% 5.07/2.07  
% 5.07/2.07  %Foreground operators:
% 5.07/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.07/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.07/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.07/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.07/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.07/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.07/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.07/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.07/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.07/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.07/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.07/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.07/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.07/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.07/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.07  
% 5.41/2.08  tff(f_72, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.41/2.08  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.41/2.08  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.41/2.08  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.41/2.08  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.41/2.08  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.41/2.08  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.41/2.08  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.41/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.41/2.08  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.41/2.08  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.41/2.08  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.41/2.08  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.41/2.08  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.41/2.08  tff(c_866, plain, (![B_103, A_104]: (k3_xboole_0(B_103, k1_tarski(A_104))=k1_tarski(A_104) | ~r2_hidden(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.41/2.08  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.41/2.08  tff(c_4280, plain, (![B_190, A_191]: (k5_xboole_0(B_190, k1_tarski(A_191))=k4_xboole_0(B_190, k1_tarski(A_191)) | ~r2_hidden(A_191, B_190))), inference(superposition, [status(thm), theory('equality')], [c_866, c_4])).
% 5.41/2.08  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.41/2.08  tff(c_999, plain, (![A_108, B_109, C_110]: (k5_xboole_0(k5_xboole_0(A_108, B_109), C_110)=k5_xboole_0(A_108, k5_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.41/2.08  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.41/2.08  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.41/2.08  tff(c_341, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.41/2.08  tff(c_356, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_341])).
% 5.41/2.08  tff(c_370, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_356])).
% 5.41/2.08  tff(c_1013, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k5_xboole_0(B_109, k5_xboole_0(A_108, B_109)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_999, c_370])).
% 5.41/2.08  tff(c_83, plain, (![B_58, A_59]: (k3_xboole_0(B_58, A_59)=k3_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.41/2.08  tff(c_53, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.41/2.08  tff(c_10, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.41/2.08  tff(c_58, plain, (![B_55]: (k3_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_53, c_10])).
% 5.41/2.08  tff(c_99, plain, (![B_58]: (k3_xboole_0(B_58, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_58])).
% 5.41/2.08  tff(c_353, plain, (![B_58]: (k5_xboole_0(B_58, k1_xboole_0)=k4_xboole_0(B_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_341])).
% 5.41/2.08  tff(c_369, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_353])).
% 5.41/2.08  tff(c_545, plain, (![A_89, B_90]: (k2_xboole_0(k3_xboole_0(A_89, B_90), k4_xboole_0(A_89, B_90))=A_89)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.41/2.08  tff(c_584, plain, (![B_58]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_58, k1_xboole_0))=B_58)), inference(superposition, [status(thm), theory('equality')], [c_99, c_545])).
% 5.41/2.08  tff(c_607, plain, (![B_58]: (k2_xboole_0(k1_xboole_0, B_58)=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_584])).
% 5.41/2.08  tff(c_433, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=B_85)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_353])).
% 5.41/2.08  tff(c_439, plain, (![B_85]: (k5_xboole_0(k1_xboole_0, B_85)=k2_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_433, c_20])).
% 5.41/2.08  tff(c_1064, plain, (![B_85]: (k5_xboole_0(k1_xboole_0, B_85)=B_85)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_439])).
% 5.41/2.08  tff(c_1037, plain, (![A_7, C_110]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_110))=k5_xboole_0(k1_xboole_0, C_110))), inference(superposition, [status(thm), theory('equality')], [c_370, c_999])).
% 5.41/2.08  tff(c_1602, plain, (![A_141, C_142]: (k5_xboole_0(A_141, k5_xboole_0(A_141, C_142))=C_142)), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_1037])).
% 5.41/2.08  tff(c_1639, plain, (![B_109, A_108]: (k5_xboole_0(B_109, k5_xboole_0(A_108, B_109))=k5_xboole_0(A_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1013, c_1602])).
% 5.41/2.08  tff(c_1683, plain, (![B_109, A_108]: (k5_xboole_0(B_109, k5_xboole_0(A_108, B_109))=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1639])).
% 5.41/2.08  tff(c_4306, plain, (![A_191, B_190]: (k5_xboole_0(k1_tarski(A_191), k4_xboole_0(B_190, k1_tarski(A_191)))=B_190 | ~r2_hidden(A_191, B_190))), inference(superposition, [status(thm), theory('equality')], [c_4280, c_1683])).
% 5.41/2.08  tff(c_6902, plain, (![A_233, B_234]: (k2_xboole_0(k1_tarski(A_233), B_234)=B_234 | ~r2_hidden(A_233, B_234))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4306])).
% 5.41/2.08  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.41/2.08  tff(c_6959, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6902, c_40])).
% 5.41/2.08  tff(c_6993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6959])).
% 5.41/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.08  
% 5.41/2.08  Inference rules
% 5.41/2.08  ----------------------
% 5.41/2.08  #Ref     : 0
% 5.41/2.08  #Sup     : 1713
% 5.41/2.08  #Fact    : 0
% 5.41/2.08  #Define  : 0
% 5.41/2.08  #Split   : 0
% 5.41/2.08  #Chain   : 0
% 5.41/2.08  #Close   : 0
% 5.41/2.08  
% 5.41/2.08  Ordering : KBO
% 5.41/2.08  
% 5.41/2.08  Simplification rules
% 5.41/2.08  ----------------------
% 5.41/2.08  #Subsume      : 128
% 5.41/2.08  #Demod        : 1738
% 5.41/2.08  #Tautology    : 1138
% 5.41/2.08  #SimpNegUnit  : 0
% 5.41/2.08  #BackRed      : 5
% 5.41/2.08  
% 5.41/2.08  #Partial instantiations: 0
% 5.41/2.08  #Strategies tried      : 1
% 5.41/2.08  
% 5.41/2.08  Timing (in seconds)
% 5.41/2.08  ----------------------
% 5.41/2.08  Preprocessing        : 0.32
% 5.41/2.08  Parsing              : 0.17
% 5.41/2.08  CNF conversion       : 0.02
% 5.41/2.08  Main loop            : 0.97
% 5.41/2.08  Inferencing          : 0.31
% 5.41/2.08  Reduction            : 0.45
% 5.41/2.08  Demodulation         : 0.39
% 5.41/2.08  BG Simplification    : 0.04
% 5.41/2.08  Subsumption          : 0.12
% 5.41/2.08  Abstraction          : 0.05
% 5.41/2.08  MUC search           : 0.00
% 5.41/2.08  Cooper               : 0.00
% 5.41/2.08  Total                : 1.31
% 5.41/2.08  Index Insertion      : 0.00
% 5.41/2.08  Index Deletion       : 0.00
% 5.41/2.08  Index Matching       : 0.00
% 5.41/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
