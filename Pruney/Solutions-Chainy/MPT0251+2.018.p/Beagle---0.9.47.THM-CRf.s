%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:48 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 146 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :   76 ( 151 expanded)
%              Number of equality atoms :   50 ( 117 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_251,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_134])).

tff(c_32,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_302,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_32])).

tff(c_330,plain,(
    ! [A_61] : k2_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_12])).

tff(c_414,plain,(
    ! [A_64,B_65] : k2_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_421,plain,(
    ! [B_65] : k4_xboole_0(B_65,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_330])).

tff(c_436,plain,(
    ! [B_65] : k4_xboole_0(B_65,k1_xboole_0) = B_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_421])).

tff(c_361,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_12])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_197,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(resolution,[status(thm)],[c_20,c_186])).

tff(c_442,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_197])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_510,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_518,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k4_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_10])).

tff(c_548,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_518])).

tff(c_447,plain,(
    ! [A_66] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_10])).

tff(c_853,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_447])).

tff(c_560,plain,(
    ! [A_69,B_70] : k4_xboole_0(k2_xboole_0(A_69,B_70),B_70) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_583,plain,(
    ! [A_61] : k4_xboole_0(k1_xboole_0,A_61) = k4_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_560])).

tff(c_854,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_583])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_277,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_292,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_277])).

tff(c_885,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_292])).

tff(c_24,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_982,plain,(
    ! [A_101,B_102,C_103] :
      ( r1_tarski(k2_tarski(A_101,B_102),C_103)
      | ~ r2_hidden(B_102,C_103)
      | ~ r2_hidden(A_101,C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1998,plain,(
    ! [A_147,C_148] :
      ( r1_tarski(k1_tarski(A_147),C_148)
      | ~ r2_hidden(A_147,C_148)
      | ~ r2_hidden(A_147,C_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_982])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3283,plain,(
    ! [A_168,C_169] :
      ( k3_xboole_0(k1_tarski(A_168),C_169) = k1_tarski(A_168)
      | ~ r2_hidden(A_168,C_169) ) ),
    inference(resolution,[status(thm)],[c_1998,c_14])).

tff(c_3300,plain,(
    ! [A_168,C_169] :
      ( k5_xboole_0(k1_tarski(A_168),k1_tarski(A_168)) = k4_xboole_0(k1_tarski(A_168),C_169)
      | ~ r2_hidden(A_168,C_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3283,c_10])).

tff(c_3363,plain,(
    ! [A_170,C_171] :
      ( k4_xboole_0(k1_tarski(A_170),C_171) = k1_xboole_0
      | ~ r2_hidden(A_170,C_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_3300])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3400,plain,(
    ! [C_171,A_170] :
      ( k2_xboole_0(C_171,k1_tarski(A_170)) = k2_xboole_0(C_171,k1_xboole_0)
      | ~ r2_hidden(A_170,C_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3363,c_16])).

tff(c_3446,plain,(
    ! [C_172,A_173] :
      ( k2_xboole_0(C_172,k1_tarski(A_173)) = C_172
      | ~ r2_hidden(A_173,C_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3400])).

tff(c_257,plain,(
    ! [B_57,A_56] : k2_xboole_0(B_57,A_56) = k2_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_32])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_301,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_40])).

tff(c_3562,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3446,c_301])).

tff(c_3651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.75  
% 3.74/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.76  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.74/1.76  
% 3.74/1.76  %Foreground sorts:
% 3.74/1.76  
% 3.74/1.76  
% 3.74/1.76  %Background operators:
% 3.74/1.76  
% 3.74/1.76  
% 3.74/1.76  %Foreground operators:
% 3.74/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.74/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.74/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.74/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.74/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.76  
% 3.74/1.77  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.74/1.77  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.74/1.77  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.74/1.77  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.74/1.77  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.74/1.77  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.74/1.77  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.74/1.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.74/1.77  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.74/1.77  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.74/1.77  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.74/1.77  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.74/1.77  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.74/1.77  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.74/1.77  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.77  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.77  tff(c_134, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.74/1.77  tff(c_251, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_22, c_134])).
% 3.74/1.77  tff(c_32, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.74/1.77  tff(c_302, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_251, c_32])).
% 3.74/1.77  tff(c_330, plain, (![A_61]: (k2_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_302, c_12])).
% 3.74/1.77  tff(c_414, plain, (![A_64, B_65]: (k2_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.74/1.77  tff(c_421, plain, (![B_65]: (k4_xboole_0(B_65, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_65))), inference(superposition, [status(thm), theory('equality')], [c_414, c_330])).
% 3.74/1.77  tff(c_436, plain, (![B_65]: (k4_xboole_0(B_65, k1_xboole_0)=B_65)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_421])).
% 3.74/1.77  tff(c_361, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_302, c_12])).
% 3.74/1.77  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.74/1.77  tff(c_186, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.77  tff(c_197, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(resolution, [status(thm)], [c_20, c_186])).
% 3.74/1.77  tff(c_442, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_361, c_197])).
% 3.74/1.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.77  tff(c_510, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_442, c_2])).
% 3.74/1.77  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.77  tff(c_518, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k4_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_510, c_10])).
% 3.74/1.77  tff(c_548, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_436, c_518])).
% 3.74/1.77  tff(c_447, plain, (![A_66]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_442, c_10])).
% 3.74/1.77  tff(c_853, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_548, c_447])).
% 3.74/1.77  tff(c_560, plain, (![A_69, B_70]: (k4_xboole_0(k2_xboole_0(A_69, B_70), B_70)=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.77  tff(c_583, plain, (![A_61]: (k4_xboole_0(k1_xboole_0, A_61)=k4_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_330, c_560])).
% 3.74/1.77  tff(c_854, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_853, c_583])).
% 3.74/1.77  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.77  tff(c_198, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_186])).
% 3.74/1.77  tff(c_277, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.77  tff(c_292, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_198, c_277])).
% 3.74/1.77  tff(c_885, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_854, c_292])).
% 3.74/1.77  tff(c_24, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.74/1.77  tff(c_982, plain, (![A_101, B_102, C_103]: (r1_tarski(k2_tarski(A_101, B_102), C_103) | ~r2_hidden(B_102, C_103) | ~r2_hidden(A_101, C_103))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.77  tff(c_1998, plain, (![A_147, C_148]: (r1_tarski(k1_tarski(A_147), C_148) | ~r2_hidden(A_147, C_148) | ~r2_hidden(A_147, C_148))), inference(superposition, [status(thm), theory('equality')], [c_24, c_982])).
% 3.74/1.77  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.77  tff(c_3283, plain, (![A_168, C_169]: (k3_xboole_0(k1_tarski(A_168), C_169)=k1_tarski(A_168) | ~r2_hidden(A_168, C_169))), inference(resolution, [status(thm)], [c_1998, c_14])).
% 3.74/1.77  tff(c_3300, plain, (![A_168, C_169]: (k5_xboole_0(k1_tarski(A_168), k1_tarski(A_168))=k4_xboole_0(k1_tarski(A_168), C_169) | ~r2_hidden(A_168, C_169))), inference(superposition, [status(thm), theory('equality')], [c_3283, c_10])).
% 3.74/1.77  tff(c_3363, plain, (![A_170, C_171]: (k4_xboole_0(k1_tarski(A_170), C_171)=k1_xboole_0 | ~r2_hidden(A_170, C_171))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_3300])).
% 3.74/1.77  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.74/1.77  tff(c_3400, plain, (![C_171, A_170]: (k2_xboole_0(C_171, k1_tarski(A_170))=k2_xboole_0(C_171, k1_xboole_0) | ~r2_hidden(A_170, C_171))), inference(superposition, [status(thm), theory('equality')], [c_3363, c_16])).
% 3.74/1.77  tff(c_3446, plain, (![C_172, A_173]: (k2_xboole_0(C_172, k1_tarski(A_173))=C_172 | ~r2_hidden(A_173, C_172))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3400])).
% 3.74/1.77  tff(c_257, plain, (![B_57, A_56]: (k2_xboole_0(B_57, A_56)=k2_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_251, c_32])).
% 3.74/1.77  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.74/1.77  tff(c_301, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_40])).
% 3.74/1.77  tff(c_3562, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3446, c_301])).
% 3.74/1.77  tff(c_3651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3562])).
% 3.74/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.77  
% 3.74/1.77  Inference rules
% 3.74/1.77  ----------------------
% 3.74/1.77  #Ref     : 0
% 3.74/1.77  #Sup     : 855
% 3.74/1.77  #Fact    : 0
% 3.74/1.77  #Define  : 0
% 3.74/1.77  #Split   : 0
% 3.74/1.77  #Chain   : 0
% 3.74/1.77  #Close   : 0
% 3.74/1.77  
% 3.74/1.77  Ordering : KBO
% 3.74/1.77  
% 3.74/1.77  Simplification rules
% 3.74/1.77  ----------------------
% 3.74/1.77  #Subsume      : 45
% 3.74/1.77  #Demod        : 927
% 3.74/1.77  #Tautology    : 665
% 3.74/1.77  #SimpNegUnit  : 0
% 3.74/1.77  #BackRed      : 6
% 3.74/1.77  
% 3.74/1.77  #Partial instantiations: 0
% 3.74/1.77  #Strategies tried      : 1
% 3.74/1.77  
% 3.74/1.77  Timing (in seconds)
% 3.74/1.77  ----------------------
% 3.74/1.77  Preprocessing        : 0.32
% 3.74/1.77  Parsing              : 0.18
% 3.74/1.77  CNF conversion       : 0.02
% 3.74/1.77  Main loop            : 0.62
% 3.74/1.77  Inferencing          : 0.21
% 3.74/1.77  Reduction            : 0.28
% 3.74/1.77  Demodulation         : 0.23
% 3.74/1.77  BG Simplification    : 0.02
% 3.74/1.77  Subsumption          : 0.08
% 3.74/1.78  Abstraction          : 0.03
% 3.74/1.78  MUC search           : 0.00
% 3.74/1.78  Cooper               : 0.00
% 3.74/1.78  Total                : 0.97
% 3.74/1.78  Index Insertion      : 0.00
% 3.74/1.78  Index Deletion       : 0.00
% 3.74/1.78  Index Matching       : 0.00
% 3.74/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
