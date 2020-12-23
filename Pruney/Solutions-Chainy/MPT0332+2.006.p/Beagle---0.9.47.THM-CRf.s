%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:48 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 112 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 ( 103 expanded)
%              Number of equality atoms :   39 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [C_50,A_48,B_49] :
      ( k4_xboole_0(C_50,k2_tarski(A_48,B_49)) = C_50
      | r2_hidden(B_49,C_50)
      | r2_hidden(A_48,C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [B_62,A_63] : k3_tarski(k2_tarski(B_62,A_63)) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_141])).

tff(c_32,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_162,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_32])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,B_16),k2_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_471,plain,(
    ! [A_80,B_81,C_82] : k5_xboole_0(k5_xboole_0(A_80,B_81),C_82) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3985,plain,(
    ! [A_161,B_162] : k5_xboole_0(A_161,k5_xboole_0(B_162,k2_xboole_0(A_161,B_162))) = k3_xboole_0(A_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_471])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_317,plain,(
    ! [A_76,B_77] : k5_xboole_0(k5_xboole_0(A_76,B_77),k2_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_365,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_14,A_14)) = k3_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_317])).

tff(c_373,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_365])).

tff(c_548,plain,(
    ! [A_14,C_82] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_82)) = k5_xboole_0(k1_xboole_0,C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_471])).

tff(c_561,plain,(
    ! [A_14,C_82] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_548])).

tff(c_4025,plain,(
    ! [B_162,A_161] : k5_xboole_0(B_162,k2_xboole_0(A_161,B_162)) = k5_xboole_0(A_161,k3_xboole_0(A_161,B_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3985,c_561])).

tff(c_4131,plain,(
    ! [B_163,A_164] : k5_xboole_0(B_163,k2_xboole_0(A_164,B_163)) = k4_xboole_0(A_164,B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4025])).

tff(c_4228,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,k2_xboole_0(B_62,A_63)) = k4_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_4131])).

tff(c_213,plain,(
    ! [A_66,B_67] : k2_xboole_0(A_66,k2_xboole_0(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_231,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,k2_xboole_0(A_63,B_62)) = k2_xboole_0(B_62,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_213])).

tff(c_4784,plain,(
    ! [B_171,A_172] : k5_xboole_0(B_171,k2_xboole_0(B_171,A_172)) = k4_xboole_0(A_172,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_4131])).

tff(c_4886,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,k2_xboole_0(B_62,A_63)) = k4_xboole_0(k2_xboole_0(A_63,B_62),B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_4784])).

tff(c_4919,plain,(
    ! [A_63,B_62] : k4_xboole_0(k2_xboole_0(A_63,B_62),B_62) = k4_xboole_0(A_63,B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4228,c_4886])).

tff(c_36,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7062,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4919,c_36])).

tff(c_7168,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_7062])).

tff(c_7172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_7168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.35  
% 5.74/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.35  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.74/2.35  
% 5.74/2.35  %Foreground sorts:
% 5.74/2.35  
% 5.74/2.35  
% 5.74/2.35  %Background operators:
% 5.74/2.35  
% 5.74/2.35  
% 5.74/2.35  %Foreground operators:
% 5.74/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.74/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.74/2.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.74/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.74/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.74/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.74/2.35  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.35  tff('#skF_3', type, '#skF_3': $i).
% 5.74/2.35  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.74/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.74/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.74/2.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.74/2.35  
% 5.74/2.36  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 5.74/2.36  tff(f_67, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 5.74/2.36  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.74/2.36  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.74/2.36  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.74/2.36  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.74/2.36  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.74/2.36  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.74/2.36  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.74/2.36  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.74/2.36  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.74/2.36  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.74/2.36  tff(c_38, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.74/2.36  tff(c_34, plain, (![C_50, A_48, B_49]: (k4_xboole_0(C_50, k2_tarski(A_48, B_49))=C_50 | r2_hidden(B_49, C_50) | r2_hidden(A_48, C_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.74/2.36  tff(c_18, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.74/2.36  tff(c_141, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.36  tff(c_156, plain, (![B_62, A_63]: (k3_tarski(k2_tarski(B_62, A_63))=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_18, c_141])).
% 5.74/2.36  tff(c_32, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.36  tff(c_162, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_156, c_32])).
% 5.74/2.36  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.74/2.36  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, B_16), k2_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.36  tff(c_471, plain, (![A_80, B_81, C_82]: (k5_xboole_0(k5_xboole_0(A_80, B_81), C_82)=k5_xboole_0(A_80, k5_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.36  tff(c_3985, plain, (![A_161, B_162]: (k5_xboole_0(A_161, k5_xboole_0(B_162, k2_xboole_0(A_161, B_162)))=k3_xboole_0(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_16, c_471])).
% 5.74/2.36  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.74/2.36  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.74/2.36  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.74/2.36  tff(c_317, plain, (![A_76, B_77]: (k5_xboole_0(k5_xboole_0(A_76, B_77), k2_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.74/2.36  tff(c_365, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_14, A_14))=k3_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_317])).
% 5.74/2.36  tff(c_373, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_365])).
% 5.74/2.36  tff(c_548, plain, (![A_14, C_82]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_82))=k5_xboole_0(k1_xboole_0, C_82))), inference(superposition, [status(thm), theory('equality')], [c_14, c_471])).
% 5.74/2.36  tff(c_561, plain, (![A_14, C_82]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_373, c_548])).
% 5.74/2.36  tff(c_4025, plain, (![B_162, A_161]: (k5_xboole_0(B_162, k2_xboole_0(A_161, B_162))=k5_xboole_0(A_161, k3_xboole_0(A_161, B_162)))), inference(superposition, [status(thm), theory('equality')], [c_3985, c_561])).
% 5.74/2.36  tff(c_4131, plain, (![B_163, A_164]: (k5_xboole_0(B_163, k2_xboole_0(A_164, B_163))=k4_xboole_0(A_164, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4025])).
% 5.74/2.36  tff(c_4228, plain, (![B_62, A_63]: (k5_xboole_0(B_62, k2_xboole_0(B_62, A_63))=k4_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_162, c_4131])).
% 5.74/2.36  tff(c_213, plain, (![A_66, B_67]: (k2_xboole_0(A_66, k2_xboole_0(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.74/2.36  tff(c_231, plain, (![B_62, A_63]: (k2_xboole_0(B_62, k2_xboole_0(A_63, B_62))=k2_xboole_0(B_62, A_63))), inference(superposition, [status(thm), theory('equality')], [c_162, c_213])).
% 5.74/2.36  tff(c_4784, plain, (![B_171, A_172]: (k5_xboole_0(B_171, k2_xboole_0(B_171, A_172))=k4_xboole_0(A_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_162, c_4131])).
% 5.74/2.36  tff(c_4886, plain, (![B_62, A_63]: (k5_xboole_0(B_62, k2_xboole_0(B_62, A_63))=k4_xboole_0(k2_xboole_0(A_63, B_62), B_62))), inference(superposition, [status(thm), theory('equality')], [c_231, c_4784])).
% 5.74/2.36  tff(c_4919, plain, (![A_63, B_62]: (k4_xboole_0(k2_xboole_0(A_63, B_62), B_62)=k4_xboole_0(A_63, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_4228, c_4886])).
% 5.74/2.36  tff(c_36, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.74/2.36  tff(c_7062, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4919, c_36])).
% 5.74/2.36  tff(c_7168, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_7062])).
% 5.74/2.36  tff(c_7172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_7168])).
% 5.74/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.36  
% 5.74/2.36  Inference rules
% 5.74/2.36  ----------------------
% 5.74/2.36  #Ref     : 0
% 5.74/2.36  #Sup     : 1780
% 5.74/2.36  #Fact    : 0
% 5.74/2.36  #Define  : 0
% 5.74/2.36  #Split   : 1
% 5.74/2.36  #Chain   : 0
% 5.74/2.36  #Close   : 0
% 5.74/2.36  
% 5.74/2.36  Ordering : KBO
% 5.74/2.36  
% 5.74/2.36  Simplification rules
% 5.74/2.36  ----------------------
% 5.74/2.36  #Subsume      : 70
% 5.74/2.36  #Demod        : 1757
% 5.74/2.36  #Tautology    : 955
% 5.74/2.36  #SimpNegUnit  : 1
% 5.74/2.36  #BackRed      : 2
% 5.74/2.36  
% 5.74/2.36  #Partial instantiations: 0
% 5.74/2.36  #Strategies tried      : 1
% 5.74/2.36  
% 5.74/2.36  Timing (in seconds)
% 5.74/2.36  ----------------------
% 5.74/2.37  Preprocessing        : 0.35
% 5.74/2.37  Parsing              : 0.16
% 5.74/2.37  CNF conversion       : 0.03
% 5.74/2.37  Main loop            : 1.18
% 5.74/2.37  Inferencing          : 0.33
% 5.74/2.37  Reduction            : 0.60
% 5.74/2.37  Demodulation         : 0.52
% 5.74/2.37  BG Simplification    : 0.05
% 5.74/2.37  Subsumption          : 0.15
% 5.74/2.37  Abstraction          : 0.07
% 5.74/2.37  MUC search           : 0.00
% 5.74/2.37  Cooper               : 0.00
% 5.74/2.37  Total                : 1.56
% 5.74/2.37  Index Insertion      : 0.00
% 5.74/2.37  Index Deletion       : 0.00
% 5.74/2.37  Index Matching       : 0.00
% 5.74/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
