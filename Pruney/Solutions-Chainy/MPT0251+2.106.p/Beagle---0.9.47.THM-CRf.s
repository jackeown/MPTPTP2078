%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   38 (  61 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_36,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [B_44,A_43] :
      ( k3_xboole_0(B_44,k1_tarski(A_43)) = k1_tarski(A_43)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [B_51,A_52] : k5_xboole_0(B_51,A_52) = k5_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_52] : k5_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_285,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_265])).

tff(c_289,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_285])).

tff(c_556,plain,(
    ! [A_83,B_84,C_85] : k5_xboole_0(k5_xboole_0(A_83,B_84),C_85) = k5_xboole_0(A_83,k5_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_604,plain,(
    ! [A_5,C_85] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_85)) = k5_xboole_0(k1_xboole_0,C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_556])).

tff(c_656,plain,(
    ! [A_86,C_87] : k5_xboole_0(A_86,k5_xboole_0(A_86,C_87)) = C_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_604])).

tff(c_1068,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k4_xboole_0(A_109,B_110)) = k3_xboole_0(A_109,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_656])).

tff(c_708,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_656])).

tff(c_1521,plain,(
    ! [A_128,B_129] : k5_xboole_0(k4_xboole_0(A_128,B_129),k3_xboole_0(A_128,B_129)) = A_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_708])).

tff(c_1563,plain,(
    ! [B_44,A_43] :
      ( k5_xboole_0(k4_xboole_0(B_44,k1_tarski(A_43)),k1_tarski(A_43)) = B_44
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1521])).

tff(c_4745,plain,(
    ! [A_167,B_168] :
      ( k2_xboole_0(k1_tarski(A_167),B_168) = B_168
      | ~ r2_hidden(A_167,B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_1563])).

tff(c_34,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4829,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4745,c_34])).

tff(c_4861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.93  
% 4.84/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.93  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.84/1.93  
% 4.84/1.93  %Foreground sorts:
% 4.84/1.93  
% 4.84/1.93  
% 4.84/1.93  %Background operators:
% 4.84/1.93  
% 4.84/1.93  
% 4.84/1.93  %Foreground operators:
% 4.84/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.84/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.84/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.84/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.84/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.84/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.84/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.84/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.84/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.84/1.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.84/1.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.84/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.84/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.84/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.84/1.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.84/1.93  
% 4.84/1.94  tff(f_64, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.84/1.94  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.84/1.94  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.84/1.94  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 4.84/1.94  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.84/1.94  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.84/1.94  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.84/1.94  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.84/1.94  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.84/1.94  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.84/1.94  tff(c_14, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.94  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.84/1.94  tff(c_30, plain, (![B_44, A_43]: (k3_xboole_0(B_44, k1_tarski(A_43))=k1_tarski(A_43) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.84/1.94  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.84/1.94  tff(c_64, plain, (![B_51, A_52]: (k5_xboole_0(B_51, A_52)=k5_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.84/1.94  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.84/1.94  tff(c_80, plain, (![A_52]: (k5_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_64, c_10])).
% 4.84/1.94  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.84/1.94  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/1.94  tff(c_265, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.84/1.94  tff(c_285, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_265])).
% 4.84/1.94  tff(c_289, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_285])).
% 4.84/1.94  tff(c_556, plain, (![A_83, B_84, C_85]: (k5_xboole_0(k5_xboole_0(A_83, B_84), C_85)=k5_xboole_0(A_83, k5_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.84/1.94  tff(c_604, plain, (![A_5, C_85]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_85))=k5_xboole_0(k1_xboole_0, C_85))), inference(superposition, [status(thm), theory('equality')], [c_289, c_556])).
% 4.84/1.94  tff(c_656, plain, (![A_86, C_87]: (k5_xboole_0(A_86, k5_xboole_0(A_86, C_87))=C_87)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_604])).
% 4.84/1.94  tff(c_1068, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k4_xboole_0(A_109, B_110))=k3_xboole_0(A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_4, c_656])).
% 4.84/1.94  tff(c_708, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_656])).
% 4.84/1.94  tff(c_1521, plain, (![A_128, B_129]: (k5_xboole_0(k4_xboole_0(A_128, B_129), k3_xboole_0(A_128, B_129))=A_128)), inference(superposition, [status(thm), theory('equality')], [c_1068, c_708])).
% 4.84/1.94  tff(c_1563, plain, (![B_44, A_43]: (k5_xboole_0(k4_xboole_0(B_44, k1_tarski(A_43)), k1_tarski(A_43))=B_44 | ~r2_hidden(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1521])).
% 4.84/1.94  tff(c_4745, plain, (![A_167, B_168]: (k2_xboole_0(k1_tarski(A_167), B_168)=B_168 | ~r2_hidden(A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_1563])).
% 4.84/1.94  tff(c_34, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.84/1.94  tff(c_4829, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4745, c_34])).
% 4.84/1.94  tff(c_4861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_4829])).
% 4.84/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.94  
% 4.84/1.94  Inference rules
% 4.84/1.94  ----------------------
% 4.84/1.94  #Ref     : 0
% 4.84/1.94  #Sup     : 1222
% 4.84/1.94  #Fact    : 0
% 4.84/1.94  #Define  : 0
% 4.84/1.94  #Split   : 0
% 4.84/1.94  #Chain   : 0
% 4.84/1.94  #Close   : 0
% 4.84/1.94  
% 4.84/1.94  Ordering : KBO
% 4.84/1.94  
% 4.84/1.94  Simplification rules
% 4.84/1.94  ----------------------
% 4.84/1.94  #Subsume      : 61
% 4.84/1.94  #Demod        : 1099
% 4.84/1.94  #Tautology    : 677
% 4.84/1.94  #SimpNegUnit  : 0
% 4.84/1.94  #BackRed      : 0
% 4.84/1.94  
% 4.84/1.94  #Partial instantiations: 0
% 4.84/1.94  #Strategies tried      : 1
% 4.84/1.94  
% 4.84/1.94  Timing (in seconds)
% 4.84/1.94  ----------------------
% 4.84/1.95  Preprocessing        : 0.30
% 4.84/1.95  Parsing              : 0.16
% 4.84/1.95  CNF conversion       : 0.02
% 4.84/1.95  Main loop            : 0.87
% 4.84/1.95  Inferencing          : 0.28
% 4.84/1.95  Reduction            : 0.42
% 4.84/1.95  Demodulation         : 0.36
% 4.84/1.95  BG Simplification    : 0.03
% 4.84/1.95  Subsumption          : 0.10
% 4.84/1.95  Abstraction          : 0.05
% 4.84/1.95  MUC search           : 0.00
% 4.84/1.95  Cooper               : 0.00
% 4.84/1.95  Total                : 1.20
% 4.84/1.95  Index Insertion      : 0.00
% 4.84/1.95  Index Deletion       : 0.00
% 4.84/1.95  Index Matching       : 0.00
% 4.84/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
