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
% DateTime   : Thu Dec  3 09:51:18 EST 2020

% Result     : Theorem 12.62s
% Output     : CNFRefutation 12.62s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  75 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_551,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(k2_tarski(A_94,B_95),C_96)
      | ~ r2_hidden(B_95,C_96)
      | ~ r2_hidden(A_94,C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5221,plain,(
    ! [A_168,B_169,C_170] :
      ( k4_xboole_0(k2_tarski(A_168,B_169),C_170) = k1_xboole_0
      | ~ r2_hidden(B_169,C_170)
      | ~ r2_hidden(A_168,C_170) ) ),
    inference(resolution,[status(thm)],[c_551,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_381,plain,(
    ! [A_85,B_86] : k5_xboole_0(k5_xboole_0(A_85,B_86),k3_xboole_0(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_393,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k5_xboole_0(B_86,k3_xboole_0(A_85,B_86))) = k2_xboole_0(A_85,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_14])).

tff(c_445,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_393])).

tff(c_5238,plain,(
    ! [C_170,A_168,B_169] :
      ( k2_xboole_0(C_170,k2_tarski(A_168,B_169)) = k5_xboole_0(C_170,k1_xboole_0)
      | ~ r2_hidden(B_169,C_170)
      | ~ r2_hidden(A_168,C_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5221,c_445])).

tff(c_22535,plain,(
    ! [C_255,A_256,B_257] :
      ( k2_xboole_0(C_255,k2_tarski(A_256,B_257)) = C_255
      | ~ r2_hidden(B_257,C_255)
      | ~ r2_hidden(A_256,C_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5238])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_303,plain,(
    ! [A_79,B_80,C_81] : k5_xboole_0(k5_xboole_0(A_79,B_80),C_81) = k5_xboole_0(A_79,k5_xboole_0(B_80,C_81)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1365,plain,(
    ! [B_132,A_133,B_134] : k5_xboole_0(B_132,k5_xboole_0(A_133,B_134)) = k5_xboole_0(A_133,k5_xboole_0(B_134,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_303])).

tff(c_399,plain,(
    ! [A_85,B_86] : k5_xboole_0(k3_xboole_0(A_85,B_86),k5_xboole_0(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_4])).

tff(c_1428,plain,(
    ! [B_132,B_134] : k5_xboole_0(B_132,k5_xboole_0(k3_xboole_0(B_134,B_132),B_134)) = k2_xboole_0(B_134,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_1365,c_399])).

tff(c_1695,plain,(
    ! [B_134,B_132] : k2_xboole_0(B_134,B_132) = k2_xboole_0(B_132,B_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_10,c_4,c_1428])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1727,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_38])).

tff(c_22563,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22535,c_1727])).

tff(c_22595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_22563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.62/6.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.62/6.02  
% 12.62/6.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.62/6.02  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.62/6.02  
% 12.62/6.02  %Foreground sorts:
% 12.62/6.02  
% 12.62/6.02  
% 12.62/6.02  %Background operators:
% 12.62/6.02  
% 12.62/6.02  
% 12.62/6.02  %Foreground operators:
% 12.62/6.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.62/6.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.62/6.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.62/6.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.62/6.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.62/6.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.62/6.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.62/6.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.62/6.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.62/6.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.62/6.02  tff('#skF_2', type, '#skF_2': $i).
% 12.62/6.02  tff('#skF_3', type, '#skF_3': $i).
% 12.62/6.02  tff('#skF_1', type, '#skF_1': $i).
% 12.62/6.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.62/6.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.62/6.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.62/6.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.62/6.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.62/6.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.62/6.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.62/6.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.62/6.02  
% 12.62/6.04  tff(f_68, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 12.62/6.04  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.62/6.04  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 12.62/6.04  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.62/6.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.62/6.04  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.62/6.04  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.62/6.04  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.62/6.04  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.62/6.04  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.62/6.04  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.62/6.04  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.62/6.04  tff(c_551, plain, (![A_94, B_95, C_96]: (r1_tarski(k2_tarski(A_94, B_95), C_96) | ~r2_hidden(B_95, C_96) | ~r2_hidden(A_94, C_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.62/6.04  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.62/6.04  tff(c_5221, plain, (![A_168, B_169, C_170]: (k4_xboole_0(k2_tarski(A_168, B_169), C_170)=k1_xboole_0 | ~r2_hidden(B_169, C_170) | ~r2_hidden(A_168, C_170))), inference(resolution, [status(thm)], [c_551, c_8])).
% 12.62/6.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.62/6.04  tff(c_208, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.62/6.04  tff(c_224, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 12.62/6.04  tff(c_381, plain, (![A_85, B_86]: (k5_xboole_0(k5_xboole_0(A_85, B_86), k3_xboole_0(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.62/6.04  tff(c_14, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.62/6.04  tff(c_393, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k5_xboole_0(B_86, k3_xboole_0(A_85, B_86)))=k2_xboole_0(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_381, c_14])).
% 12.62/6.04  tff(c_445, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_393])).
% 12.62/6.04  tff(c_5238, plain, (![C_170, A_168, B_169]: (k2_xboole_0(C_170, k2_tarski(A_168, B_169))=k5_xboole_0(C_170, k1_xboole_0) | ~r2_hidden(B_169, C_170) | ~r2_hidden(A_168, C_170))), inference(superposition, [status(thm), theory('equality')], [c_5221, c_445])).
% 12.62/6.04  tff(c_22535, plain, (![C_255, A_256, B_257]: (k2_xboole_0(C_255, k2_tarski(A_256, B_257))=C_255 | ~r2_hidden(B_257, C_255) | ~r2_hidden(A_256, C_255))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5238])).
% 12.62/6.04  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.62/6.04  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.62/6.04  tff(c_303, plain, (![A_79, B_80, C_81]: (k5_xboole_0(k5_xboole_0(A_79, B_80), C_81)=k5_xboole_0(A_79, k5_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.62/6.04  tff(c_1365, plain, (![B_132, A_133, B_134]: (k5_xboole_0(B_132, k5_xboole_0(A_133, B_134))=k5_xboole_0(A_133, k5_xboole_0(B_134, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_303])).
% 12.62/6.04  tff(c_399, plain, (![A_85, B_86]: (k5_xboole_0(k3_xboole_0(A_85, B_86), k5_xboole_0(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_381, c_4])).
% 12.62/6.04  tff(c_1428, plain, (![B_132, B_134]: (k5_xboole_0(B_132, k5_xboole_0(k3_xboole_0(B_134, B_132), B_134))=k2_xboole_0(B_134, B_132))), inference(superposition, [status(thm), theory('equality')], [c_1365, c_399])).
% 12.62/6.04  tff(c_1695, plain, (![B_134, B_132]: (k2_xboole_0(B_134, B_132)=k2_xboole_0(B_132, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_10, c_4, c_1428])).
% 12.62/6.04  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.62/6.04  tff(c_1727, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_38])).
% 12.62/6.04  tff(c_22563, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22535, c_1727])).
% 12.62/6.04  tff(c_22595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_22563])).
% 12.62/6.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.62/6.04  
% 12.62/6.04  Inference rules
% 12.62/6.04  ----------------------
% 12.62/6.04  #Ref     : 0
% 12.62/6.04  #Sup     : 5819
% 12.62/6.04  #Fact    : 0
% 12.62/6.04  #Define  : 0
% 12.62/6.04  #Split   : 0
% 12.62/6.04  #Chain   : 0
% 12.62/6.04  #Close   : 0
% 12.62/6.04  
% 12.62/6.04  Ordering : KBO
% 12.62/6.04  
% 12.62/6.04  Simplification rules
% 12.62/6.04  ----------------------
% 12.62/6.04  #Subsume      : 673
% 12.62/6.04  #Demod        : 5223
% 12.62/6.04  #Tautology    : 1090
% 12.62/6.04  #SimpNegUnit  : 0
% 12.62/6.04  #BackRed      : 1
% 12.62/6.04  
% 12.62/6.04  #Partial instantiations: 0
% 12.62/6.04  #Strategies tried      : 1
% 12.62/6.04  
% 12.62/6.04  Timing (in seconds)
% 12.62/6.04  ----------------------
% 12.62/6.04  Preprocessing        : 0.31
% 12.62/6.04  Parsing              : 0.16
% 12.62/6.04  CNF conversion       : 0.02
% 12.62/6.04  Main loop            : 4.94
% 12.62/6.04  Inferencing          : 0.74
% 12.62/6.04  Reduction            : 3.39
% 12.62/6.04  Demodulation         : 3.19
% 12.62/6.04  BG Simplification    : 0.14
% 12.62/6.04  Subsumption          : 0.51
% 12.62/6.04  Abstraction          : 0.21
% 12.62/6.04  MUC search           : 0.00
% 12.62/6.04  Cooper               : 0.00
% 12.62/6.04  Total                : 5.28
% 12.62/6.04  Index Insertion      : 0.00
% 12.62/6.04  Index Deletion       : 0.00
% 12.62/6.04  Index Matching       : 0.00
% 12.62/6.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
