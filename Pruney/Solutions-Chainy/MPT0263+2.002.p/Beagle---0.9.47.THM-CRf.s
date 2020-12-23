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
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_143,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_143,c_32])).

tff(c_28,plain,(
    ! [B_43,A_42] :
      ( k3_xboole_0(B_43,k1_tarski(A_42)) = k1_tarski(A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_26,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_163,plain,(
    ! [B_57,A_56] : k2_xboole_0(B_57,A_56) = k2_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_26])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k5_xboole_0(k5_xboole_0(A_3,B_4),C_5) = k5_xboole_0(A_3,k5_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_272,plain,(
    ! [A_68,B_69] : k5_xboole_0(k5_xboole_0(A_68,B_69),k2_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_558,plain,(
    ! [A_79,B_80] : k5_xboole_0(k5_xboole_0(A_79,B_80),k2_xboole_0(B_80,A_79)) = k3_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_272])).

tff(c_1124,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k5_xboole_0(B_109,k2_xboole_0(B_109,A_108))) = k3_xboole_0(B_109,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_558])).

tff(c_3077,plain,(
    ! [B_126,A_127] : k5_xboole_0(B_126,k5_xboole_0(A_127,k2_xboole_0(B_126,A_127))) = k3_xboole_0(A_127,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1124])).

tff(c_284,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k5_xboole_0(B_69,k2_xboole_0(A_68,B_69))) = k3_xboole_0(A_68,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_4])).

tff(c_3142,plain,(
    ! [B_126,A_127] : k3_xboole_0(B_126,A_127) = k3_xboole_0(A_127,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_3077,c_284])).

tff(c_30,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3248,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_30])).

tff(c_4073,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3248])).

tff(c_4077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_4073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.01/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.44  
% 7.01/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.45  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 7.01/2.45  
% 7.01/2.45  %Foreground sorts:
% 7.01/2.45  
% 7.01/2.45  
% 7.01/2.45  %Background operators:
% 7.01/2.45  
% 7.01/2.45  
% 7.01/2.45  %Foreground operators:
% 7.01/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.01/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.01/2.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.01/2.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.01/2.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.01/2.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.01/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.01/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.01/2.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.01/2.45  tff('#skF_2', type, '#skF_2': $i).
% 7.01/2.45  tff('#skF_1', type, '#skF_1': $i).
% 7.01/2.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.01/2.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.01/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.01/2.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.01/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.01/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.01/2.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.01/2.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.01/2.45  
% 7.24/2.46  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.24/2.46  tff(f_63, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 7.24/2.46  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 7.24/2.46  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.24/2.46  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.24/2.46  tff(f_29, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.24/2.46  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.24/2.46  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.24/2.46  tff(c_143, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.24/2.46  tff(c_32, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.24/2.46  tff(c_147, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_143, c_32])).
% 7.24/2.46  tff(c_28, plain, (![B_43, A_42]: (k3_xboole_0(B_43, k1_tarski(A_42))=k1_tarski(A_42) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.24/2.46  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.24/2.46  tff(c_108, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.24/2.46  tff(c_157, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_8, c_108])).
% 7.24/2.46  tff(c_26, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.24/2.46  tff(c_163, plain, (![B_57, A_56]: (k2_xboole_0(B_57, A_56)=k2_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_157, c_26])).
% 7.24/2.46  tff(c_4, plain, (![A_3, B_4, C_5]: (k5_xboole_0(k5_xboole_0(A_3, B_4), C_5)=k5_xboole_0(A_3, k5_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.24/2.46  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.24/2.46  tff(c_272, plain, (![A_68, B_69]: (k5_xboole_0(k5_xboole_0(A_68, B_69), k2_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.24/2.46  tff(c_558, plain, (![A_79, B_80]: (k5_xboole_0(k5_xboole_0(A_79, B_80), k2_xboole_0(B_80, A_79))=k3_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_272])).
% 7.24/2.46  tff(c_1124, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k5_xboole_0(B_109, k2_xboole_0(B_109, A_108)))=k3_xboole_0(B_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_4, c_558])).
% 7.24/2.46  tff(c_3077, plain, (![B_126, A_127]: (k5_xboole_0(B_126, k5_xboole_0(A_127, k2_xboole_0(B_126, A_127)))=k3_xboole_0(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1124])).
% 7.24/2.46  tff(c_284, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k5_xboole_0(B_69, k2_xboole_0(A_68, B_69)))=k3_xboole_0(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_272, c_4])).
% 7.24/2.46  tff(c_3142, plain, (![B_126, A_127]: (k3_xboole_0(B_126, A_127)=k3_xboole_0(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_3077, c_284])).
% 7.24/2.46  tff(c_30, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.24/2.46  tff(c_3248, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_30])).
% 7.24/2.46  tff(c_4073, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_3248])).
% 7.24/2.46  tff(c_4077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_4073])).
% 7.24/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.24/2.46  
% 7.24/2.46  Inference rules
% 7.24/2.46  ----------------------
% 7.24/2.46  #Ref     : 0
% 7.24/2.46  #Sup     : 1075
% 7.24/2.46  #Fact    : 0
% 7.24/2.46  #Define  : 0
% 7.24/2.46  #Split   : 0
% 7.24/2.46  #Chain   : 0
% 7.24/2.46  #Close   : 0
% 7.24/2.46  
% 7.24/2.46  Ordering : KBO
% 7.24/2.46  
% 7.24/2.46  Simplification rules
% 7.24/2.46  ----------------------
% 7.24/2.46  #Subsume      : 56
% 7.24/2.46  #Demod        : 908
% 7.24/2.46  #Tautology    : 223
% 7.24/2.46  #SimpNegUnit  : 0
% 7.24/2.46  #BackRed      : 1
% 7.24/2.46  
% 7.24/2.46  #Partial instantiations: 0
% 7.24/2.46  #Strategies tried      : 1
% 7.24/2.46  
% 7.24/2.46  Timing (in seconds)
% 7.24/2.46  ----------------------
% 7.24/2.46  Preprocessing        : 0.29
% 7.24/2.46  Parsing              : 0.15
% 7.24/2.46  CNF conversion       : 0.02
% 7.24/2.46  Main loop            : 1.40
% 7.24/2.46  Inferencing          : 0.30
% 7.24/2.46  Reduction            : 0.88
% 7.24/2.46  Demodulation         : 0.83
% 7.24/2.46  BG Simplification    : 0.05
% 7.24/2.46  Subsumption          : 0.11
% 7.24/2.46  Abstraction          : 0.07
% 7.24/2.46  MUC search           : 0.00
% 7.24/2.46  Cooper               : 0.00
% 7.24/2.46  Total                : 1.71
% 7.24/2.46  Index Insertion      : 0.00
% 7.24/2.46  Index Deletion       : 0.00
% 7.24/2.46  Index Matching       : 0.00
% 7.24/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
