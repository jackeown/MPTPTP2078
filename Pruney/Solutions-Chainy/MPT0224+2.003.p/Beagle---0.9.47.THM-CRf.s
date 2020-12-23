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
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 183 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 241 expanded)
%              Number of equality atoms :   40 ( 163 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,k3_xboole_0(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_16])).

tff(c_388,plain,(
    ! [A_53,B_54] : k3_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_190])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_184])).

tff(c_397,plain,(
    ! [A_53,B_54] : k4_xboole_0(k3_xboole_0(A_53,B_54),k3_xboole_0(A_53,B_54)) = k4_xboole_0(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_202])).

tff(c_432,plain,(
    ! [A_53,B_54] : k4_xboole_0(k3_xboole_0(A_53,B_54),A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_397])).

tff(c_132,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_132])).

tff(c_199,plain,(
    ! [B_4] : k4_xboole_0(B_4,k4_xboole_0(B_4,k1_xboole_0)) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_184])).

tff(c_210,plain,(
    ! [B_4] : k3_xboole_0(B_4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_86,c_199])).

tff(c_153,plain,(
    ! [B_42] : k4_xboole_0(B_42,k1_xboole_0) = k3_xboole_0(B_42,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_132])).

tff(c_162,plain,(
    ! [B_42] : k4_xboole_0(B_42,k3_xboole_0(B_42,B_42)) = k3_xboole_0(B_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_16])).

tff(c_813,plain,(
    ! [B_42] : k4_xboole_0(B_42,k3_xboole_0(B_42,B_42)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_162])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_716,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | k4_xboole_0(A_68,B_67) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_119])).

tff(c_1375,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | k4_xboole_0(B_82,A_83) != k1_xboole_0
      | k4_xboole_0(A_83,B_82) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_716])).

tff(c_1385,plain,(
    ! [B_42] :
      ( k3_xboole_0(B_42,B_42) = B_42
      | k4_xboole_0(k3_xboole_0(B_42,B_42),B_42) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_1375])).

tff(c_1419,plain,(
    ! [B_42] : k3_xboole_0(B_42,B_42) = B_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_1385])).

tff(c_814,plain,(
    ! [B_71] : k4_xboole_0(B_71,k3_xboole_0(B_71,B_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_162])).

tff(c_828,plain,(
    ! [B_71] : k3_xboole_0(B_71,k3_xboole_0(B_71,B_71)) = k4_xboole_0(B_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_16])).

tff(c_1443,plain,(
    ! [B_71] : k4_xboole_0(B_71,k1_xboole_0) = B_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1419,c_1419,c_828])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k1_tarski(A_21),k2_tarski(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [A_21,B_22] : k4_xboole_0(k1_tarski(A_21),k2_tarski(A_21,B_22)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_147,plain,(
    ! [A_21,B_22] : k3_xboole_0(k1_tarski(A_21),k2_tarski(A_21,B_22)) = k4_xboole_0(k1_tarski(A_21),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_132])).

tff(c_28,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1331,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_28])).

tff(c_1515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_1331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.50  
% 2.93/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.51  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.93/1.51  
% 2.93/1.51  %Foreground sorts:
% 2.93/1.51  
% 2.93/1.51  
% 2.93/1.51  %Background operators:
% 2.93/1.51  
% 2.93/1.51  
% 2.93/1.51  %Foreground operators:
% 2.93/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.51  
% 2.93/1.52  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.52  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.93/1.52  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.93/1.52  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.93/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.93/1.52  tff(f_51, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.93/1.52  tff(f_54, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.93/1.52  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.52  tff(c_78, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.52  tff(c_86, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.93/1.52  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.52  tff(c_184, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.52  tff(c_190, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_16])).
% 2.93/1.52  tff(c_388, plain, (![A_53, B_54]: (k3_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_190])).
% 2.93/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.52  tff(c_202, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_184])).
% 2.93/1.52  tff(c_397, plain, (![A_53, B_54]: (k4_xboole_0(k3_xboole_0(A_53, B_54), k3_xboole_0(A_53, B_54))=k4_xboole_0(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_388, c_202])).
% 2.93/1.52  tff(c_432, plain, (![A_53, B_54]: (k4_xboole_0(k3_xboole_0(A_53, B_54), A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_397])).
% 2.93/1.52  tff(c_132, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.52  tff(c_150, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_86, c_132])).
% 2.93/1.52  tff(c_199, plain, (![B_4]: (k4_xboole_0(B_4, k4_xboole_0(B_4, k1_xboole_0))=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_150, c_184])).
% 2.93/1.52  tff(c_210, plain, (![B_4]: (k3_xboole_0(B_4, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_86, c_199])).
% 2.93/1.52  tff(c_153, plain, (![B_42]: (k4_xboole_0(B_42, k1_xboole_0)=k3_xboole_0(B_42, B_42))), inference(superposition, [status(thm), theory('equality')], [c_86, c_132])).
% 2.93/1.52  tff(c_162, plain, (![B_42]: (k4_xboole_0(B_42, k3_xboole_0(B_42, B_42))=k3_xboole_0(B_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_153, c_16])).
% 2.93/1.52  tff(c_813, plain, (![B_42]: (k4_xboole_0(B_42, k3_xboole_0(B_42, B_42))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_162])).
% 2.93/1.52  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.52  tff(c_119, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.52  tff(c_716, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | k4_xboole_0(A_68, B_67)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_119])).
% 2.93/1.52  tff(c_1375, plain, (![B_82, A_83]: (B_82=A_83 | k4_xboole_0(B_82, A_83)!=k1_xboole_0 | k4_xboole_0(A_83, B_82)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_716])).
% 2.93/1.52  tff(c_1385, plain, (![B_42]: (k3_xboole_0(B_42, B_42)=B_42 | k4_xboole_0(k3_xboole_0(B_42, B_42), B_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_813, c_1375])).
% 2.93/1.52  tff(c_1419, plain, (![B_42]: (k3_xboole_0(B_42, B_42)=B_42)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_1385])).
% 2.93/1.52  tff(c_814, plain, (![B_71]: (k4_xboole_0(B_71, k3_xboole_0(B_71, B_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_162])).
% 2.93/1.52  tff(c_828, plain, (![B_71]: (k3_xboole_0(B_71, k3_xboole_0(B_71, B_71))=k4_xboole_0(B_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_814, c_16])).
% 2.93/1.52  tff(c_1443, plain, (![B_71]: (k4_xboole_0(B_71, k1_xboole_0)=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_1419, c_1419, c_828])).
% 2.93/1.52  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), k2_tarski(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.52  tff(c_85, plain, (![A_21, B_22]: (k4_xboole_0(k1_tarski(A_21), k2_tarski(A_21, B_22))=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_78])).
% 2.93/1.52  tff(c_147, plain, (![A_21, B_22]: (k3_xboole_0(k1_tarski(A_21), k2_tarski(A_21, B_22))=k4_xboole_0(k1_tarski(A_21), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_85, c_132])).
% 2.93/1.52  tff(c_28, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.93/1.52  tff(c_1331, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_28])).
% 2.93/1.52  tff(c_1515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1443, c_1331])).
% 2.93/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.52  
% 2.93/1.52  Inference rules
% 2.93/1.52  ----------------------
% 2.93/1.52  #Ref     : 0
% 2.93/1.52  #Sup     : 352
% 2.93/1.52  #Fact    : 0
% 2.93/1.52  #Define  : 0
% 2.93/1.52  #Split   : 0
% 2.93/1.52  #Chain   : 0
% 2.93/1.52  #Close   : 0
% 2.93/1.52  
% 2.93/1.52  Ordering : KBO
% 2.93/1.52  
% 2.93/1.52  Simplification rules
% 2.93/1.52  ----------------------
% 2.93/1.52  #Subsume      : 15
% 2.93/1.52  #Demod        : 389
% 2.93/1.52  #Tautology    : 289
% 2.93/1.52  #SimpNegUnit  : 0
% 2.93/1.52  #BackRed      : 10
% 2.93/1.52  
% 2.93/1.52  #Partial instantiations: 0
% 2.93/1.52  #Strategies tried      : 1
% 2.93/1.52  
% 2.93/1.52  Timing (in seconds)
% 2.93/1.52  ----------------------
% 2.93/1.52  Preprocessing        : 0.30
% 2.93/1.52  Parsing              : 0.16
% 2.93/1.52  CNF conversion       : 0.02
% 2.93/1.52  Main loop            : 0.41
% 2.93/1.52  Inferencing          : 0.14
% 2.93/1.52  Reduction            : 0.18
% 2.93/1.52  Demodulation         : 0.15
% 2.93/1.52  BG Simplification    : 0.02
% 2.93/1.52  Subsumption          : 0.05
% 2.93/1.52  Abstraction          : 0.02
% 2.93/1.52  MUC search           : 0.00
% 2.93/1.52  Cooper               : 0.00
% 2.93/1.52  Total                : 0.74
% 2.93/1.52  Index Insertion      : 0.00
% 2.93/1.52  Index Deletion       : 0.00
% 2.93/1.52  Index Matching       : 0.00
% 2.93/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
