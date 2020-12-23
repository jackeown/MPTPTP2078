%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_143,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_110,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_107])).

tff(c_153,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(A_33,B_34))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_110])).

tff(c_29,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_29])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_32,c_34])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,(
    ! [A_33,B_34,B_12] : k4_xboole_0(A_33,k2_xboole_0(B_34,k4_xboole_0(k4_xboole_0(A_33,B_34),B_12))) = k3_xboole_0(k4_xboole_0(A_33,B_34),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_3720,plain,(
    ! [A_119,B_120,B_121] : k4_xboole_0(A_119,k2_xboole_0(B_120,k4_xboole_0(A_119,k2_xboole_0(B_120,B_121)))) = k3_xboole_0(k4_xboole_0(A_119,B_120),B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_190])).

tff(c_3905,plain,(
    ! [A_119,A_7] : k4_xboole_0(A_119,k2_xboole_0(A_7,k4_xboole_0(A_119,A_7))) = k3_xboole_0(k4_xboole_0(A_119,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_3720])).

tff(c_3939,plain,(
    ! [A_119,A_7] : k3_xboole_0(k4_xboole_0(A_119,A_7),A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_3905])).

tff(c_70,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_18])).

tff(c_3942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.68  
% 3.57/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.69  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.57/1.69  
% 3.57/1.69  %Foreground sorts:
% 3.57/1.69  
% 3.57/1.69  
% 3.57/1.69  %Background operators:
% 3.57/1.69  
% 3.57/1.69  
% 3.57/1.69  %Foreground operators:
% 3.57/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.57/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.69  
% 3.84/1.70  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.84/1.70  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.84/1.70  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.84/1.70  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.84/1.70  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.84/1.70  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.84/1.70  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.84/1.70  tff(f_46, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.84/1.70  tff(c_143, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.70  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.84/1.70  tff(c_65, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.84/1.70  tff(c_69, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_65])).
% 3.84/1.70  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.84/1.70  tff(c_86, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.84/1.70  tff(c_107, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_86])).
% 3.84/1.70  tff(c_110, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_107])).
% 3.84/1.70  tff(c_153, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(A_33, B_34)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_143, c_110])).
% 3.84/1.70  tff(c_29, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.84/1.70  tff(c_32, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_29])).
% 3.84/1.70  tff(c_34, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.70  tff(c_41, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(resolution, [status(thm)], [c_32, c_34])).
% 3.84/1.70  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.70  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.84/1.70  tff(c_190, plain, (![A_33, B_34, B_12]: (k4_xboole_0(A_33, k2_xboole_0(B_34, k4_xboole_0(k4_xboole_0(A_33, B_34), B_12)))=k3_xboole_0(k4_xboole_0(A_33, B_34), B_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_143])).
% 3.84/1.70  tff(c_3720, plain, (![A_119, B_120, B_121]: (k4_xboole_0(A_119, k2_xboole_0(B_120, k4_xboole_0(A_119, k2_xboole_0(B_120, B_121))))=k3_xboole_0(k4_xboole_0(A_119, B_120), B_121))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_190])).
% 3.84/1.70  tff(c_3905, plain, (![A_119, A_7]: (k4_xboole_0(A_119, k2_xboole_0(A_7, k4_xboole_0(A_119, A_7)))=k3_xboole_0(k4_xboole_0(A_119, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_41, c_3720])).
% 3.84/1.70  tff(c_3939, plain, (![A_119, A_7]: (k3_xboole_0(k4_xboole_0(A_119, A_7), A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_3905])).
% 3.84/1.70  tff(c_70, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.84/1.70  tff(c_18, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.84/1.70  tff(c_78, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_18])).
% 3.84/1.70  tff(c_3942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3939, c_78])).
% 3.84/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.70  
% 3.84/1.70  Inference rules
% 3.84/1.70  ----------------------
% 3.84/1.70  #Ref     : 0
% 3.84/1.70  #Sup     : 949
% 3.84/1.70  #Fact    : 0
% 3.84/1.70  #Define  : 0
% 3.84/1.70  #Split   : 0
% 3.84/1.70  #Chain   : 0
% 3.84/1.70  #Close   : 0
% 3.84/1.70  
% 3.84/1.70  Ordering : KBO
% 3.84/1.70  
% 3.84/1.70  Simplification rules
% 3.84/1.70  ----------------------
% 3.84/1.70  #Subsume      : 0
% 3.84/1.70  #Demod        : 889
% 3.84/1.70  #Tautology    : 680
% 3.84/1.70  #SimpNegUnit  : 0
% 3.84/1.70  #BackRed      : 5
% 3.84/1.70  
% 3.84/1.70  #Partial instantiations: 0
% 3.84/1.70  #Strategies tried      : 1
% 3.84/1.70  
% 3.84/1.70  Timing (in seconds)
% 3.84/1.70  ----------------------
% 3.84/1.70  Preprocessing        : 0.28
% 3.84/1.70  Parsing              : 0.16
% 3.84/1.70  CNF conversion       : 0.02
% 3.84/1.70  Main loop            : 0.60
% 3.84/1.70  Inferencing          : 0.21
% 3.84/1.70  Reduction            : 0.24
% 3.84/1.70  Demodulation         : 0.19
% 3.84/1.70  BG Simplification    : 0.02
% 3.84/1.70  Subsumption          : 0.08
% 3.84/1.70  Abstraction          : 0.03
% 3.84/1.70  MUC search           : 0.00
% 3.84/1.70  Cooper               : 0.00
% 3.84/1.70  Total                : 0.90
% 3.84/1.70  Index Insertion      : 0.00
% 3.84/1.70  Index Deletion       : 0.00
% 3.84/1.70  Index Matching       : 0.00
% 3.84/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
