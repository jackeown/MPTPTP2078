%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:54 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  86 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k3_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_tarski(A_20,k3_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [B_23,C_24] : r1_tarski(k3_xboole_0(B_23,C_24),B_23) ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_334,plain,(
    ! [B_49,C_50] :
      ( k3_xboole_0(B_49,C_50) = B_49
      | ~ r1_tarski(B_49,k3_xboole_0(B_49,C_50)) ) ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_341,plain,(
    ! [B_9,C_10] :
      ( k3_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_334])).

tff(c_370,plain,(
    ! [B_53,C_54] :
      ( k3_xboole_0(B_53,C_54) = B_53
      | ~ r1_tarski(B_53,C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_341])).

tff(c_409,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_370])).

tff(c_539,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_409])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_410,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_370])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12,D_14] : k3_xboole_0(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,D_14)) = k2_zfmisc_1(k3_xboole_0(A_11,B_12),k3_xboole_0(C_13,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_548,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_21])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  %$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.56/1.38  
% 2.56/1.38  %Foreground sorts:
% 2.56/1.38  
% 2.56/1.38  
% 2.56/1.38  %Background operators:
% 2.56/1.38  
% 2.56/1.38  
% 2.56/1.38  %Foreground operators:
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.38  
% 2.56/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.56/1.39  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 2.56/1.39  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.39  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.56/1.39  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.56/1.39  tff(f_45, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.56/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.39  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.39  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.39  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k3_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.56/1.39  tff(c_70, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, B_21) | ~r1_tarski(A_20, k3_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.39  tff(c_84, plain, (![B_23, C_24]: (r1_tarski(k3_xboole_0(B_23, C_24), B_23))), inference(resolution, [status(thm)], [c_8, c_70])).
% 2.56/1.39  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.39  tff(c_334, plain, (![B_49, C_50]: (k3_xboole_0(B_49, C_50)=B_49 | ~r1_tarski(B_49, k3_xboole_0(B_49, C_50)))), inference(resolution, [status(thm)], [c_84, c_4])).
% 2.56/1.39  tff(c_341, plain, (![B_9, C_10]: (k3_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_334])).
% 2.56/1.39  tff(c_370, plain, (![B_53, C_54]: (k3_xboole_0(B_53, C_54)=B_53 | ~r1_tarski(B_53, C_54))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_341])).
% 2.56/1.39  tff(c_409, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_370])).
% 2.56/1.39  tff(c_539, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_409])).
% 2.56/1.39  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.39  tff(c_410, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_370])).
% 2.56/1.39  tff(c_14, plain, (![A_11, C_13, B_12, D_14]: (k3_xboole_0(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, D_14))=k2_zfmisc_1(k3_xboole_0(A_11, B_12), k3_xboole_0(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.39  tff(c_16, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.39  tff(c_21, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.56/1.39  tff(c_548, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_21])).
% 2.56/1.39  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_539, c_548])).
% 2.56/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  Inference rules
% 2.56/1.39  ----------------------
% 2.56/1.39  #Ref     : 0
% 2.56/1.39  #Sup     : 235
% 2.56/1.39  #Fact    : 0
% 2.56/1.39  #Define  : 0
% 2.56/1.39  #Split   : 2
% 2.56/1.39  #Chain   : 0
% 2.56/1.39  #Close   : 0
% 2.56/1.39  
% 2.56/1.39  Ordering : KBO
% 2.56/1.39  
% 2.56/1.39  Simplification rules
% 2.56/1.39  ----------------------
% 2.56/1.39  #Subsume      : 12
% 2.56/1.39  #Demod        : 118
% 2.56/1.39  #Tautology    : 126
% 2.56/1.39  #SimpNegUnit  : 0
% 2.56/1.39  #BackRed      : 1
% 2.56/1.39  
% 2.56/1.39  #Partial instantiations: 0
% 2.56/1.39  #Strategies tried      : 1
% 2.56/1.39  
% 2.56/1.39  Timing (in seconds)
% 2.56/1.39  ----------------------
% 2.56/1.39  Preprocessing        : 0.29
% 2.56/1.39  Parsing              : 0.15
% 2.56/1.39  CNF conversion       : 0.02
% 2.56/1.39  Main loop            : 0.35
% 2.56/1.39  Inferencing          : 0.11
% 2.56/1.39  Reduction            : 0.13
% 2.56/1.39  Demodulation         : 0.11
% 2.56/1.39  BG Simplification    : 0.02
% 2.56/1.39  Subsumption          : 0.06
% 2.56/1.39  Abstraction          : 0.02
% 2.56/1.39  MUC search           : 0.00
% 2.56/1.39  Cooper               : 0.00
% 2.56/1.39  Total                : 0.66
% 2.56/1.39  Index Insertion      : 0.00
% 2.56/1.39  Index Deletion       : 0.00
% 2.56/1.39  Index Matching       : 0.00
% 2.56/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
