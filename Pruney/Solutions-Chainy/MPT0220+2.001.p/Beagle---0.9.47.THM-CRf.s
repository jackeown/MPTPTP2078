%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k1_tarski(A_17),k2_tarski(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [A_24,B_23] : r1_tarski(A_24,k2_xboole_0(B_23,A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_12])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k2_xboole_0(A_40,C_41),k2_xboole_0(B_42,C_41))
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,(
    ! [A_43,A_44] :
      ( r1_tarski(k2_xboole_0(A_43,A_44),A_44)
      | ~ r1_tarski(A_43,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_166])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [A_43,A_44] :
      ( k2_xboole_0(A_43,A_44) = A_44
      | ~ r1_tarski(A_44,k2_xboole_0(A_43,A_44))
      | ~ r1_tarski(A_43,A_44) ) ),
    inference(resolution,[status(thm)],[c_200,c_6])).

tff(c_239,plain,(
    ! [A_45,A_46] :
      ( k2_xboole_0(A_45,A_46) = A_46
      | ~ r1_tarski(A_45,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_216])).

tff(c_261,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k2_tarski(A_17,B_18)) = k2_tarski(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_20,c_239])).

tff(c_22,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.59  
% 3.17/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.59  %$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 3.17/1.59  
% 3.17/1.59  %Foreground sorts:
% 3.17/1.59  
% 3.17/1.59  
% 3.17/1.59  %Background operators:
% 3.17/1.59  
% 3.17/1.59  
% 3.17/1.59  %Foreground operators:
% 3.17/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.59  
% 3.17/1.60  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.17/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.17/1.60  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.17/1.60  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.17/1.60  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.17/1.60  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.60  tff(f_50, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 3.17/1.60  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), k2_tarski(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.60  tff(c_39, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.17/1.60  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.60  tff(c_54, plain, (![A_24, B_23]: (r1_tarski(A_24, k2_xboole_0(B_23, A_24)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_12])).
% 3.17/1.60  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.60  tff(c_166, plain, (![A_40, C_41, B_42]: (r1_tarski(k2_xboole_0(A_40, C_41), k2_xboole_0(B_42, C_41)) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.17/1.60  tff(c_200, plain, (![A_43, A_44]: (r1_tarski(k2_xboole_0(A_43, A_44), A_44) | ~r1_tarski(A_43, A_44))), inference(superposition, [status(thm), theory('equality')], [c_4, c_166])).
% 3.17/1.60  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.60  tff(c_216, plain, (![A_43, A_44]: (k2_xboole_0(A_43, A_44)=A_44 | ~r1_tarski(A_44, k2_xboole_0(A_43, A_44)) | ~r1_tarski(A_43, A_44))), inference(resolution, [status(thm)], [c_200, c_6])).
% 3.17/1.60  tff(c_239, plain, (![A_45, A_46]: (k2_xboole_0(A_45, A_46)=A_46 | ~r1_tarski(A_45, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_216])).
% 3.17/1.60  tff(c_261, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(A_17, B_18))=k2_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_20, c_239])).
% 3.17/1.60  tff(c_22, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.60  tff(c_1820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_22])).
% 3.17/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.60  
% 3.17/1.60  Inference rules
% 3.17/1.60  ----------------------
% 3.17/1.60  #Ref     : 0
% 3.17/1.60  #Sup     : 447
% 3.17/1.60  #Fact    : 0
% 3.17/1.60  #Define  : 0
% 3.17/1.60  #Split   : 0
% 3.17/1.60  #Chain   : 0
% 3.17/1.60  #Close   : 0
% 3.17/1.60  
% 3.17/1.60  Ordering : KBO
% 3.17/1.60  
% 3.17/1.60  Simplification rules
% 3.17/1.60  ----------------------
% 3.17/1.60  #Subsume      : 66
% 3.17/1.60  #Demod        : 433
% 3.17/1.60  #Tautology    : 225
% 3.17/1.60  #SimpNegUnit  : 0
% 3.17/1.60  #BackRed      : 1
% 3.17/1.60  
% 3.17/1.60  #Partial instantiations: 0
% 3.17/1.60  #Strategies tried      : 1
% 3.17/1.60  
% 3.17/1.60  Timing (in seconds)
% 3.17/1.60  ----------------------
% 3.17/1.60  Preprocessing        : 0.30
% 3.17/1.60  Parsing              : 0.16
% 3.17/1.60  CNF conversion       : 0.02
% 3.17/1.60  Main loop            : 0.49
% 3.17/1.60  Inferencing          : 0.15
% 3.17/1.60  Reduction            : 0.21
% 3.17/1.60  Demodulation         : 0.18
% 3.17/1.60  BG Simplification    : 0.02
% 3.17/1.60  Subsumption          : 0.08
% 3.17/1.60  Abstraction          : 0.03
% 3.17/1.60  MUC search           : 0.00
% 3.17/1.60  Cooper               : 0.00
% 3.17/1.60  Total                : 0.81
% 3.17/1.60  Index Insertion      : 0.00
% 3.17/1.60  Index Deletion       : 0.00
% 3.17/1.60  Index Matching       : 0.00
% 3.17/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
