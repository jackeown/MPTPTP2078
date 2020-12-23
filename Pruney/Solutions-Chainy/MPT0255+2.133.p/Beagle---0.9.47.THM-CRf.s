%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:55 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  45 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k8_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k8_enumset1,type,(
    k8_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J,K] :
      ( K = k8_enumset1(A,B,C,D,E,F,G,H,I,J)
    <=> ! [L] :
          ( r2_hidden(L,K)
        <=> ~ ( L != A
              & L != B
              & L != C
              & L != D
              & L != E
              & L != F
              & L != G
              & L != H
              & L != I
              & L != J ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_enumset1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_203,plain,(
    ! [E_61,D_52,I_53,L_60,A_59,B_57,J_56,F_54,C_58,G_55] : r2_hidden(L_60,k8_enumset1(A_59,B_57,C_58,D_52,E_61,F_54,G_55,L_60,I_53,J_56)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103,plain,(
    ! [A_26,B_27] :
      ( k1_xboole_0 = A_26
      | k2_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_103])).

tff(c_113,plain,(
    ! [A_28,B_29] : k3_xboole_0(k1_tarski(A_28),k2_tarski(A_28,B_29)) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_122,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_113])).

tff(c_125,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_122])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [A_31,C_32,B_33] :
      ( ~ r2_hidden(A_31,C_32)
      | k4_xboole_0(k2_tarski(A_31,B_33),C_32) != k1_tarski(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_156,plain,(
    ! [C_32] :
      ( ~ r2_hidden('#skF_3',C_32)
      | k4_xboole_0(k1_xboole_0,C_32) != k1_tarski('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_153])).

tff(c_158,plain,(
    ! [C_32] : ~ r2_hidden('#skF_3',C_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_6,c_156])).

tff(c_208,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_203,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  %$ r2_hidden > k8_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4
% 2.69/1.38  
% 2.69/1.38  %Foreground sorts:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Background operators:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Foreground operators:
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.38  tff(k8_enumset1, type, k8_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.38  
% 2.69/1.39  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I, J, K]: ((K = k8_enumset1(A, B, C, D, E, F, G, H, I, J)) <=> (![L]: (r2_hidden(L, K) <=> ~(((((((((~(L = A) & ~(L = B)) & ~(L = C)) & ~(L = D)) & ~(L = E)) & ~(L = F)) & ~(L = G)) & ~(L = H)) & ~(L = I)) & ~(L = J)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_enumset1)).
% 2.69/1.39  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.69/1.39  tff(f_84, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.69/1.39  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.69/1.39  tff(f_80, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.69/1.39  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.69/1.39  tff(f_78, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.69/1.39  tff(c_203, plain, (![E_61, D_52, I_53, L_60, A_59, B_57, J_56, F_54, C_58, G_55]: (r2_hidden(L_60, k8_enumset1(A_59, B_57, C_58, D_52, E_61, F_54, G_55, L_60, I_53, J_56)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.39  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.39  tff(c_84, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.39  tff(c_103, plain, (![A_26, B_27]: (k1_xboole_0=A_26 | k2_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.39  tff(c_107, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_84, c_103])).
% 2.69/1.39  tff(c_113, plain, (![A_28, B_29]: (k3_xboole_0(k1_tarski(A_28), k2_tarski(A_28, B_29))=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.39  tff(c_122, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_113])).
% 2.69/1.39  tff(c_125, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_122])).
% 2.69/1.39  tff(c_6, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.39  tff(c_153, plain, (![A_31, C_32, B_33]: (~r2_hidden(A_31, C_32) | k4_xboole_0(k2_tarski(A_31, B_33), C_32)!=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.39  tff(c_156, plain, (![C_32]: (~r2_hidden('#skF_3', C_32) | k4_xboole_0(k1_xboole_0, C_32)!=k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_153])).
% 2.69/1.39  tff(c_158, plain, (![C_32]: (~r2_hidden('#skF_3', C_32))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_6, c_156])).
% 2.69/1.39  tff(c_208, plain, $false, inference(resolution, [status(thm)], [c_203, c_158])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 31
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 1
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 0
% 2.69/1.39  #Demod        : 12
% 2.69/1.39  #Tautology    : 24
% 2.69/1.39  #SimpNegUnit  : 0
% 2.69/1.39  #BackRed      : 5
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 3.00/1.39  Preprocessing        : 0.36
% 3.00/1.39  Parsing              : 0.17
% 3.00/1.39  CNF conversion       : 0.03
% 3.00/1.39  Main loop            : 0.25
% 3.00/1.39  Inferencing          : 0.05
% 3.00/1.39  Reduction            : 0.06
% 3.00/1.39  Demodulation         : 0.05
% 3.00/1.39  BG Simplification    : 0.02
% 3.00/1.39  Subsumption          : 0.11
% 3.00/1.39  Abstraction          : 0.03
% 3.00/1.39  MUC search           : 0.00
% 3.00/1.39  Cooper               : 0.00
% 3.00/1.39  Total                : 0.64
% 3.00/1.39  Index Insertion      : 0.00
% 3.00/1.39  Index Deletion       : 0.00
% 3.00/1.39  Index Matching       : 0.00
% 3.00/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
