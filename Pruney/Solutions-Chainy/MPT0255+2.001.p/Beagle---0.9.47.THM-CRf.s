%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:39 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   44 (  90 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 (  86 expanded)
%              Number of equality atoms :   25 (  72 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_36,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_39,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).

tff(c_68,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k2_xboole_0(A_34,B_35)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_68])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_6])).

tff(c_189,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_204,plain,(
    k2_xboole_0('#skF_4','#skF_3') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_189])).

tff(c_207,plain,(
    k2_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_204])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_4])).

tff(c_16,plain,(
    ! [D_15,B_11] : r2_hidden(D_15,k2_tarski(D_15,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_16])).

tff(c_223,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_237,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:15:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.19  
% 1.93/1.20  tff(f_56, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.93/1.20  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.93/1.20  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.93/1.20  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.93/1.20  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.93/1.20  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.93/1.20  tff(f_34, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.93/1.20  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.20  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.93/1.20  tff(c_36, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.20  tff(c_10, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.20  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.20  tff(c_39, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 1.93/1.20  tff(c_68, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k2_xboole_0(A_34, B_35))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.20  tff(c_75, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_39, c_68])).
% 1.93/1.20  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.20  tff(c_81, plain, (k2_tarski('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_75, c_6])).
% 1.93/1.20  tff(c_189, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.20  tff(c_204, plain, (k2_xboole_0('#skF_4', '#skF_3')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_189])).
% 1.93/1.20  tff(c_207, plain, (k2_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_204])).
% 1.93/1.20  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.20  tff(c_217, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_207, c_4])).
% 1.93/1.20  tff(c_16, plain, (![D_15, B_11]: (r2_hidden(D_15, k2_tarski(D_15, B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.20  tff(c_103, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_16])).
% 1.93/1.20  tff(c_223, plain, (r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_103])).
% 1.93/1.20  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.93/1.20  tff(c_237, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_223, c_2])).
% 1.93/1.20  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_237])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 55
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 6
% 1.93/1.20  #Demod        : 28
% 1.93/1.20  #Tautology    : 37
% 1.93/1.20  #SimpNegUnit  : 0
% 1.93/1.20  #BackRed      : 13
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.29
% 1.93/1.21  Parsing              : 0.15
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.15
% 1.93/1.21  Inferencing          : 0.05
% 1.93/1.21  Reduction            : 0.06
% 1.93/1.21  Demodulation         : 0.05
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.03
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.47
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
