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
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_39,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [D_8,A_3] : r2_hidden(D_8,k2_tarski(A_3,D_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_6])).

tff(c_118,plain,(
    ! [B_40,C_41,A_42] :
      ( ~ r2_hidden(B_40,C_41)
      | k4_xboole_0(k2_tarski(A_42,B_40),C_41) = k1_tarski(A_42)
      | r2_hidden(A_42,C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_34])).

tff(c_142,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_130])).

tff(c_22,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [D_27,B_28,A_29] :
      ( D_27 = B_28
      | D_27 = A_29
      | ~ r2_hidden(D_27,k2_tarski(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [D_27,A_9] :
      ( D_27 = A_9
      | D_27 = A_9
      | ~ r2_hidden(D_27,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_84])).

tff(c_147,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_90])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.87/1.20  
% 1.87/1.20  %Foreground sorts:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Background operators:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Foreground operators:
% 1.87/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.20  
% 1.93/1.20  tff(f_55, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.93/1.20  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.20  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.20  tff(f_49, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.93/1.20  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.20  tff(c_39, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.20  tff(c_6, plain, (![D_8, A_3]: (r2_hidden(D_8, k2_tarski(A_3, D_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.20  tff(c_45, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_6])).
% 1.93/1.20  tff(c_118, plain, (![B_40, C_41, A_42]: (~r2_hidden(B_40, C_41) | k4_xboole_0(k2_tarski(A_42, B_40), C_41)=k1_tarski(A_42) | r2_hidden(A_42, C_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.20  tff(c_34, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.20  tff(c_130, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_34])).
% 1.93/1.20  tff(c_142, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_130])).
% 1.93/1.20  tff(c_22, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.20  tff(c_84, plain, (![D_27, B_28, A_29]: (D_27=B_28 | D_27=A_29 | ~r2_hidden(D_27, k2_tarski(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.20  tff(c_90, plain, (![D_27, A_9]: (D_27=A_9 | D_27=A_9 | ~r2_hidden(D_27, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_84])).
% 1.93/1.20  tff(c_147, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_142, c_90])).
% 1.93/1.20  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_147])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 24
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
% 1.93/1.20  #Subsume      : 1
% 1.93/1.20  #Demod        : 3
% 1.93/1.20  #Tautology    : 18
% 1.93/1.20  #SimpNegUnit  : 1
% 1.93/1.20  #BackRed      : 0
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.21  Preprocessing        : 0.29
% 1.93/1.21  Parsing              : 0.14
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.13
% 1.93/1.21  Inferencing          : 0.04
% 1.93/1.21  Reduction            : 0.04
% 1.93/1.21  Demodulation         : 0.03
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.03
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.44
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
