%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  45 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_30,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_294,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_tarski(A_66,B_67),C_68)
      | ~ r2_hidden(B_67,C_68)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_313,plain,(
    ! [A_69,C_70] :
      ( r1_tarski(k1_tarski(A_69),C_70)
      | ~ r2_hidden(A_69,C_70)
      | ~ r2_hidden(A_69,C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_338,plain,(
    ! [A_74,C_75] :
      ( k2_xboole_0(k1_tarski(A_74),C_75) = C_75
      | ~ r2_hidden(A_74,C_75) ) ),
    inference(resolution,[status(thm)],[c_313,c_28])).

tff(c_42,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_390,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_42])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_228,plain,(
    ! [B_53,C_54,A_55] :
      ( r2_hidden(B_53,C_54)
      | ~ r1_tarski(k2_tarski(A_55,B_53),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_237,plain,(
    ! [B_56,A_57] : r2_hidden(B_56,k2_tarski(A_57,B_56)) ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_61,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_61])).

tff(c_184,plain,(
    ! [D_40,B_41,A_42] :
      ( ~ r2_hidden(D_40,B_41)
      | r2_hidden(D_40,k2_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_187,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_184])).

tff(c_245,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_237,c_187])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.30  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.11/1.30  
% 2.11/1.30  %Foreground sorts:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Background operators:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Foreground operators:
% 2.11/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.30  
% 2.11/1.31  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.31  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.11/1.31  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.11/1.31  tff(f_61, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.11/1.31  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.31  tff(f_65, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.11/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.11/1.31  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.11/1.31  tff(c_30, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.31  tff(c_294, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_tarski(A_66, B_67), C_68) | ~r2_hidden(B_67, C_68) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.31  tff(c_313, plain, (![A_69, C_70]: (r1_tarski(k1_tarski(A_69), C_70) | ~r2_hidden(A_69, C_70) | ~r2_hidden(A_69, C_70))), inference(superposition, [status(thm), theory('equality')], [c_30, c_294])).
% 2.11/1.31  tff(c_28, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.31  tff(c_338, plain, (![A_74, C_75]: (k2_xboole_0(k1_tarski(A_74), C_75)=C_75 | ~r2_hidden(A_74, C_75))), inference(resolution, [status(thm)], [c_313, c_28])).
% 2.11/1.31  tff(c_42, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.11/1.31  tff(c_390, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_338, c_42])).
% 2.11/1.31  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.11/1.31  tff(c_228, plain, (![B_53, C_54, A_55]: (r2_hidden(B_53, C_54) | ~r1_tarski(k2_tarski(A_55, B_53), C_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.31  tff(c_237, plain, (![B_56, A_57]: (r2_hidden(B_56, k2_tarski(A_57, B_56)))), inference(resolution, [status(thm)], [c_26, c_228])).
% 2.11/1.31  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.31  tff(c_61, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.31  tff(c_102, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_44, c_61])).
% 2.11/1.31  tff(c_184, plain, (![D_40, B_41, A_42]: (~r2_hidden(D_40, B_41) | r2_hidden(D_40, k2_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.31  tff(c_187, plain, (![D_40]: (~r2_hidden(D_40, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_102, c_184])).
% 2.11/1.31  tff(c_245, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_187])).
% 2.11/1.31  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_245])).
% 2.11/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  Inference rules
% 2.11/1.31  ----------------------
% 2.11/1.31  #Ref     : 0
% 2.11/1.31  #Sup     : 85
% 2.11/1.31  #Fact    : 0
% 2.11/1.31  #Define  : 0
% 2.11/1.31  #Split   : 0
% 2.11/1.31  #Chain   : 0
% 2.11/1.31  #Close   : 0
% 2.11/1.31  
% 2.11/1.31  Ordering : KBO
% 2.11/1.31  
% 2.11/1.31  Simplification rules
% 2.11/1.31  ----------------------
% 2.11/1.31  #Subsume      : 12
% 2.11/1.31  #Demod        : 10
% 2.11/1.31  #Tautology    : 43
% 2.11/1.31  #SimpNegUnit  : 4
% 2.11/1.31  #BackRed      : 4
% 2.11/1.31  
% 2.11/1.31  #Partial instantiations: 0
% 2.11/1.31  #Strategies tried      : 1
% 2.11/1.31  
% 2.11/1.31  Timing (in seconds)
% 2.11/1.31  ----------------------
% 2.41/1.31  Preprocessing        : 0.31
% 2.41/1.31  Parsing              : 0.15
% 2.41/1.31  CNF conversion       : 0.02
% 2.41/1.31  Main loop            : 0.25
% 2.41/1.31  Inferencing          : 0.08
% 2.41/1.31  Reduction            : 0.09
% 2.41/1.31  Demodulation         : 0.07
% 2.41/1.31  BG Simplification    : 0.02
% 2.41/1.32  Subsumption          : 0.05
% 2.41/1.32  Abstraction          : 0.01
% 2.41/1.32  MUC search           : 0.00
% 2.41/1.32  Cooper               : 0.00
% 2.41/1.32  Total                : 0.59
% 2.41/1.32  Index Insertion      : 0.00
% 2.41/1.32  Index Deletion       : 0.00
% 2.41/1.32  Index Matching       : 0.00
% 2.41/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
