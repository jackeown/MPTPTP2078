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
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_28,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [D_29,B_30] : r2_hidden(D_29,k2_tarski(D_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_75])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_52])).

tff(c_205,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k4_xboole_0(A_55,B_56),C_57) = k4_xboole_0(A_55,k2_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_355,plain,(
    ! [D_67,C_68,A_69,B_70] :
      ( ~ r2_hidden(D_67,C_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_69,k2_xboole_0(B_70,C_68))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_6])).

tff(c_375,plain,(
    ! [D_67,A_69] :
      ( ~ r2_hidden(D_67,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_67,k4_xboole_0(A_69,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_355])).

tff(c_389,plain,(
    ! [D_73,A_74] :
      ( ~ r2_hidden(D_73,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_73,A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_375])).

tff(c_394,plain,(
    ! [A_75] : ~ r2_hidden('#skF_5',A_75) ),
    inference(resolution,[status(thm)],[c_78,c_389])).

tff(c_411,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_28,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.18/1.25  
% 2.18/1.25  %Foreground sorts:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Background operators:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Foreground operators:
% 2.18/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.25  
% 2.18/1.25  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.18/1.25  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.25  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.18/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.18/1.25  tff(f_62, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.18/1.25  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.18/1.25  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.18/1.25  tff(c_28, plain, (![D_18, A_13]: (r2_hidden(D_18, k2_tarski(A_13, D_18)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.25  tff(c_44, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.25  tff(c_75, plain, (![D_29, B_30]: (r2_hidden(D_29, k2_tarski(D_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.25  tff(c_78, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_75])).
% 2.18/1.25  tff(c_22, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.25  tff(c_85, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.25  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.25  tff(c_100, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_85, c_52])).
% 2.18/1.25  tff(c_205, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k4_xboole_0(A_55, B_56), C_57)=k4_xboole_0(A_55, k2_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.25  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.25  tff(c_355, plain, (![D_67, C_68, A_69, B_70]: (~r2_hidden(D_67, C_68) | ~r2_hidden(D_67, k4_xboole_0(A_69, k2_xboole_0(B_70, C_68))))), inference(superposition, [status(thm), theory('equality')], [c_205, c_6])).
% 2.18/1.25  tff(c_375, plain, (![D_67, A_69]: (~r2_hidden(D_67, k1_tarski('#skF_5')) | ~r2_hidden(D_67, k4_xboole_0(A_69, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_355])).
% 2.18/1.25  tff(c_389, plain, (![D_73, A_74]: (~r2_hidden(D_73, k1_tarski('#skF_5')) | ~r2_hidden(D_73, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_375])).
% 2.18/1.25  tff(c_394, plain, (![A_75]: (~r2_hidden('#skF_5', A_75))), inference(resolution, [status(thm)], [c_78, c_389])).
% 2.18/1.25  tff(c_411, plain, $false, inference(resolution, [status(thm)], [c_28, c_394])).
% 2.18/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  Inference rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Ref     : 0
% 2.18/1.25  #Sup     : 88
% 2.18/1.25  #Fact    : 0
% 2.18/1.25  #Define  : 0
% 2.18/1.25  #Split   : 0
% 2.18/1.25  #Chain   : 0
% 2.18/1.25  #Close   : 0
% 2.18/1.25  
% 2.18/1.25  Ordering : KBO
% 2.18/1.25  
% 2.18/1.25  Simplification rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Subsume      : 7
% 2.18/1.25  #Demod        : 25
% 2.18/1.26  #Tautology    : 48
% 2.18/1.26  #SimpNegUnit  : 1
% 2.18/1.26  #BackRed      : 0
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.30
% 2.18/1.26  Parsing              : 0.15
% 2.18/1.26  CNF conversion       : 0.02
% 2.18/1.26  Main loop            : 0.21
% 2.18/1.26  Inferencing          : 0.07
% 2.18/1.26  Reduction            : 0.08
% 2.18/1.26  Demodulation         : 0.06
% 2.18/1.26  BG Simplification    : 0.01
% 2.18/1.26  Subsumption          : 0.04
% 2.18/1.26  Abstraction          : 0.01
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.53
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
