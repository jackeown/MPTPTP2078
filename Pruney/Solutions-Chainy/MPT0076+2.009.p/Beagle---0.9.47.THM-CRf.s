%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:33 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  57 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_95,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_xboole_0(A_34,C_35)
      | ~ r1_xboole_0(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_174,plain,(
    ! [A_42] :
      ( r1_xboole_0(A_42,'#skF_4')
      | ~ r1_tarski(A_42,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_76])).

tff(c_102,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_16])).

tff(c_123,plain,(
    ! [A_38] : k3_xboole_0(A_38,A_38) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_26,B_27] :
      ( ~ r1_xboole_0(A_26,B_27)
      | v1_xboole_0(k3_xboole_0(A_26,B_27)) ) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_129,plain,(
    ! [A_38] :
      ( ~ r1_xboole_0(A_38,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_63])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_129])).

tff(c_185,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_178])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.85/1.19  
% 1.85/1.19  %Foreground sorts:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Background operators:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Foreground operators:
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.85/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.19  
% 1.85/1.20  tff(f_70, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.85/1.20  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.85/1.20  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.85/1.20  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.85/1.20  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.85/1.20  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.85/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.85/1.20  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.85/1.20  tff(c_24, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.85/1.20  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.85/1.20  tff(c_20, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.85/1.20  tff(c_47, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.20  tff(c_50, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_47])).
% 1.85/1.20  tff(c_95, plain, (![A_34, C_35, B_36]: (r1_xboole_0(A_34, C_35) | ~r1_xboole_0(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.20  tff(c_174, plain, (![A_42]: (r1_xboole_0(A_42, '#skF_4') | ~r1_tarski(A_42, '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_95])).
% 1.85/1.20  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.20  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.20  tff(c_76, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.20  tff(c_91, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_76])).
% 1.85/1.20  tff(c_102, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_91])).
% 1.85/1.20  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.20  tff(c_107, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_102, c_16])).
% 1.85/1.20  tff(c_123, plain, (![A_38]: (k3_xboole_0(A_38, A_38)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_107])).
% 1.85/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.20  tff(c_55, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.20  tff(c_63, plain, (![A_26, B_27]: (~r1_xboole_0(A_26, B_27) | v1_xboole_0(k3_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_4, c_55])).
% 1.85/1.20  tff(c_129, plain, (![A_38]: (~r1_xboole_0(A_38, A_38) | v1_xboole_0(A_38))), inference(superposition, [status(thm), theory('equality')], [c_123, c_63])).
% 1.85/1.20  tff(c_178, plain, (v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_174, c_129])).
% 1.85/1.20  tff(c_185, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_178])).
% 1.85/1.20  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_185])).
% 1.85/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  Inference rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Ref     : 0
% 1.85/1.20  #Sup     : 38
% 1.85/1.20  #Fact    : 0
% 1.85/1.20  #Define  : 0
% 1.85/1.20  #Split   : 2
% 1.85/1.20  #Chain   : 0
% 1.85/1.20  #Close   : 0
% 1.85/1.20  
% 1.85/1.20  Ordering : KBO
% 1.85/1.20  
% 1.85/1.20  Simplification rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Subsume      : 2
% 1.85/1.20  #Demod        : 5
% 1.85/1.20  #Tautology    : 17
% 1.85/1.20  #SimpNegUnit  : 1
% 1.85/1.20  #BackRed      : 0
% 1.85/1.20  
% 1.85/1.20  #Partial instantiations: 0
% 1.85/1.20  #Strategies tried      : 1
% 1.85/1.20  
% 1.85/1.20  Timing (in seconds)
% 1.85/1.20  ----------------------
% 1.85/1.20  Preprocessing        : 0.25
% 1.85/1.20  Parsing              : 0.14
% 1.85/1.20  CNF conversion       : 0.02
% 1.85/1.20  Main loop            : 0.15
% 1.85/1.20  Inferencing          : 0.07
% 1.85/1.20  Reduction            : 0.04
% 1.85/1.20  Demodulation         : 0.03
% 1.85/1.20  BG Simplification    : 0.01
% 1.85/1.20  Subsumption          : 0.02
% 1.85/1.20  Abstraction          : 0.01
% 1.85/1.20  MUC search           : 0.00
% 1.85/1.20  Cooper               : 0.00
% 1.85/1.20  Total                : 0.43
% 1.85/1.20  Index Insertion      : 0.00
% 1.85/1.20  Index Deletion       : 0.00
% 1.85/1.20  Index Matching       : 0.00
% 1.85/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
