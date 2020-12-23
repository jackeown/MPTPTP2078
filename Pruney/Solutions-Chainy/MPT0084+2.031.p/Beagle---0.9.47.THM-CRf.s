%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:08 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   38 (  59 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  87 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_342,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),k3_xboole_0(A_34,B_35))
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r2_hidden(C_21,k3_xboole_0(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [B_2,A_1,C_21] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_21,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_380,plain,(
    ! [B_36,A_37] :
      ( ~ r1_xboole_0(B_36,A_37)
      | r1_xboole_0(A_37,B_36) ) ),
    inference(resolution,[status(thm)],[c_342,c_64])).

tff(c_383,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_19,c_380])).

tff(c_375,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_1'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_342])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_124,plain,(
    ! [A_27,B_28,C_29] : k3_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k3_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_173,plain,(
    ! [C_30] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_4',C_30)) = k3_xboole_0('#skF_2',C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_124])).

tff(c_1390,plain,(
    ! [C_50,C_51] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4',C_50),'#skF_2')
      | ~ r2_hidden(C_51,k3_xboole_0('#skF_2',C_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_64])).

tff(c_1557,plain,(
    ! [B_53] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4',B_53),'#skF_2')
      | r1_xboole_0(B_53,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_375,c_1390])).

tff(c_1598,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_383,c_1557])).

tff(c_376,plain,(
    ! [B_35,A_34] :
      ( ~ r1_xboole_0(B_35,A_34)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_342,c_64])).

tff(c_1600,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1598,c_376])).

tff(c_1604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:09:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.64  
% 3.25/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.25/1.64  
% 3.25/1.64  %Foreground sorts:
% 3.25/1.64  
% 3.25/1.64  
% 3.25/1.64  %Background operators:
% 3.25/1.64  
% 3.25/1.64  
% 3.25/1.64  %Foreground operators:
% 3.25/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.64  
% 3.57/1.65  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.57/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.57/1.65  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.57/1.65  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.57/1.65  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.57/1.65  tff(c_18, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.65  tff(c_14, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.65  tff(c_19, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 3.57/1.65  tff(c_342, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), k3_xboole_0(A_34, B_35)) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.65  tff(c_58, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r2_hidden(C_21, k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.65  tff(c_64, plain, (![B_2, A_1, C_21]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_21, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 3.57/1.65  tff(c_380, plain, (![B_36, A_37]: (~r1_xboole_0(B_36, A_37) | r1_xboole_0(A_37, B_36))), inference(resolution, [status(thm)], [c_342, c_64])).
% 3.57/1.65  tff(c_383, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_19, c_380])).
% 3.57/1.65  tff(c_375, plain, (![B_2, A_1]: (r2_hidden('#skF_1'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_342])).
% 3.57/1.65  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.65  tff(c_53, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.65  tff(c_57, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_53])).
% 3.57/1.65  tff(c_124, plain, (![A_27, B_28, C_29]: (k3_xboole_0(k3_xboole_0(A_27, B_28), C_29)=k3_xboole_0(A_27, k3_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.65  tff(c_173, plain, (![C_30]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_4', C_30))=k3_xboole_0('#skF_2', C_30))), inference(superposition, [status(thm), theory('equality')], [c_57, c_124])).
% 3.57/1.65  tff(c_1390, plain, (![C_50, C_51]: (~r1_xboole_0(k3_xboole_0('#skF_4', C_50), '#skF_2') | ~r2_hidden(C_51, k3_xboole_0('#skF_2', C_50)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_64])).
% 3.57/1.65  tff(c_1557, plain, (![B_53]: (~r1_xboole_0(k3_xboole_0('#skF_4', B_53), '#skF_2') | r1_xboole_0(B_53, '#skF_2'))), inference(resolution, [status(thm)], [c_375, c_1390])).
% 3.57/1.65  tff(c_1598, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_383, c_1557])).
% 3.57/1.65  tff(c_376, plain, (![B_35, A_34]: (~r1_xboole_0(B_35, A_34) | r1_xboole_0(A_34, B_35))), inference(resolution, [status(thm)], [c_342, c_64])).
% 3.57/1.65  tff(c_1600, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1598, c_376])).
% 3.57/1.65  tff(c_1604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_1600])).
% 3.57/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.65  
% 3.57/1.65  Inference rules
% 3.57/1.65  ----------------------
% 3.57/1.65  #Ref     : 0
% 3.57/1.65  #Sup     : 427
% 3.57/1.65  #Fact    : 0
% 3.57/1.65  #Define  : 0
% 3.57/1.65  #Split   : 2
% 3.57/1.65  #Chain   : 0
% 3.57/1.65  #Close   : 0
% 3.57/1.65  
% 3.57/1.65  Ordering : KBO
% 3.57/1.65  
% 3.57/1.65  Simplification rules
% 3.57/1.65  ----------------------
% 3.57/1.65  #Subsume      : 49
% 3.57/1.65  #Demod        : 201
% 3.57/1.65  #Tautology    : 159
% 3.57/1.65  #SimpNegUnit  : 5
% 3.57/1.65  #BackRed      : 0
% 3.57/1.65  
% 3.57/1.65  #Partial instantiations: 0
% 3.57/1.65  #Strategies tried      : 1
% 3.57/1.65  
% 3.57/1.65  Timing (in seconds)
% 3.57/1.65  ----------------------
% 3.57/1.65  Preprocessing        : 0.29
% 3.57/1.65  Parsing              : 0.16
% 3.57/1.65  CNF conversion       : 0.02
% 3.57/1.65  Main loop            : 0.52
% 3.57/1.65  Inferencing          : 0.16
% 3.57/1.65  Reduction            : 0.24
% 3.57/1.66  Demodulation         : 0.20
% 3.57/1.66  BG Simplification    : 0.02
% 3.57/1.66  Subsumption          : 0.07
% 3.57/1.66  Abstraction          : 0.02
% 3.57/1.66  MUC search           : 0.00
% 3.57/1.66  Cooper               : 0.00
% 3.57/1.66  Total                : 0.84
% 3.57/1.66  Index Insertion      : 0.00
% 3.57/1.66  Index Deletion       : 0.00
% 3.57/1.66  Index Matching       : 0.00
% 3.57/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
