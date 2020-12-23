%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:55 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  46 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_128,plain,(
    ! [A_28,B_29] :
      ( ~ r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_132,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_128])).

tff(c_164,plain,(
    ! [A_33,B_34] : k2_xboole_0(k3_xboole_0(A_33,B_34),k4_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_176,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_164])).

tff(c_35,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_23] : k2_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_10])).

tff(c_182,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_51])).

tff(c_486,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(k4_xboole_0(A_43,B_44),C_45)
      | ~ r1_tarski(A_43,k2_xboole_0(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_535,plain,(
    ! [C_47] :
      ( r1_tarski('#skF_3',C_47)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_486])).

tff(c_760,plain,(
    ! [B_53] :
      ( r1_tarski('#skF_3',B_53)
      | ~ r1_tarski('#skF_3',k2_xboole_0(B_53,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_535])).

tff(c_783,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_760])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.23/1.33  
% 2.23/1.33  %Foreground sorts:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Background operators:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Foreground operators:
% 2.23/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.33  
% 2.23/1.34  tff(f_68, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.23/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.23/1.34  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.23/1.34  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/1.34  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.23/1.34  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.23/1.34  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.23/1.34  tff(c_20, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.34  tff(c_24, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.34  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.34  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.34  tff(c_121, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.34  tff(c_128, plain, (![A_28, B_29]: (~r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_121])).
% 2.23/1.34  tff(c_132, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_128])).
% 2.23/1.34  tff(c_164, plain, (![A_33, B_34]: (k2_xboole_0(k3_xboole_0(A_33, B_34), k4_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.34  tff(c_176, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_132, c_164])).
% 2.23/1.34  tff(c_35, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.34  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.34  tff(c_51, plain, (![A_23]: (k2_xboole_0(k1_xboole_0, A_23)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_35, c_10])).
% 2.23/1.34  tff(c_182, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_176, c_51])).
% 2.23/1.34  tff(c_486, plain, (![A_43, B_44, C_45]: (r1_tarski(k4_xboole_0(A_43, B_44), C_45) | ~r1_tarski(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.34  tff(c_535, plain, (![C_47]: (r1_tarski('#skF_3', C_47) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_47)))), inference(superposition, [status(thm), theory('equality')], [c_182, c_486])).
% 2.23/1.34  tff(c_760, plain, (![B_53]: (r1_tarski('#skF_3', B_53) | ~r1_tarski('#skF_3', k2_xboole_0(B_53, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_535])).
% 2.23/1.34  tff(c_783, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_760])).
% 2.23/1.34  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_783])).
% 2.23/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  Inference rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Ref     : 0
% 2.23/1.34  #Sup     : 192
% 2.23/1.34  #Fact    : 0
% 2.23/1.34  #Define  : 0
% 2.23/1.34  #Split   : 2
% 2.23/1.34  #Chain   : 0
% 2.23/1.34  #Close   : 0
% 2.23/1.34  
% 2.23/1.34  Ordering : KBO
% 2.23/1.34  
% 2.23/1.34  Simplification rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Subsume      : 7
% 2.23/1.34  #Demod        : 132
% 2.23/1.34  #Tautology    : 139
% 2.23/1.34  #SimpNegUnit  : 5
% 2.23/1.34  #BackRed      : 2
% 2.23/1.34  
% 2.23/1.34  #Partial instantiations: 0
% 2.23/1.34  #Strategies tried      : 1
% 2.23/1.34  
% 2.23/1.34  Timing (in seconds)
% 2.23/1.34  ----------------------
% 2.23/1.34  Preprocessing        : 0.27
% 2.23/1.34  Parsing              : 0.15
% 2.23/1.34  CNF conversion       : 0.02
% 2.23/1.34  Main loop            : 0.31
% 2.23/1.34  Inferencing          : 0.11
% 2.23/1.34  Reduction            : 0.12
% 2.53/1.34  Demodulation         : 0.09
% 2.53/1.34  BG Simplification    : 0.01
% 2.53/1.34  Subsumption          : 0.04
% 2.53/1.34  Abstraction          : 0.01
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.61
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
