%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_41,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [A_30] : k2_xboole_0(k1_xboole_0,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_10])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_166,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_315,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k3_xboole_0(A_51,B_52),k3_xboole_0(A_51,C_53)) = k3_xboole_0(A_51,k2_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_342,plain,(
    ! [C_53] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_53)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_315])).

tff(c_356,plain,(
    ! [C_53] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_53)) = k3_xboole_0('#skF_3',C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_342])).

tff(c_22,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.37  % Computer   : n007.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:00:06 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.38  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.32/1.32  
% 2.32/1.32  %Foreground sorts:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Background operators:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Foreground operators:
% 2.32/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.32  
% 2.32/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.32/1.33  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.32/1.33  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.32/1.33  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.32/1.33  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.32/1.33  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.32/1.33  tff(c_41, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.33  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.33  tff(c_63, plain, (![A_30]: (k2_xboole_0(k1_xboole_0, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_41, c_10])).
% 2.32/1.33  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.32/1.33  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.33  tff(c_156, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.33  tff(c_162, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_156])).
% 2.32/1.33  tff(c_166, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_162])).
% 2.32/1.33  tff(c_315, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k3_xboole_0(A_51, B_52), k3_xboole_0(A_51, C_53))=k3_xboole_0(A_51, k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.33  tff(c_342, plain, (![C_53]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_53))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_53)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_315])).
% 2.32/1.33  tff(c_356, plain, (![C_53]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_53))=k3_xboole_0('#skF_3', C_53))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_342])).
% 2.32/1.33  tff(c_22, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.32/1.33  tff(c_617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_22])).
% 2.32/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  Inference rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Ref     : 0
% 2.32/1.33  #Sup     : 146
% 2.32/1.33  #Fact    : 0
% 2.32/1.33  #Define  : 0
% 2.32/1.33  #Split   : 0
% 2.32/1.33  #Chain   : 0
% 2.32/1.33  #Close   : 0
% 2.32/1.33  
% 2.32/1.33  Ordering : KBO
% 2.32/1.33  
% 2.32/1.33  Simplification rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Subsume      : 2
% 2.32/1.33  #Demod        : 82
% 2.32/1.33  #Tautology    : 93
% 2.32/1.33  #SimpNegUnit  : 3
% 2.32/1.33  #BackRed      : 2
% 2.32/1.33  
% 2.32/1.33  #Partial instantiations: 0
% 2.32/1.33  #Strategies tried      : 1
% 2.32/1.33  
% 2.32/1.33  Timing (in seconds)
% 2.32/1.33  ----------------------
% 2.32/1.33  Preprocessing        : 0.27
% 2.32/1.33  Parsing              : 0.15
% 2.32/1.33  CNF conversion       : 0.02
% 2.32/1.33  Main loop            : 0.28
% 2.32/1.33  Inferencing          : 0.10
% 2.32/1.33  Reduction            : 0.11
% 2.32/1.33  Demodulation         : 0.09
% 2.32/1.33  BG Simplification    : 0.01
% 2.32/1.33  Subsumption          : 0.04
% 2.32/1.33  Abstraction          : 0.01
% 2.32/1.33  MUC search           : 0.00
% 2.32/1.33  Cooper               : 0.00
% 2.32/1.33  Total                : 0.58
% 2.32/1.33  Index Insertion      : 0.00
% 2.32/1.33  Index Deletion       : 0.00
% 2.32/1.33  Index Matching       : 0.00
% 2.32/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
