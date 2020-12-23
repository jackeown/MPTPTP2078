%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_339,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_348,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_339])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_352,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_12])).

tff(c_358,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_352])).

tff(c_407,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_518,plain,(
    ! [C_45] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_45)) = k4_xboole_0('#skF_3',C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_407])).

tff(c_527,plain,(
    ! [C_45] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',C_45)) = k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_14])).

tff(c_533,plain,(
    ! [C_45] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_45)) = k3_xboole_0('#skF_3',C_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_527])).

tff(c_16,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.29/1.32  
% 2.29/1.32  %Foreground sorts:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Background operators:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Foreground operators:
% 2.29/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.32  
% 2.29/1.33  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.29/1.33  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.29/1.33  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.29/1.33  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.29/1.33  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.29/1.33  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.29/1.33  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.29/1.33  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.33  tff(c_8, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.29/1.33  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.33  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.33  tff(c_47, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, k3_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.33  tff(c_339, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.29/1.33  tff(c_348, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_339])).
% 2.29/1.33  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.33  tff(c_352, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_348, c_12])).
% 2.29/1.33  tff(c_358, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_352])).
% 2.29/1.33  tff(c_407, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.33  tff(c_518, plain, (![C_45]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_45))=k4_xboole_0('#skF_3', C_45))), inference(superposition, [status(thm), theory('equality')], [c_358, c_407])).
% 2.29/1.33  tff(c_527, plain, (![C_45]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', C_45))=k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_45)))), inference(superposition, [status(thm), theory('equality')], [c_518, c_14])).
% 2.29/1.33  tff(c_533, plain, (![C_45]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_45))=k3_xboole_0('#skF_3', C_45))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_527])).
% 2.29/1.33  tff(c_16, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.33  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_16])).
% 2.29/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  Inference rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Ref     : 0
% 2.29/1.33  #Sup     : 187
% 2.29/1.33  #Fact    : 0
% 2.29/1.33  #Define  : 0
% 2.29/1.33  #Split   : 3
% 2.29/1.33  #Chain   : 0
% 2.29/1.33  #Close   : 0
% 2.29/1.33  
% 2.29/1.33  Ordering : KBO
% 2.29/1.33  
% 2.29/1.33  Simplification rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Subsume      : 3
% 2.29/1.33  #Demod        : 110
% 2.29/1.33  #Tautology    : 93
% 2.29/1.33  #SimpNegUnit  : 8
% 2.29/1.33  #BackRed      : 2
% 2.29/1.33  
% 2.29/1.33  #Partial instantiations: 0
% 2.29/1.33  #Strategies tried      : 1
% 2.29/1.33  
% 2.29/1.33  Timing (in seconds)
% 2.29/1.33  ----------------------
% 2.63/1.33  Preprocessing        : 0.28
% 2.63/1.33  Parsing              : 0.16
% 2.63/1.33  CNF conversion       : 0.02
% 2.63/1.33  Main loop            : 0.33
% 2.63/1.33  Inferencing          : 0.13
% 2.63/1.33  Reduction            : 0.12
% 2.63/1.33  Demodulation         : 0.09
% 2.63/1.33  BG Simplification    : 0.02
% 2.63/1.33  Subsumption          : 0.04
% 2.63/1.33  Abstraction          : 0.02
% 2.63/1.33  MUC search           : 0.00
% 2.63/1.33  Cooper               : 0.00
% 2.63/1.33  Total                : 0.64
% 2.63/1.33  Index Insertion      : 0.00
% 2.63/1.33  Index Deletion       : 0.00
% 2.63/1.33  Index Matching       : 0.00
% 2.63/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
