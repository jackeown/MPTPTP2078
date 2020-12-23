%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 152 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   46 ( 253 expanded)
%              Number of equality atoms :   20 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_174,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_4'(A_59,B_60),A_59)
      | r2_hidden('#skF_5'(A_59,B_60),B_60)
      | k3_tarski(A_59) = B_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_12,C_27] :
      ( r2_hidden('#skF_6'(A_12,k3_tarski(A_12),C_27),A_12)
      | ~ r2_hidden(C_27,k3_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    ! [A_46,C_47] :
      ( r2_hidden('#skF_6'(A_46,k3_tarski(A_46),C_47),A_46)
      | ~ r2_hidden(C_47,k3_tarski(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_41] : k5_xboole_0(A_41,A_41) = k4_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_65])).

tff(c_24,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_24])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4])).

tff(c_144,plain,(
    ! [C_53] :
      ( ~ r2_hidden('#skF_6'(k1_xboole_0,k3_tarski(k1_xboole_0),C_53),k1_xboole_0)
      | ~ r2_hidden(C_53,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_107,c_97])).

tff(c_149,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_284,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_64),B_64)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_64 ) ),
    inference(resolution,[status(thm)],[c_174,c_149])).

tff(c_328,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_284,c_149])).

tff(c_225,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_60),B_60)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_60 ) ),
    inference(resolution,[status(thm)],[c_174,c_149])).

tff(c_333,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_60),B_60)
      | k3_tarski(k1_xboole_0) = B_60 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_225])).

tff(c_358,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_67),B_67)
      | k3_tarski(k1_xboole_0) = B_67 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_225])).

tff(c_365,plain,
    ( ~ r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_358,c_97])).

tff(c_380,plain,(
    ~ r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_365])).

tff(c_386,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_333,c_380])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.20/1.31  
% 2.20/1.31  %Foreground sorts:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Background operators:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Foreground operators:
% 2.20/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.20/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.20/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.20/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.20/1.31  
% 2.20/1.32  tff(f_53, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.20/1.32  tff(f_51, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.20/1.32  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.20/1.32  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.20/1.32  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.20/1.32  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.20/1.32  tff(c_44, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.20/1.32  tff(c_174, plain, (![A_59, B_60]: (r2_hidden('#skF_4'(A_59, B_60), A_59) | r2_hidden('#skF_5'(A_59, B_60), B_60) | k3_tarski(A_59)=B_60)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.32  tff(c_28, plain, (![A_12, C_27]: (r2_hidden('#skF_6'(A_12, k3_tarski(A_12), C_27), A_12) | ~r2_hidden(C_27, k3_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.32  tff(c_107, plain, (![A_46, C_47]: (r2_hidden('#skF_6'(A_46, k3_tarski(A_46), C_47), A_46) | ~r2_hidden(C_47, k3_tarski(A_46)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.32  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.32  tff(c_65, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.32  tff(c_77, plain, (![A_41]: (k5_xboole_0(A_41, A_41)=k4_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_20, c_65])).
% 2.20/1.32  tff(c_24, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.32  tff(c_84, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_77, c_24])).
% 2.20/1.32  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.32  tff(c_97, plain, (![D_6]: (~r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_84, c_4])).
% 2.20/1.32  tff(c_144, plain, (![C_53]: (~r2_hidden('#skF_6'(k1_xboole_0, k3_tarski(k1_xboole_0), C_53), k1_xboole_0) | ~r2_hidden(C_53, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_107, c_97])).
% 2.20/1.32  tff(c_149, plain, (![C_27]: (~r2_hidden(C_27, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_28, c_144])).
% 2.20/1.32  tff(c_284, plain, (![B_64]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_64), B_64) | k3_tarski(k3_tarski(k1_xboole_0))=B_64)), inference(resolution, [status(thm)], [c_174, c_149])).
% 2.20/1.32  tff(c_328, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_284, c_149])).
% 2.20/1.32  tff(c_225, plain, (![B_60]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_60), B_60) | k3_tarski(k3_tarski(k1_xboole_0))=B_60)), inference(resolution, [status(thm)], [c_174, c_149])).
% 2.20/1.32  tff(c_333, plain, (![B_60]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_60), B_60) | k3_tarski(k1_xboole_0)=B_60)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_225])).
% 2.20/1.32  tff(c_358, plain, (![B_67]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_67), B_67) | k3_tarski(k1_xboole_0)=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_225])).
% 2.20/1.32  tff(c_365, plain, (~r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), k1_xboole_0), k1_xboole_0) | k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_358, c_97])).
% 2.20/1.32  tff(c_380, plain, (~r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_365])).
% 2.20/1.32  tff(c_386, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_333, c_380])).
% 2.20/1.32  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_386])).
% 2.20/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  Inference rules
% 2.20/1.32  ----------------------
% 2.20/1.32  #Ref     : 0
% 2.20/1.32  #Sup     : 72
% 2.20/1.32  #Fact    : 0
% 2.20/1.32  #Define  : 0
% 2.20/1.32  #Split   : 0
% 2.20/1.32  #Chain   : 0
% 2.20/1.32  #Close   : 0
% 2.20/1.32  
% 2.20/1.32  Ordering : KBO
% 2.20/1.32  
% 2.20/1.32  Simplification rules
% 2.20/1.32  ----------------------
% 2.20/1.32  #Subsume      : 8
% 2.20/1.32  #Demod        : 22
% 2.20/1.32  #Tautology    : 21
% 2.20/1.32  #SimpNegUnit  : 3
% 2.20/1.32  #BackRed      : 6
% 2.20/1.32  
% 2.20/1.32  #Partial instantiations: 0
% 2.20/1.32  #Strategies tried      : 1
% 2.20/1.32  
% 2.20/1.32  Timing (in seconds)
% 2.20/1.32  ----------------------
% 2.20/1.33  Preprocessing        : 0.30
% 2.20/1.33  Parsing              : 0.15
% 2.20/1.33  CNF conversion       : 0.03
% 2.20/1.33  Main loop            : 0.22
% 2.20/1.33  Inferencing          : 0.08
% 2.20/1.33  Reduction            : 0.06
% 2.20/1.33  Demodulation         : 0.04
% 2.20/1.33  BG Simplification    : 0.02
% 2.20/1.33  Subsumption          : 0.05
% 2.20/1.33  Abstraction          : 0.01
% 2.20/1.33  MUC search           : 0.00
% 2.20/1.33  Cooper               : 0.00
% 2.20/1.33  Total                : 0.54
% 2.20/1.33  Index Insertion      : 0.00
% 2.20/1.33  Index Deletion       : 0.00
% 2.20/1.33  Index Matching       : 0.00
% 2.20/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
