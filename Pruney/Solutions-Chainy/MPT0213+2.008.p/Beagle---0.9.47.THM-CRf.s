%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  51 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_64,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_5'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_300,plain,(
    ! [A_75,C_76] :
      ( r2_hidden('#skF_9'(A_75,k3_tarski(A_75),C_76),A_75)
      | ~ r2_hidden(C_76,k3_tarski(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,A_48)
      | ~ r2_hidden(D_47,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [D_47,A_17] :
      ( r2_hidden(D_47,A_17)
      | ~ r2_hidden(D_47,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_94])).

tff(c_328,plain,(
    ! [C_76,A_17] :
      ( r2_hidden('#skF_9'(k1_xboole_0,k3_tarski(k1_xboole_0),C_76),A_17)
      | ~ r2_hidden(C_76,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_300,c_101])).

tff(c_44,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_118,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_127,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_118])).

tff(c_131,plain,(
    ! [A_57] : k4_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,(
    ! [D_12,A_57] :
      ( ~ r2_hidden(D_12,k1_xboole_0)
      | ~ r2_hidden(D_12,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_22])).

tff(c_532,plain,(
    ! [C_89,A_90] :
      ( ~ r2_hidden('#skF_9'(k1_xboole_0,k3_tarski(k1_xboole_0),C_89),A_90)
      | ~ r2_hidden(C_89,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_300,c_137])).

tff(c_562,plain,(
    ! [C_91] : ~ r2_hidden(C_91,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_328,c_532])).

tff(c_586,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_562])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.73  
% 2.85/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.73  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7
% 2.85/1.73  
% 2.85/1.73  %Foreground sorts:
% 2.85/1.73  
% 2.85/1.73  
% 2.85/1.73  %Background operators:
% 2.85/1.73  
% 2.85/1.73  
% 2.85/1.73  %Foreground operators:
% 2.85/1.73  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.85/1.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.85/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.85/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.85/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.85/1.73  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.85/1.73  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.85/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.85/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.85/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.73  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.85/1.73  
% 2.85/1.75  tff(f_70, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.85/1.75  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.85/1.75  tff(f_68, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.85/1.75  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.85/1.75  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.85/1.75  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.85/1.75  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.85/1.75  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.85/1.75  tff(c_64, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.85/1.75  tff(c_38, plain, (![A_13]: (r2_hidden('#skF_5'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.75  tff(c_300, plain, (![A_75, C_76]: (r2_hidden('#skF_9'(A_75, k3_tarski(A_75), C_76), A_75) | ~r2_hidden(C_76, k3_tarski(A_75)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.75  tff(c_42, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.85/1.75  tff(c_94, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, A_48) | ~r2_hidden(D_47, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.75  tff(c_101, plain, (![D_47, A_17]: (r2_hidden(D_47, A_17) | ~r2_hidden(D_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_94])).
% 2.85/1.75  tff(c_328, plain, (![C_76, A_17]: (r2_hidden('#skF_9'(k1_xboole_0, k3_tarski(k1_xboole_0), C_76), A_17) | ~r2_hidden(C_76, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_300, c_101])).
% 2.85/1.75  tff(c_44, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.85/1.75  tff(c_118, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.75  tff(c_127, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_118])).
% 2.85/1.75  tff(c_131, plain, (![A_57]: (k4_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127])).
% 2.85/1.75  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.85/1.75  tff(c_137, plain, (![D_12, A_57]: (~r2_hidden(D_12, k1_xboole_0) | ~r2_hidden(D_12, A_57))), inference(superposition, [status(thm), theory('equality')], [c_131, c_22])).
% 2.85/1.75  tff(c_532, plain, (![C_89, A_90]: (~r2_hidden('#skF_9'(k1_xboole_0, k3_tarski(k1_xboole_0), C_89), A_90) | ~r2_hidden(C_89, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_300, c_137])).
% 2.85/1.75  tff(c_562, plain, (![C_91]: (~r2_hidden(C_91, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_328, c_532])).
% 2.85/1.75  tff(c_586, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_562])).
% 2.85/1.75  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_586])).
% 2.85/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.75  
% 2.85/1.75  Inference rules
% 2.85/1.75  ----------------------
% 2.85/1.75  #Ref     : 0
% 2.85/1.75  #Sup     : 119
% 2.85/1.75  #Fact    : 0
% 2.85/1.75  #Define  : 0
% 2.85/1.75  #Split   : 0
% 2.85/1.75  #Chain   : 0
% 2.85/1.75  #Close   : 0
% 2.85/1.75  
% 2.85/1.75  Ordering : KBO
% 2.85/1.75  
% 2.85/1.75  Simplification rules
% 2.85/1.75  ----------------------
% 2.85/1.75  #Subsume      : 21
% 2.85/1.75  #Demod        : 26
% 2.85/1.75  #Tautology    : 49
% 2.85/1.75  #SimpNegUnit  : 1
% 2.85/1.75  #BackRed      : 0
% 2.85/1.75  
% 2.85/1.75  #Partial instantiations: 0
% 2.85/1.75  #Strategies tried      : 1
% 2.85/1.75  
% 2.85/1.75  Timing (in seconds)
% 2.85/1.75  ----------------------
% 2.85/1.76  Preprocessing        : 0.49
% 2.85/1.76  Parsing              : 0.25
% 2.85/1.76  CNF conversion       : 0.04
% 2.85/1.76  Main loop            : 0.43
% 2.85/1.76  Inferencing          : 0.16
% 2.85/1.76  Reduction            : 0.11
% 2.85/1.76  Demodulation         : 0.08
% 2.85/1.76  BG Simplification    : 0.03
% 2.85/1.76  Subsumption          : 0.10
% 2.85/1.76  Abstraction          : 0.02
% 2.85/1.76  MUC search           : 0.00
% 2.85/1.76  Cooper               : 0.00
% 2.85/1.76  Total                : 0.96
% 2.85/1.76  Index Insertion      : 0.00
% 2.85/1.76  Index Deletion       : 0.00
% 2.85/1.76  Index Matching       : 0.00
% 2.85/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
