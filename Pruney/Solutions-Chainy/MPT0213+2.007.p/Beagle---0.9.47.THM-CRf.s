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
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 116 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 217 expanded)
%              Number of equality atoms :   13 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_62,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_6'(A_18,B_19),A_18)
      | r2_hidden('#skF_7'(A_18,B_19),B_19)
      | k3_tarski(A_18) = B_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_179,plain,(
    ! [A_72,C_73] :
      ( r2_hidden('#skF_8'(A_72,k3_tarski(A_72),C_73),A_72)
      | ~ r2_hidden(C_73,k3_tarski(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,(
    ! [D_49,B_50,A_51] :
      ( ~ r2_hidden(D_49,B_50)
      | r2_hidden(D_49,k2_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [D_49,A_13] :
      ( ~ r2_hidden(D_49,k1_xboole_0)
      | r2_hidden(D_49,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_99])).

tff(c_204,plain,(
    ! [C_73,A_13] :
      ( r2_hidden('#skF_8'(k1_xboole_0,k3_tarski(k1_xboole_0),C_73),A_13)
      | ~ r2_hidden(C_73,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_179,c_102])).

tff(c_224,plain,(
    ! [C_77,A_78] :
      ( r2_hidden('#skF_8'(k1_xboole_0,k3_tarski(k1_xboole_0),C_77),A_78)
      | ~ r2_hidden(C_77,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_179,c_102])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_340,plain,(
    ! [C_84,B_85] :
      ( ~ r2_hidden('#skF_8'(k1_xboole_0,k3_tarski(k1_xboole_0),C_84),B_85)
      | ~ r2_hidden(C_84,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_224,c_22])).

tff(c_370,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_204,c_340])).

tff(c_538,plain,(
    ! [A_96] :
      ( r2_hidden('#skF_6'(A_96,k3_tarski(k1_xboole_0)),A_96)
      | k3_tarski(k1_xboole_0) = k3_tarski(A_96) ) ),
    inference(resolution,[status(thm)],[c_58,c_370])).

tff(c_364,plain,(
    ! [C_73] : ~ r2_hidden(C_73,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_204,c_340])).

tff(c_597,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_538,c_364])).

tff(c_383,plain,(
    ! [B_19] :
      ( r2_hidden('#skF_7'(k3_tarski(k1_xboole_0),B_19),B_19)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_19 ) ),
    inference(resolution,[status(thm)],[c_58,c_370])).

tff(c_653,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_7'(k3_tarski(k1_xboole_0),B_100),B_100)
      | k3_tarski(k1_xboole_0) = B_100 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_383])).

tff(c_680,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_7'(k3_tarski(k1_xboole_0),k1_xboole_0),A_13)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_653,c_102])).

tff(c_704,plain,(
    ! [A_101] : r2_hidden('#skF_7'(k3_tarski(k1_xboole_0),k1_xboole_0),A_101) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_680])).

tff(c_743,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_704,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.47  
% 2.87/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.47  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 2.87/1.47  
% 2.87/1.47  %Foreground sorts:
% 2.87/1.47  
% 2.87/1.47  
% 2.87/1.47  %Background operators:
% 2.87/1.47  
% 2.87/1.47  
% 2.87/1.47  %Foreground operators:
% 2.87/1.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.87/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.87/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.87/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.87/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.87/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.87/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.87/1.47  
% 2.87/1.49  tff(f_62, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.87/1.49  tff(f_60, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.87/1.49  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.87/1.49  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.87/1.49  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.87/1.49  tff(c_62, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.49  tff(c_58, plain, (![A_18, B_19]: (r2_hidden('#skF_6'(A_18, B_19), A_18) | r2_hidden('#skF_7'(A_18, B_19), B_19) | k3_tarski(A_18)=B_19)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.49  tff(c_179, plain, (![A_72, C_73]: (r2_hidden('#skF_8'(A_72, k3_tarski(A_72), C_73), A_72) | ~r2_hidden(C_73, k3_tarski(A_72)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.49  tff(c_38, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.49  tff(c_99, plain, (![D_49, B_50, A_51]: (~r2_hidden(D_49, B_50) | r2_hidden(D_49, k2_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.87/1.49  tff(c_102, plain, (![D_49, A_13]: (~r2_hidden(D_49, k1_xboole_0) | r2_hidden(D_49, A_13))), inference(superposition, [status(thm), theory('equality')], [c_38, c_99])).
% 2.87/1.49  tff(c_204, plain, (![C_73, A_13]: (r2_hidden('#skF_8'(k1_xboole_0, k3_tarski(k1_xboole_0), C_73), A_13) | ~r2_hidden(C_73, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_179, c_102])).
% 2.87/1.49  tff(c_224, plain, (![C_77, A_78]: (r2_hidden('#skF_8'(k1_xboole_0, k3_tarski(k1_xboole_0), C_77), A_78) | ~r2_hidden(C_77, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_179, c_102])).
% 2.87/1.49  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.87/1.49  tff(c_340, plain, (![C_84, B_85]: (~r2_hidden('#skF_8'(k1_xboole_0, k3_tarski(k1_xboole_0), C_84), B_85) | ~r2_hidden(C_84, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_224, c_22])).
% 2.87/1.49  tff(c_370, plain, (![C_86]: (~r2_hidden(C_86, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_204, c_340])).
% 2.87/1.49  tff(c_538, plain, (![A_96]: (r2_hidden('#skF_6'(A_96, k3_tarski(k1_xboole_0)), A_96) | k3_tarski(k1_xboole_0)=k3_tarski(A_96))), inference(resolution, [status(thm)], [c_58, c_370])).
% 2.87/1.49  tff(c_364, plain, (![C_73]: (~r2_hidden(C_73, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_204, c_340])).
% 2.87/1.49  tff(c_597, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_538, c_364])).
% 2.87/1.49  tff(c_383, plain, (![B_19]: (r2_hidden('#skF_7'(k3_tarski(k1_xboole_0), B_19), B_19) | k3_tarski(k3_tarski(k1_xboole_0))=B_19)), inference(resolution, [status(thm)], [c_58, c_370])).
% 2.87/1.49  tff(c_653, plain, (![B_100]: (r2_hidden('#skF_7'(k3_tarski(k1_xboole_0), B_100), B_100) | k3_tarski(k1_xboole_0)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_597, c_383])).
% 2.87/1.49  tff(c_680, plain, (![A_13]: (r2_hidden('#skF_7'(k3_tarski(k1_xboole_0), k1_xboole_0), A_13) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_653, c_102])).
% 2.87/1.49  tff(c_704, plain, (![A_101]: (r2_hidden('#skF_7'(k3_tarski(k1_xboole_0), k1_xboole_0), A_101))), inference(negUnitSimplification, [status(thm)], [c_62, c_680])).
% 2.87/1.49  tff(c_743, plain, $false, inference(resolution, [status(thm)], [c_704, c_364])).
% 2.87/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.49  
% 2.87/1.49  Inference rules
% 2.87/1.49  ----------------------
% 2.87/1.49  #Ref     : 0
% 2.87/1.49  #Sup     : 147
% 2.87/1.49  #Fact    : 0
% 2.87/1.49  #Define  : 0
% 2.87/1.49  #Split   : 0
% 2.87/1.49  #Chain   : 0
% 2.87/1.49  #Close   : 0
% 2.87/1.49  
% 2.87/1.49  Ordering : KBO
% 2.87/1.49  
% 2.87/1.49  Simplification rules
% 2.87/1.49  ----------------------
% 2.87/1.49  #Subsume      : 28
% 2.87/1.49  #Demod        : 35
% 2.87/1.49  #Tautology    : 23
% 2.87/1.49  #SimpNegUnit  : 4
% 2.87/1.49  #BackRed      : 5
% 2.87/1.49  
% 2.87/1.49  #Partial instantiations: 0
% 2.87/1.49  #Strategies tried      : 1
% 2.87/1.49  
% 2.87/1.49  Timing (in seconds)
% 2.87/1.49  ----------------------
% 2.87/1.49  Preprocessing        : 0.32
% 2.87/1.49  Parsing              : 0.17
% 2.87/1.49  CNF conversion       : 0.03
% 2.87/1.49  Main loop            : 0.35
% 2.87/1.49  Inferencing          : 0.13
% 2.87/1.49  Reduction            : 0.09
% 2.87/1.49  Demodulation         : 0.06
% 2.87/1.49  BG Simplification    : 0.02
% 2.87/1.49  Subsumption          : 0.08
% 2.87/1.49  Abstraction          : 0.02
% 2.87/1.49  MUC search           : 0.00
% 2.87/1.49  Cooper               : 0.00
% 2.87/1.49  Total                : 0.70
% 2.87/1.49  Index Insertion      : 0.00
% 2.87/1.49  Index Deletion       : 0.00
% 2.96/1.49  Index Matching       : 0.00
% 2.96/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
