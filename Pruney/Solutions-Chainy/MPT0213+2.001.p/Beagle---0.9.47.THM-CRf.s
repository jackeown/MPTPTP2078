%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   37 (  87 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 ( 142 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_42,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_556,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_4'(A_123,B_124),A_123)
      | r2_hidden('#skF_5'(A_123,B_124),B_124)
      | k3_tarski(A_123) = B_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_284,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_4'(A_91,B_92),A_91)
      | r2_hidden('#skF_5'(A_91,B_92),B_92)
      | k3_tarski(A_91) = B_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [D_35,B_36,A_37] :
      ( ~ r2_hidden(D_35,B_36)
      | r2_hidden(D_35,k2_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75,plain,(
    ! [A_43,B_44,D_45] :
      ( ~ r2_hidden(k2_xboole_0(A_43,B_44),D_45)
      | ~ r2_hidden(D_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_89,plain,(
    ! [A_46,D_47] :
      ( ~ r2_hidden(A_46,D_47)
      | ~ r2_hidden(D_47,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_75])).

tff(c_134,plain,(
    ! [A_58,B_59,D_60] :
      ( ~ r2_hidden(k2_xboole_0(A_58,B_59),k1_xboole_0)
      | ~ r2_hidden(D_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_136,plain,(
    ! [A_9,D_60] :
      ( ~ r2_hidden(A_9,k1_xboole_0)
      | ~ r2_hidden(D_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_134])).

tff(c_137,plain,(
    ! [D_60] : ~ r2_hidden(D_60,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_374,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_4'(A_93,k1_xboole_0),A_93)
      | k3_tarski(A_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_284,c_137])).

tff(c_406,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_374,c_137])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_406])).

tff(c_422,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_656,plain,(
    ! [A_125] :
      ( r2_hidden('#skF_4'(A_125,k1_xboole_0),A_125)
      | k3_tarski(A_125) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_556,c_422])).

tff(c_692,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_656,c_422])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:56:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  %$ r2_hidden > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.49/1.34  
% 2.49/1.34  %Foreground sorts:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Background operators:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Foreground operators:
% 2.49/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.49/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.49/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.49/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.49/1.34  
% 2.49/1.35  tff(f_53, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.49/1.35  tff(f_51, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.49/1.35  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.49/1.35  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.49/1.35  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.49/1.35  tff(c_42, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.35  tff(c_556, plain, (![A_123, B_124]: (r2_hidden('#skF_4'(A_123, B_124), A_123) | r2_hidden('#skF_5'(A_123, B_124), B_124) | k3_tarski(A_123)=B_124)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.35  tff(c_284, plain, (![A_91, B_92]: (r2_hidden('#skF_4'(A_91, B_92), A_91) | r2_hidden('#skF_5'(A_91, B_92), B_92) | k3_tarski(A_91)=B_92)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.35  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.35  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.49/1.35  tff(c_60, plain, (![D_35, B_36, A_37]: (~r2_hidden(D_35, B_36) | r2_hidden(D_35, k2_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.49/1.35  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.49/1.35  tff(c_75, plain, (![A_43, B_44, D_45]: (~r2_hidden(k2_xboole_0(A_43, B_44), D_45) | ~r2_hidden(D_45, B_44))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.49/1.35  tff(c_89, plain, (![A_46, D_47]: (~r2_hidden(A_46, D_47) | ~r2_hidden(D_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_75])).
% 2.49/1.35  tff(c_134, plain, (![A_58, B_59, D_60]: (~r2_hidden(k2_xboole_0(A_58, B_59), k1_xboole_0) | ~r2_hidden(D_60, B_59))), inference(resolution, [status(thm)], [c_6, c_89])).
% 2.49/1.35  tff(c_136, plain, (![A_9, D_60]: (~r2_hidden(A_9, k1_xboole_0) | ~r2_hidden(D_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_134])).
% 2.49/1.35  tff(c_137, plain, (![D_60]: (~r2_hidden(D_60, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_136])).
% 2.49/1.35  tff(c_374, plain, (![A_93]: (r2_hidden('#skF_4'(A_93, k1_xboole_0), A_93) | k3_tarski(A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_284, c_137])).
% 2.49/1.35  tff(c_406, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_374, c_137])).
% 2.49/1.35  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_406])).
% 2.49/1.35  tff(c_422, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(splitRight, [status(thm)], [c_136])).
% 2.49/1.35  tff(c_656, plain, (![A_125]: (r2_hidden('#skF_4'(A_125, k1_xboole_0), A_125) | k3_tarski(A_125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_556, c_422])).
% 2.49/1.35  tff(c_692, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_656, c_422])).
% 2.49/1.35  tff(c_708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_692])).
% 2.49/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  Inference rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Ref     : 0
% 2.49/1.35  #Sup     : 147
% 2.49/1.35  #Fact    : 0
% 2.49/1.35  #Define  : 0
% 2.49/1.35  #Split   : 1
% 2.49/1.35  #Chain   : 0
% 2.49/1.35  #Close   : 0
% 2.49/1.35  
% 2.49/1.35  Ordering : KBO
% 2.49/1.35  
% 2.49/1.35  Simplification rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Subsume      : 18
% 2.49/1.35  #Demod        : 0
% 2.49/1.35  #Tautology    : 9
% 2.49/1.35  #SimpNegUnit  : 4
% 2.49/1.35  #BackRed      : 0
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.49/1.36  Preprocessing        : 0.28
% 2.49/1.36  Parsing              : 0.15
% 2.49/1.36  CNF conversion       : 0.02
% 2.49/1.36  Main loop            : 0.30
% 2.63/1.36  Inferencing          : 0.11
% 2.63/1.36  Reduction            : 0.06
% 2.63/1.36  Demodulation         : 0.04
% 2.63/1.36  BG Simplification    : 0.02
% 2.63/1.36  Subsumption          : 0.08
% 2.63/1.36  Abstraction          : 0.02
% 2.63/1.36  MUC search           : 0.00
% 2.63/1.36  Cooper               : 0.00
% 2.63/1.36  Total                : 0.60
% 2.63/1.36  Index Insertion      : 0.00
% 2.63/1.36  Index Deletion       : 0.00
% 2.63/1.36  Index Matching       : 0.00
% 2.63/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
