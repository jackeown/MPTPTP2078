%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  78 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

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

tff(c_62,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_255,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_258,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_255])).

tff(c_267,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_258])).

tff(c_101,plain,(
    ! [A_53,B_54] : k1_enumset1(A_53,A_53,B_54) = k2_tarski(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [B_54,A_53] : r2_hidden(B_54,k2_tarski(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_26])).

tff(c_284,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_122])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_168,plain,(
    ! [D_62,B_63,A_64] :
      ( ~ r2_hidden(D_62,B_63)
      | r2_hidden(D_62,k2_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [D_62,A_9] :
      ( ~ r2_hidden(D_62,k1_xboole_0)
      | r2_hidden(D_62,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_295,plain,(
    ! [A_9] : r2_hidden('#skF_6',A_9) ),
    inference(resolution,[status(thm)],[c_284,c_189])).

tff(c_30,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [A_53,B_54] : r2_hidden(A_53,k2_tarski(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_30])).

tff(c_287,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_116])).

tff(c_316,plain,(
    ! [A_83] : r2_hidden('#skF_5',A_83) ),
    inference(resolution,[status(thm)],[c_287,c_189])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_347,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_5') ),
    inference(resolution,[status(thm)],[c_316,c_2])).

tff(c_355,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_295,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:07:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.15/1.28  
% 2.15/1.28  %Foreground sorts:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Background operators:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Foreground operators:
% 2.15/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.28  
% 2.15/1.29  tff(f_75, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.15/1.29  tff(f_70, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.15/1.29  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.29  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.15/1.29  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.15/1.29  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.15/1.29  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.15/1.29  tff(c_62, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.15/1.29  tff(c_64, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.15/1.29  tff(c_255, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.29  tff(c_258, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_255])).
% 2.15/1.29  tff(c_267, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_258])).
% 2.15/1.29  tff(c_101, plain, (![A_53, B_54]: (k1_enumset1(A_53, A_53, B_54)=k2_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.29  tff(c_26, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.29  tff(c_122, plain, (![B_54, A_53]: (r2_hidden(B_54, k2_tarski(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_26])).
% 2.15/1.29  tff(c_284, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_122])).
% 2.15/1.29  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.29  tff(c_168, plain, (![D_62, B_63, A_64]: (~r2_hidden(D_62, B_63) | r2_hidden(D_62, k2_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.29  tff(c_189, plain, (![D_62, A_9]: (~r2_hidden(D_62, k1_xboole_0) | r2_hidden(D_62, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_168])).
% 2.15/1.29  tff(c_295, plain, (![A_9]: (r2_hidden('#skF_6', A_9))), inference(resolution, [status(thm)], [c_284, c_189])).
% 2.15/1.29  tff(c_30, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.29  tff(c_116, plain, (![A_53, B_54]: (r2_hidden(A_53, k2_tarski(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_30])).
% 2.15/1.29  tff(c_287, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_116])).
% 2.15/1.29  tff(c_316, plain, (![A_83]: (r2_hidden('#skF_5', A_83))), inference(resolution, [status(thm)], [c_287, c_189])).
% 2.15/1.29  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.15/1.29  tff(c_347, plain, (![A_85]: (~r2_hidden(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_316, c_2])).
% 2.15/1.29  tff(c_355, plain, $false, inference(resolution, [status(thm)], [c_295, c_347])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 67
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 0
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 8
% 2.15/1.29  #Demod        : 13
% 2.15/1.29  #Tautology    : 25
% 2.15/1.29  #SimpNegUnit  : 1
% 2.15/1.29  #BackRed      : 2
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.32
% 2.15/1.29  Parsing              : 0.16
% 2.15/1.29  CNF conversion       : 0.02
% 2.15/1.29  Main loop            : 0.21
% 2.15/1.29  Inferencing          : 0.07
% 2.15/1.29  Reduction            : 0.07
% 2.15/1.29  Demodulation         : 0.05
% 2.15/1.29  BG Simplification    : 0.02
% 2.15/1.29  Subsumption          : 0.04
% 2.15/1.29  Abstraction          : 0.01
% 2.15/1.29  MUC search           : 0.00
% 2.15/1.29  Cooper               : 0.00
% 2.15/1.29  Total                : 0.56
% 2.15/1.29  Index Insertion      : 0.00
% 2.15/1.29  Index Deletion       : 0.00
% 2.15/1.29  Index Matching       : 0.00
% 2.15/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
