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
% DateTime   : Thu Dec  3 09:50:41 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    ! [A_64,B_65] : r2_hidden(A_64,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_18])).

tff(c_54,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,k3_tarski(B_47))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [B_66,A_67] : r2_hidden(B_66,k2_tarski(A_67,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_125,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_285,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_307,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(A_87,B_88)
      | ~ r1_tarski(k1_tarski(A_87),B_88) ) ),
    inference(resolution,[status(thm)],[c_125,c_285])).

tff(c_358,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(A_98,k3_tarski(B_99))
      | ~ r2_hidden(k1_tarski(A_98),B_99) ) ),
    inference(resolution,[status(thm)],[c_54,c_307])).

tff(c_362,plain,(
    ! [A_98,B_65] : r2_hidden(A_98,k3_tarski(k2_tarski(k1_tarski(A_98),B_65))) ),
    inference(resolution,[status(thm)],[c_113,c_358])).

tff(c_391,plain,(
    ! [A_100,B_101] : r2_hidden(A_100,k2_xboole_0(k1_tarski(A_100),B_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_362])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6240,plain,(
    ! [A_12832,B_12833,B_12834] :
      ( r2_hidden(A_12832,B_12833)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_12832),B_12834),B_12833) ) ),
    inference(resolution,[status(thm)],[c_391,c_2])).

tff(c_6265,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_6240])).

tff(c_6277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.37  
% 6.04/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.04/2.37  
% 6.04/2.37  %Foreground sorts:
% 6.04/2.37  
% 6.04/2.37  
% 6.04/2.37  %Background operators:
% 6.04/2.37  
% 6.04/2.37  
% 6.04/2.37  %Foreground operators:
% 6.04/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.04/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.04/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.04/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.04/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.04/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.04/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.04/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.04/2.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.04/2.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.04/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.04/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.04/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.04/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.04/2.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.04/2.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.04/2.37  
% 6.41/2.38  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 6.41/2.38  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.41/2.38  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.41/2.38  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.41/2.38  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.41/2.38  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.41/2.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.41/2.38  tff(c_58, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.41/2.38  tff(c_60, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.41/2.38  tff(c_56, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.41/2.38  tff(c_104, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.41/2.38  tff(c_18, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.41/2.38  tff(c_113, plain, (![A_64, B_65]: (r2_hidden(A_64, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_18])).
% 6.41/2.38  tff(c_54, plain, (![A_46, B_47]: (r1_tarski(A_46, k3_tarski(B_47)) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.41/2.38  tff(c_40, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.41/2.38  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.41/2.38  tff(c_122, plain, (![B_66, A_67]: (r2_hidden(B_66, k2_tarski(A_67, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 6.41/2.38  tff(c_125, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_122])).
% 6.41/2.38  tff(c_285, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.41/2.38  tff(c_307, plain, (![A_87, B_88]: (r2_hidden(A_87, B_88) | ~r1_tarski(k1_tarski(A_87), B_88))), inference(resolution, [status(thm)], [c_125, c_285])).
% 6.41/2.38  tff(c_358, plain, (![A_98, B_99]: (r2_hidden(A_98, k3_tarski(B_99)) | ~r2_hidden(k1_tarski(A_98), B_99))), inference(resolution, [status(thm)], [c_54, c_307])).
% 6.41/2.38  tff(c_362, plain, (![A_98, B_65]: (r2_hidden(A_98, k3_tarski(k2_tarski(k1_tarski(A_98), B_65))))), inference(resolution, [status(thm)], [c_113, c_358])).
% 6.41/2.38  tff(c_391, plain, (![A_100, B_101]: (r2_hidden(A_100, k2_xboole_0(k1_tarski(A_100), B_101)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_362])).
% 6.41/2.38  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.41/2.38  tff(c_6240, plain, (![A_12832, B_12833, B_12834]: (r2_hidden(A_12832, B_12833) | ~r1_tarski(k2_xboole_0(k1_tarski(A_12832), B_12834), B_12833))), inference(resolution, [status(thm)], [c_391, c_2])).
% 6.41/2.38  tff(c_6265, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_6240])).
% 6.41/2.38  tff(c_6277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_6265])).
% 6.41/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.38  
% 6.41/2.38  Inference rules
% 6.41/2.38  ----------------------
% 6.41/2.38  #Ref     : 0
% 6.41/2.38  #Sup     : 678
% 6.41/2.38  #Fact    : 18
% 6.41/2.38  #Define  : 0
% 6.41/2.38  #Split   : 1
% 6.41/2.38  #Chain   : 0
% 6.41/2.38  #Close   : 0
% 6.41/2.38  
% 6.41/2.38  Ordering : KBO
% 6.41/2.38  
% 6.41/2.38  Simplification rules
% 6.41/2.38  ----------------------
% 6.41/2.38  #Subsume      : 90
% 6.41/2.38  #Demod        : 189
% 6.41/2.38  #Tautology    : 189
% 6.41/2.38  #SimpNegUnit  : 1
% 6.41/2.38  #BackRed      : 0
% 6.41/2.38  
% 6.41/2.38  #Partial instantiations: 3870
% 6.41/2.38  #Strategies tried      : 1
% 6.41/2.38  
% 6.41/2.38  Timing (in seconds)
% 6.41/2.38  ----------------------
% 6.41/2.38  Preprocessing        : 0.40
% 6.41/2.38  Parsing              : 0.19
% 6.41/2.38  CNF conversion       : 0.03
% 6.41/2.38  Main loop            : 1.16
% 6.41/2.38  Inferencing          : 0.62
% 6.41/2.38  Reduction            : 0.29
% 6.41/2.38  Demodulation         : 0.23
% 6.41/2.38  BG Simplification    : 0.05
% 6.41/2.38  Subsumption          : 0.14
% 6.41/2.38  Abstraction          : 0.05
% 6.41/2.38  MUC search           : 0.00
% 6.41/2.38  Cooper               : 0.00
% 6.41/2.38  Total                : 1.58
% 6.41/2.38  Index Insertion      : 0.00
% 6.41/2.38  Index Deletion       : 0.00
% 6.41/2.38  Index Matching       : 0.00
% 6.41/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
