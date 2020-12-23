%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_71,plain,(
    ! [A_32,B_33,C_34,D_35] : k2_xboole_0(k1_tarski(A_32),k1_enumset1(B_33,C_34,D_35)) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_36,B_37,C_38,D_39] : r1_tarski(k1_tarski(A_36),k2_enumset1(A_36,B_37,C_38,D_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_767,plain,(
    ! [A_85,B_86,C_87,D_88] : k2_xboole_0(k1_tarski(A_85),k2_enumset1(A_85,B_86,C_87,D_88)) = k2_enumset1(A_85,B_86,C_87,D_88) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,D_12,A_9] : k2_xboole_0(k1_tarski(A_9),k2_enumset1(B_10,C_11,D_12,E_13)) = k3_enumset1(A_9,B_10,C_11,D_12,E_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_773,plain,(
    ! [A_85,B_86,C_87,D_88] : k3_enumset1(A_85,A_85,B_86,C_87,D_88) = k2_enumset1(A_85,B_86,C_87,D_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_8])).

tff(c_16,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:04:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.28  
% 2.28/1.28  %Foreground sorts:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Background operators:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Foreground operators:
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.28  
% 2.28/1.29  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.28/1.29  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.28/1.29  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.28/1.29  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.28/1.29  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.28/1.29  tff(c_71, plain, (![A_32, B_33, C_34, D_35]: (k2_xboole_0(k1_tarski(A_32), k1_enumset1(B_33, C_34, D_35))=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.29  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.29  tff(c_90, plain, (![A_36, B_37, C_38, D_39]: (r1_tarski(k1_tarski(A_36), k2_enumset1(A_36, B_37, C_38, D_39)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 2.28/1.29  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.29  tff(c_767, plain, (![A_85, B_86, C_87, D_88]: (k2_xboole_0(k1_tarski(A_85), k2_enumset1(A_85, B_86, C_87, D_88))=k2_enumset1(A_85, B_86, C_87, D_88))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.28/1.29  tff(c_8, plain, (![C_11, E_13, B_10, D_12, A_9]: (k2_xboole_0(k1_tarski(A_9), k2_enumset1(B_10, C_11, D_12, E_13))=k3_enumset1(A_9, B_10, C_11, D_12, E_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.29  tff(c_773, plain, (![A_85, B_86, C_87, D_88]: (k3_enumset1(A_85, A_85, B_86, C_87, D_88)=k2_enumset1(A_85, B_86, C_87, D_88))), inference(superposition, [status(thm), theory('equality')], [c_767, c_8])).
% 2.28/1.29  tff(c_16, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.29  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_773, c_16])).
% 2.28/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  Inference rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Ref     : 0
% 2.28/1.29  #Sup     : 188
% 2.28/1.29  #Fact    : 0
% 2.28/1.29  #Define  : 0
% 2.28/1.29  #Split   : 0
% 2.28/1.29  #Chain   : 0
% 2.28/1.29  #Close   : 0
% 2.28/1.29  
% 2.28/1.29  Ordering : KBO
% 2.28/1.29  
% 2.28/1.29  Simplification rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Subsume      : 6
% 2.28/1.29  #Demod        : 149
% 2.28/1.29  #Tautology    : 144
% 2.28/1.29  #SimpNegUnit  : 0
% 2.28/1.29  #BackRed      : 1
% 2.28/1.29  
% 2.28/1.29  #Partial instantiations: 0
% 2.28/1.29  #Strategies tried      : 1
% 2.28/1.29  
% 2.28/1.29  Timing (in seconds)
% 2.28/1.29  ----------------------
% 2.28/1.29  Preprocessing        : 0.27
% 2.28/1.29  Parsing              : 0.14
% 2.28/1.29  CNF conversion       : 0.02
% 2.28/1.29  Main loop            : 0.28
% 2.28/1.29  Inferencing          : 0.12
% 2.28/1.29  Reduction            : 0.11
% 2.28/1.29  Demodulation         : 0.08
% 2.28/1.29  BG Simplification    : 0.01
% 2.28/1.30  Subsumption          : 0.03
% 2.28/1.30  Abstraction          : 0.02
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.57
% 2.28/1.30  Index Insertion      : 0.00
% 2.28/1.30  Index Deletion       : 0.00
% 2.28/1.30  Index Matching       : 0.00
% 2.28/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
