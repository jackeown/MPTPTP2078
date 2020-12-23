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
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    ! [B_24,A_25] :
      ( ~ r2_xboole_0(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [B_26,A_27] : k5_xboole_0(B_26,A_27) = k5_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_10])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_271,plain,(
    ! [A_34,B_35,C_36] : k5_xboole_0(k5_xboole_0(A_34,B_35),C_36) = k5_xboole_0(A_34,k5_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_346,plain,(
    ! [A_15,C_36] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_36)) = k5_xboole_0(k1_xboole_0,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_271])).

tff(c_360,plain,(
    ! [A_37,C_38] : k5_xboole_0(A_37,k5_xboole_0(A_37,C_38)) = C_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_346])).

tff(c_750,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_360])).

tff(c_796,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_750])).

tff(c_803,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_796])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1154,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_8])).

tff(c_1159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.50  
% 3.05/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.51  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.05/1.51  
% 3.05/1.51  %Foreground sorts:
% 3.05/1.51  
% 3.05/1.51  
% 3.05/1.51  %Background operators:
% 3.05/1.51  
% 3.05/1.51  
% 3.05/1.51  %Foreground operators:
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.05/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.51  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.51  
% 3.05/1.52  tff(f_50, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 3.05/1.52  tff(f_40, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.05/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.05/1.52  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.05/1.52  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.05/1.52  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.05/1.52  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.05/1.52  tff(f_42, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.05/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.05/1.52  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.05/1.52  tff(c_101, plain, (![B_24, A_25]: (~r2_xboole_0(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.05/1.52  tff(c_105, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_101])).
% 3.05/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.52  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.52  tff(c_18, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.05/1.52  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.52  tff(c_106, plain, (![B_26, A_27]: (k5_xboole_0(B_26, A_27)=k5_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.52  tff(c_122, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, A_27)=A_27)), inference(superposition, [status(thm), theory('equality')], [c_106, c_10])).
% 3.05/1.52  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.05/1.52  tff(c_271, plain, (![A_34, B_35, C_36]: (k5_xboole_0(k5_xboole_0(A_34, B_35), C_36)=k5_xboole_0(A_34, k5_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.05/1.52  tff(c_346, plain, (![A_15, C_36]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_36))=k5_xboole_0(k1_xboole_0, C_36))), inference(superposition, [status(thm), theory('equality')], [c_16, c_271])).
% 3.05/1.52  tff(c_360, plain, (![A_37, C_38]: (k5_xboole_0(A_37, k5_xboole_0(A_37, C_38))=C_38)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_346])).
% 3.05/1.52  tff(c_750, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_6, c_360])).
% 3.05/1.52  tff(c_796, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_750])).
% 3.05/1.52  tff(c_803, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_796])).
% 3.05/1.52  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.52  tff(c_1154, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_803, c_8])).
% 3.05/1.52  tff(c_1159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_1154])).
% 3.05/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.52  
% 3.05/1.52  Inference rules
% 3.05/1.52  ----------------------
% 3.05/1.52  #Ref     : 0
% 3.05/1.52  #Sup     : 286
% 3.05/1.52  #Fact    : 0
% 3.05/1.52  #Define  : 0
% 3.05/1.52  #Split   : 0
% 3.05/1.52  #Chain   : 0
% 3.05/1.52  #Close   : 0
% 3.05/1.52  
% 3.05/1.52  Ordering : KBO
% 3.05/1.52  
% 3.05/1.52  Simplification rules
% 3.05/1.52  ----------------------
% 3.05/1.52  #Subsume      : 15
% 3.05/1.52  #Demod        : 152
% 3.05/1.52  #Tautology    : 166
% 3.05/1.52  #SimpNegUnit  : 1
% 3.05/1.52  #BackRed      : 0
% 3.05/1.52  
% 3.05/1.52  #Partial instantiations: 0
% 3.05/1.52  #Strategies tried      : 1
% 3.05/1.52  
% 3.05/1.52  Timing (in seconds)
% 3.05/1.52  ----------------------
% 3.05/1.52  Preprocessing        : 0.27
% 3.05/1.52  Parsing              : 0.15
% 3.05/1.52  CNF conversion       : 0.02
% 3.05/1.52  Main loop            : 0.48
% 3.05/1.52  Inferencing          : 0.14
% 3.05/1.52  Reduction            : 0.24
% 3.05/1.52  Demodulation         : 0.21
% 3.05/1.52  BG Simplification    : 0.02
% 3.05/1.52  Subsumption          : 0.06
% 3.05/1.52  Abstraction          : 0.02
% 3.05/1.52  MUC search           : 0.00
% 3.05/1.52  Cooper               : 0.00
% 3.05/1.52  Total                : 0.78
% 3.05/1.52  Index Insertion      : 0.00
% 3.05/1.52  Index Deletion       : 0.00
% 3.05/1.52  Index Matching       : 0.00
% 3.05/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
