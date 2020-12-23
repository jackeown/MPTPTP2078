%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  19 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k3_enumset1(B_11,C_12,D_13,E_14,F_15)) = k4_enumset1(A_10,B_11,C_12,D_13,E_14,F_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k1_tarski(A_5),k2_enumset1(B_6,C_7,D_8,E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [B_43,A_45,E_46,D_42,C_44] : k2_xboole_0(k1_tarski(A_45),k2_enumset1(B_43,C_44,D_42,E_46)) = k3_enumset1(A_45,B_43,C_44,D_42,E_46) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

tff(c_88,plain,(
    ! [B_43,A_45,E_46,D_42,C_44] : k2_xboole_0(k1_tarski(A_45),k3_enumset1(A_45,B_43,C_44,D_42,E_46)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(B_43,C_44,D_42,E_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_33])).

tff(c_723,plain,(
    ! [E_108,A_110,D_111,B_109,C_112] : k2_xboole_0(k1_tarski(A_110),k3_enumset1(A_110,B_109,C_112,D_111,E_108)) = k3_enumset1(A_110,B_109,C_112,D_111,E_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_88])).

tff(c_760,plain,(
    ! [B_11,C_12,F_15,E_14,D_13] : k4_enumset1(B_11,B_11,C_12,D_13,E_14,F_15) = k3_enumset1(B_11,C_12,D_13,E_14,F_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_723])).

tff(c_18,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  
% 2.19/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.34  
% 2.19/1.34  %Foreground sorts:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Background operators:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Foreground operators:
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.34  
% 2.63/1.35  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.63/1.35  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.63/1.35  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.63/1.35  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.63/1.35  tff(f_46, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.63/1.35  tff(c_8, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (k2_xboole_0(k1_tarski(A_10), k3_enumset1(B_11, C_12, D_13, E_14, F_15))=k4_enumset1(A_10, B_11, C_12, D_13, E_14, F_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.35  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5]: (k2_xboole_0(k1_tarski(A_5), k2_enumset1(B_6, C_7, D_8, E_9))=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.35  tff(c_82, plain, (![B_43, A_45, E_46, D_42, C_44]: (k2_xboole_0(k1_tarski(A_45), k2_enumset1(B_43, C_44, D_42, E_46))=k3_enumset1(A_45, B_43, C_44, D_42, E_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.35  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.35  tff(c_29, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.35  tff(c_33, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_4, c_29])).
% 2.63/1.35  tff(c_88, plain, (![B_43, A_45, E_46, D_42, C_44]: (k2_xboole_0(k1_tarski(A_45), k3_enumset1(A_45, B_43, C_44, D_42, E_46))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(B_43, C_44, D_42, E_46)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_33])).
% 2.63/1.35  tff(c_723, plain, (![E_108, A_110, D_111, B_109, C_112]: (k2_xboole_0(k1_tarski(A_110), k3_enumset1(A_110, B_109, C_112, D_111, E_108))=k3_enumset1(A_110, B_109, C_112, D_111, E_108))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_88])).
% 2.63/1.35  tff(c_760, plain, (![B_11, C_12, F_15, E_14, D_13]: (k4_enumset1(B_11, B_11, C_12, D_13, E_14, F_15)=k3_enumset1(B_11, C_12, D_13, E_14, F_15))), inference(superposition, [status(thm), theory('equality')], [c_8, c_723])).
% 2.63/1.35  tff(c_18, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.35  tff(c_857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_760, c_18])).
% 2.63/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  Inference rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Ref     : 0
% 2.63/1.35  #Sup     : 200
% 2.63/1.35  #Fact    : 0
% 2.63/1.35  #Define  : 0
% 2.63/1.35  #Split   : 0
% 2.63/1.35  #Chain   : 0
% 2.63/1.35  #Close   : 0
% 2.63/1.35  
% 2.63/1.35  Ordering : KBO
% 2.63/1.35  
% 2.63/1.35  Simplification rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Subsume      : 5
% 2.63/1.35  #Demod        : 160
% 2.63/1.35  #Tautology    : 153
% 2.63/1.35  #SimpNegUnit  : 0
% 2.63/1.35  #BackRed      : 1
% 2.63/1.35  
% 2.63/1.35  #Partial instantiations: 0
% 2.63/1.35  #Strategies tried      : 1
% 2.63/1.35  
% 2.63/1.35  Timing (in seconds)
% 2.63/1.35  ----------------------
% 2.63/1.35  Preprocessing        : 0.28
% 2.63/1.35  Parsing              : 0.16
% 2.63/1.35  CNF conversion       : 0.02
% 2.63/1.35  Main loop            : 0.31
% 2.63/1.35  Inferencing          : 0.14
% 2.63/1.35  Reduction            : 0.11
% 2.63/1.35  Demodulation         : 0.09
% 2.63/1.35  BG Simplification    : 0.02
% 2.63/1.35  Subsumption          : 0.03
% 2.63/1.35  Abstraction          : 0.02
% 2.63/1.35  MUC search           : 0.00
% 2.63/1.35  Cooper               : 0.00
% 2.63/1.35  Total                : 0.62
% 2.63/1.35  Index Insertion      : 0.00
% 2.63/1.35  Index Deletion       : 0.00
% 2.63/1.35  Index Matching       : 0.00
% 2.63/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
