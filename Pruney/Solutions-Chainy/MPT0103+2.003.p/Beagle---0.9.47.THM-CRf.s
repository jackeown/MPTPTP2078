%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15,plain,(
    ! [B_17,A_18] : k3_xboole_0(B_17,A_18) = k3_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [B_17,A_18] : r1_tarski(k3_xboole_0(B_17,A_18),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_25,D_26,B_27,C_28] :
      ( r1_tarski(k4_xboole_0(A_25,D_26),k4_xboole_0(B_27,C_28))
      | ~ r1_tarski(C_28,D_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [A_33,D_34,A_35,B_36] :
      ( r1_tarski(k4_xboole_0(A_33,D_34),k5_xboole_0(A_35,B_36))
      | ~ r1_tarski(k3_xboole_0(A_35,B_36),D_34)
      | ~ r1_tarski(A_33,k2_xboole_0(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_12,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_127,c_12])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.63/1.12  
% 1.63/1.12  %Foreground sorts:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Background operators:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Foreground operators:
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.63/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.12  
% 1.63/1.13  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.63/1.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.13  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.63/1.13  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 1.63/1.13  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_xboole_1)).
% 1.63/1.13  tff(f_42, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 1.63/1.13  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.13  tff(c_15, plain, (![B_17, A_18]: (k3_xboole_0(B_17, A_18)=k3_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.13  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.13  tff(c_30, plain, (![B_17, A_18]: (r1_tarski(k3_xboole_0(B_17, A_18), A_18))), inference(superposition, [status(thm), theory('equality')], [c_15, c_6])).
% 1.63/1.13  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.13  tff(c_107, plain, (![A_25, D_26, B_27, C_28]: (r1_tarski(k4_xboole_0(A_25, D_26), k4_xboole_0(B_27, C_28)) | ~r1_tarski(C_28, D_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.13  tff(c_127, plain, (![A_33, D_34, A_35, B_36]: (r1_tarski(k4_xboole_0(A_33, D_34), k5_xboole_0(A_35, B_36)) | ~r1_tarski(k3_xboole_0(A_35, B_36), D_34) | ~r1_tarski(A_33, k2_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 1.63/1.13  tff(c_12, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.13  tff(c_130, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_127, c_12])).
% 1.63/1.13  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_30, c_130])).
% 1.63/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  Inference rules
% 1.63/1.13  ----------------------
% 1.63/1.13  #Ref     : 0
% 1.63/1.13  #Sup     : 31
% 1.63/1.13  #Fact    : 0
% 1.63/1.13  #Define  : 0
% 1.63/1.13  #Split   : 0
% 1.63/1.13  #Chain   : 0
% 1.63/1.13  #Close   : 0
% 1.63/1.13  
% 1.63/1.13  Ordering : KBO
% 1.63/1.13  
% 1.63/1.13  Simplification rules
% 1.63/1.13  ----------------------
% 1.63/1.13  #Subsume      : 0
% 1.63/1.13  #Demod        : 8
% 1.63/1.13  #Tautology    : 20
% 1.63/1.13  #SimpNegUnit  : 0
% 1.63/1.13  #BackRed      : 0
% 1.63/1.13  
% 1.63/1.13  #Partial instantiations: 0
% 1.63/1.13  #Strategies tried      : 1
% 1.63/1.13  
% 1.63/1.13  Timing (in seconds)
% 1.63/1.13  ----------------------
% 1.63/1.14  Preprocessing        : 0.25
% 1.63/1.14  Parsing              : 0.14
% 1.63/1.14  CNF conversion       : 0.01
% 1.63/1.14  Main loop            : 0.14
% 1.63/1.14  Inferencing          : 0.05
% 1.63/1.14  Reduction            : 0.05
% 1.63/1.14  Demodulation         : 0.04
% 1.63/1.14  BG Simplification    : 0.01
% 1.63/1.14  Subsumption          : 0.02
% 1.63/1.14  Abstraction          : 0.01
% 1.63/1.14  MUC search           : 0.00
% 1.63/1.14  Cooper               : 0.00
% 1.63/1.14  Total                : 0.41
% 1.63/1.14  Index Insertion      : 0.00
% 1.63/1.14  Index Deletion       : 0.00
% 1.63/1.14  Index Matching       : 0.00
% 1.63/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
