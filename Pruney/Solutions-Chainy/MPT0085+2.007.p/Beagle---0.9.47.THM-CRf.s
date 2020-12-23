%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_126,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k3_xboole_0(A_17,B_18),k3_xboole_0(A_17,C_19)) = k3_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_144,plain,(
    ! [B_18] : k3_xboole_0('#skF_1',k2_xboole_0(B_18,'#skF_2')) = k2_xboole_0(k3_xboole_0('#skF_1',B_18),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_126])).

tff(c_154,plain,(
    ! [B_18] : k3_xboole_0('#skF_1',k2_xboole_0(B_18,'#skF_2')) = k3_xboole_0('#skF_1',B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_144])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.15  
% 1.77/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  %$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.77/1.15  
% 1.77/1.15  %Foreground sorts:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Background operators:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Foreground operators:
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.15  
% 1.77/1.16  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.77/1.16  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 1.77/1.16  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.77/1.16  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.77/1.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.77/1.16  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.16  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.16  tff(c_113, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.16  tff(c_121, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_113])).
% 1.77/1.16  tff(c_126, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k3_xboole_0(A_17, C_19))=k3_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.16  tff(c_144, plain, (![B_18]: (k3_xboole_0('#skF_1', k2_xboole_0(B_18, '#skF_2'))=k2_xboole_0(k3_xboole_0('#skF_1', B_18), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_121, c_126])).
% 1.77/1.16  tff(c_154, plain, (![B_18]: (k3_xboole_0('#skF_1', k2_xboole_0(B_18, '#skF_2'))=k3_xboole_0('#skF_1', B_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_144])).
% 1.77/1.16  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.16  tff(c_12, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.77/1.16  tff(c_15, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.77/1.16  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_15])).
% 1.77/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  Inference rules
% 1.77/1.16  ----------------------
% 1.77/1.16  #Ref     : 0
% 1.77/1.16  #Sup     : 45
% 1.77/1.16  #Fact    : 0
% 1.77/1.16  #Define  : 0
% 1.77/1.16  #Split   : 0
% 1.77/1.16  #Chain   : 0
% 1.77/1.16  #Close   : 0
% 1.77/1.16  
% 1.77/1.16  Ordering : KBO
% 1.77/1.16  
% 1.77/1.16  Simplification rules
% 1.77/1.16  ----------------------
% 1.77/1.16  #Subsume      : 0
% 1.77/1.16  #Demod        : 18
% 1.77/1.16  #Tautology    : 32
% 1.77/1.16  #SimpNegUnit  : 0
% 1.77/1.16  #BackRed      : 1
% 1.77/1.16  
% 1.77/1.16  #Partial instantiations: 0
% 1.77/1.16  #Strategies tried      : 1
% 1.77/1.16  
% 1.77/1.16  Timing (in seconds)
% 1.77/1.16  ----------------------
% 1.77/1.16  Preprocessing        : 0.25
% 1.77/1.16  Parsing              : 0.14
% 1.77/1.16  CNF conversion       : 0.01
% 1.77/1.16  Main loop            : 0.15
% 1.77/1.16  Inferencing          : 0.05
% 1.77/1.16  Reduction            : 0.06
% 1.77/1.16  Demodulation         : 0.05
% 1.77/1.16  BG Simplification    : 0.01
% 1.77/1.16  Subsumption          : 0.02
% 1.77/1.16  Abstraction          : 0.01
% 1.77/1.16  MUC search           : 0.00
% 1.77/1.16  Cooper               : 0.00
% 1.77/1.16  Total                : 0.41
% 1.77/1.16  Index Insertion      : 0.00
% 1.77/1.16  Index Deletion       : 0.00
% 1.77/1.16  Index Matching       : 0.00
% 1.77/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
