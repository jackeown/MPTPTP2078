%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:07 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  35 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_51,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_16])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_78,plain,(
    ! [A_18,B_19,C_20] : k3_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k3_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [C_21] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_21)) = k3_xboole_0('#skF_1',C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_65,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17,c_65])).

tff(c_131,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_73])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.17  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.17  
% 1.65/1.17  %Foreground sorts:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Background operators:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Foreground operators:
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.17  
% 1.85/1.18  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.85/1.18  tff(f_46, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 1.85/1.18  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.85/1.18  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.85/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.85/1.18  tff(c_51, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.18  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.18  tff(c_55, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_16])).
% 1.85/1.18  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.18  tff(c_56, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.18  tff(c_60, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_14, c_56])).
% 1.85/1.18  tff(c_78, plain, (![A_18, B_19, C_20]: (k3_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.18  tff(c_122, plain, (![C_21]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_21))=k3_xboole_0('#skF_1', C_21))), inference(superposition, [status(thm), theory('equality')], [c_60, c_78])).
% 1.85/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.18  tff(c_12, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.18  tff(c_17, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.85/1.18  tff(c_65, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.18  tff(c_73, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_17, c_65])).
% 1.85/1.18  tff(c_131, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122, c_73])).
% 1.85/1.18  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_131])).
% 1.85/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  Inference rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Ref     : 0
% 1.85/1.18  #Sup     : 35
% 1.85/1.18  #Fact    : 0
% 1.85/1.18  #Define  : 0
% 1.85/1.18  #Split   : 0
% 1.85/1.18  #Chain   : 0
% 1.85/1.18  #Close   : 0
% 1.85/1.18  
% 1.85/1.18  Ordering : KBO
% 1.85/1.18  
% 1.85/1.18  Simplification rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Subsume      : 0
% 1.85/1.18  #Demod        : 11
% 1.85/1.18  #Tautology    : 19
% 1.85/1.18  #SimpNegUnit  : 1
% 1.85/1.18  #BackRed      : 0
% 1.85/1.18  
% 1.85/1.18  #Partial instantiations: 0
% 1.85/1.18  #Strategies tried      : 1
% 1.85/1.18  
% 1.85/1.18  Timing (in seconds)
% 1.85/1.18  ----------------------
% 1.85/1.18  Preprocessing        : 0.26
% 1.85/1.18  Parsing              : 0.14
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.16
% 1.85/1.18  Inferencing          : 0.05
% 1.85/1.18  Reduction            : 0.07
% 1.87/1.18  Demodulation         : 0.06
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
