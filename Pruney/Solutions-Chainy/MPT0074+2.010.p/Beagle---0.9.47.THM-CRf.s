%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_68,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_68])).

tff(c_93,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,C_23)
      | ~ r1_xboole_0(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [A_26] :
      ( r1_xboole_0(A_26,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_27] :
      ( k3_xboole_0(A_27,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_27,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_149,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.15  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.82/1.15  
% 1.82/1.15  %Foreground sorts:
% 1.82/1.15  
% 1.82/1.15  
% 1.82/1.15  %Background operators:
% 1.82/1.15  
% 1.82/1.15  
% 1.82/1.15  %Foreground operators:
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.15  
% 1.82/1.16  tff(f_52, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.82/1.16  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.82/1.16  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.82/1.16  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.82/1.16  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.82/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.82/1.16  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.82/1.16  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.16  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.82/1.16  tff(c_46, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.16  tff(c_53, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_46])).
% 1.82/1.16  tff(c_68, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.16  tff(c_86, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_53, c_68])).
% 1.82/1.16  tff(c_93, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_86])).
% 1.82/1.16  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.82/1.16  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.82/1.16  tff(c_102, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, C_23) | ~r1_xboole_0(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.16  tff(c_134, plain, (![A_26]: (r1_xboole_0(A_26, '#skF_3') | ~r1_tarski(A_26, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_102])).
% 1.82/1.16  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.16  tff(c_142, plain, (![A_27]: (k3_xboole_0(A_27, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_27, '#skF_2'))), inference(resolution, [status(thm)], [c_134, c_2])).
% 1.82/1.16  tff(c_149, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_142])).
% 1.82/1.16  tff(c_152, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_149])).
% 1.82/1.16  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_152])).
% 1.82/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  Inference rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Ref     : 0
% 1.82/1.16  #Sup     : 37
% 1.82/1.16  #Fact    : 0
% 1.82/1.16  #Define  : 0
% 1.82/1.16  #Split   : 0
% 1.82/1.16  #Chain   : 0
% 1.82/1.16  #Close   : 0
% 1.82/1.16  
% 1.82/1.16  Ordering : KBO
% 1.82/1.16  
% 1.82/1.16  Simplification rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Subsume      : 0
% 1.82/1.16  #Demod        : 4
% 1.82/1.16  #Tautology    : 21
% 1.82/1.16  #SimpNegUnit  : 1
% 1.82/1.16  #BackRed      : 0
% 1.82/1.16  
% 1.82/1.16  #Partial instantiations: 0
% 1.82/1.16  #Strategies tried      : 1
% 1.82/1.16  
% 1.82/1.16  Timing (in seconds)
% 1.82/1.16  ----------------------
% 1.82/1.17  Preprocessing        : 0.27
% 1.82/1.17  Parsing              : 0.15
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.13
% 1.82/1.17  Inferencing          : 0.06
% 1.82/1.17  Reduction            : 0.04
% 1.82/1.17  Demodulation         : 0.03
% 1.82/1.17  BG Simplification    : 0.01
% 1.82/1.17  Subsumption          : 0.02
% 1.82/1.17  Abstraction          : 0.01
% 1.82/1.17  MUC search           : 0.00
% 1.82/1.17  Cooper               : 0.00
% 1.82/1.17  Total                : 0.43
% 1.82/1.17  Index Insertion      : 0.00
% 1.82/1.17  Index Deletion       : 0.00
% 1.82/1.17  Index Matching       : 0.00
% 1.82/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
