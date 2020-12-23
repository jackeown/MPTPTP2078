%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:44 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  58 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k1_xboole_0
      <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_12,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_20,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_13,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_26,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_13])).

tff(c_31,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_33,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_39,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_10,plain,
    ( k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0
    | k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_53])).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_6,plain,
    ( k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_55,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_59,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_59])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  %$ r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.63/1.10  
% 1.63/1.10  %Foreground sorts:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Background operators:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Foreground operators:
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.10  
% 1.63/1.11  tff(f_34, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.63/1.11  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.63/1.11  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.11  tff(c_14, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12])).
% 1.63/1.11  tff(c_20, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.11  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.11  tff(c_13, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_8])).
% 1.63/1.11  tff(c_26, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_13])).
% 1.63/1.11  tff(c_31, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 1.63/1.11  tff(c_33, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 1.63/1.11  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_12])).
% 1.63/1.11  tff(c_39, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.11  tff(c_47, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_39])).
% 1.63/1.11  tff(c_10, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0 | k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.11  tff(c_53, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47, c_10])).
% 1.63/1.11  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_53])).
% 1.63/1.11  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_8])).
% 1.63/1.11  tff(c_6, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0 | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.11  tff(c_73, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 1.63/1.11  tff(c_55, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_8])).
% 1.63/1.11  tff(c_59, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.11  tff(c_71, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_59])).
% 1.63/1.11  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_71])).
% 1.63/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  Inference rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Ref     : 0
% 1.63/1.11  #Sup     : 14
% 1.63/1.11  #Fact    : 0
% 1.63/1.11  #Define  : 0
% 1.63/1.11  #Split   : 2
% 1.63/1.11  #Chain   : 0
% 1.63/1.11  #Close   : 0
% 1.63/1.11  
% 1.63/1.11  Ordering : KBO
% 1.63/1.11  
% 1.63/1.11  Simplification rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Subsume      : 3
% 1.63/1.11  #Demod        : 4
% 1.63/1.11  #Tautology    : 10
% 1.63/1.11  #SimpNegUnit  : 2
% 1.63/1.11  #BackRed      : 0
% 1.63/1.11  
% 1.63/1.11  #Partial instantiations: 0
% 1.63/1.11  #Strategies tried      : 1
% 1.63/1.11  
% 1.63/1.11  Timing (in seconds)
% 1.63/1.11  ----------------------
% 1.63/1.11  Preprocessing        : 0.24
% 1.63/1.11  Parsing              : 0.13
% 1.63/1.12  CNF conversion       : 0.02
% 1.63/1.12  Main loop            : 0.11
% 1.63/1.12  Inferencing          : 0.05
% 1.63/1.12  Reduction            : 0.02
% 1.63/1.12  Demodulation         : 0.02
% 1.63/1.12  BG Simplification    : 0.01
% 1.63/1.12  Subsumption          : 0.02
% 1.63/1.12  Abstraction          : 0.00
% 1.63/1.12  MUC search           : 0.00
% 1.63/1.12  Cooper               : 0.00
% 1.63/1.12  Total                : 0.37
% 1.63/1.12  Index Insertion      : 0.00
% 1.63/1.12  Index Deletion       : 0.00
% 1.63/1.12  Index Matching       : 0.00
% 1.63/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
