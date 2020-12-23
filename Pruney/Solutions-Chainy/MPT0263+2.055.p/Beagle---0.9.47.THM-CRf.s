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
% DateTime   : Thu Dec  3 09:52:20 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   35 (  51 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  61 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_89,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(k1_tarski(A_20),B_21) = k1_xboole_0
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_22])).

tff(c_106,plain,
    ( k1_tarski('#skF_1') != k1_xboole_0
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_50])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_186,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(k1_tarski(A_27),B_28) = k1_tarski(A_27)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_213,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_50])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_213])).

tff(c_247,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k4_xboole_0(A_2,k4_xboole_0(A_2,B_3)) = k3_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(k1_tarski(A_20),k1_xboole_0) = k3_xboole_0(k1_tarski(A_20),B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_391,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(k1_tarski(A_39),B_40) = k1_tarski(A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_99])).

tff(c_20,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_401,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_20])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.24  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.24  
% 1.97/1.24  %Foreground sorts:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Background operators:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Foreground operators:
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.24  
% 2.04/1.25  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.04/1.25  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.04/1.25  tff(f_49, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.04/1.25  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.04/1.25  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.04/1.25  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.04/1.25  tff(c_89, plain, (![A_20, B_21]: (k4_xboole_0(k1_tarski(A_20), B_21)=k1_xboole_0 | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.25  tff(c_42, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_22, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.25  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_42, c_22])).
% 2.04/1.25  tff(c_106, plain, (k1_tarski('#skF_1')!=k1_xboole_0 | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_50])).
% 2.04/1.25  tff(c_135, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_106])).
% 2.04/1.25  tff(c_186, plain, (![A_27, B_28]: (k4_xboole_0(k1_tarski(A_27), B_28)=k1_tarski(A_27) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.25  tff(c_213, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_50])).
% 2.04/1.25  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_213])).
% 2.04/1.25  tff(c_247, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_106])).
% 2.04/1.25  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.25  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, k4_xboole_0(A_2, B_3))=k3_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.25  tff(c_99, plain, (![A_20, B_21]: (k4_xboole_0(k1_tarski(A_20), k1_xboole_0)=k3_xboole_0(k1_tarski(A_20), B_21) | ~r2_hidden(A_20, B_21))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 2.04/1.25  tff(c_391, plain, (![A_39, B_40]: (k3_xboole_0(k1_tarski(A_39), B_40)=k1_tarski(A_39) | ~r2_hidden(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_99])).
% 2.04/1.25  tff(c_20, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.25  tff(c_401, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_391, c_20])).
% 2.04/1.25  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_401])).
% 2.04/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  Inference rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Ref     : 0
% 2.04/1.25  #Sup     : 92
% 2.04/1.25  #Fact    : 0
% 2.04/1.25  #Define  : 0
% 2.04/1.25  #Split   : 1
% 2.04/1.25  #Chain   : 0
% 2.04/1.25  #Close   : 0
% 2.04/1.25  
% 2.04/1.25  Ordering : KBO
% 2.04/1.25  
% 2.04/1.25  Simplification rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Subsume      : 6
% 2.04/1.25  #Demod        : 11
% 2.04/1.25  #Tautology    : 35
% 2.04/1.25  #SimpNegUnit  : 6
% 2.04/1.25  #BackRed      : 1
% 2.04/1.25  
% 2.04/1.25  #Partial instantiations: 0
% 2.04/1.25  #Strategies tried      : 1
% 2.04/1.25  
% 2.04/1.25  Timing (in seconds)
% 2.04/1.25  ----------------------
% 2.04/1.26  Preprocessing        : 0.27
% 2.04/1.26  Parsing              : 0.15
% 2.04/1.26  CNF conversion       : 0.01
% 2.04/1.26  Main loop            : 0.20
% 2.04/1.26  Inferencing          : 0.09
% 2.04/1.26  Reduction            : 0.05
% 2.04/1.26  Demodulation         : 0.04
% 2.04/1.26  BG Simplification    : 0.01
% 2.04/1.26  Subsumption          : 0.03
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.50
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
