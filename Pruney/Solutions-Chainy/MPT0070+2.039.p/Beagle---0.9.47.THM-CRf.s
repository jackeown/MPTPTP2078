%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_57,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_61,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_26])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_62,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_248,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(k3_xboole_0(A_48,C_49),k3_xboole_0(B_50,C_49))
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_388,plain,(
    ! [A_57] :
      ( r1_tarski(k3_xboole_0(A_57,'#skF_5'),k1_xboole_0)
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_248])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_391,plain,(
    ! [A_57] :
      ( k2_xboole_0(k3_xboole_0(A_57,'#skF_5'),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_388,c_12])).

tff(c_421,plain,(
    ! [A_59] :
      ( k3_xboole_0(A_59,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_59,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_391])).

tff(c_424,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_421])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:54:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.24  
% 2.16/1.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.16/1.25  tff(f_76, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.16/1.25  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.16/1.25  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.16/1.25  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.16/1.25  tff(c_57, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.25  tff(c_26, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.25  tff(c_61, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_26])).
% 2.16/1.25  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.25  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.25  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.25  tff(c_62, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.25  tff(c_70, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.16/1.25  tff(c_248, plain, (![A_48, C_49, B_50]: (r1_tarski(k3_xboole_0(A_48, C_49), k3_xboole_0(B_50, C_49)) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.25  tff(c_388, plain, (![A_57]: (r1_tarski(k3_xboole_0(A_57, '#skF_5'), k1_xboole_0) | ~r1_tarski(A_57, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_248])).
% 2.16/1.25  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.25  tff(c_391, plain, (![A_57]: (k2_xboole_0(k3_xboole_0(A_57, '#skF_5'), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_388, c_12])).
% 2.16/1.25  tff(c_421, plain, (![A_59]: (k3_xboole_0(A_59, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_59, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_391])).
% 2.16/1.25  tff(c_424, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_421])).
% 2.16/1.25  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_424])).
% 2.16/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  Inference rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Ref     : 0
% 2.16/1.25  #Sup     : 95
% 2.16/1.25  #Fact    : 0
% 2.16/1.25  #Define  : 0
% 2.16/1.25  #Split   : 3
% 2.16/1.25  #Chain   : 0
% 2.16/1.25  #Close   : 0
% 2.16/1.25  
% 2.16/1.25  Ordering : KBO
% 2.16/1.25  
% 2.16/1.25  Simplification rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Subsume      : 7
% 2.16/1.25  #Demod        : 51
% 2.16/1.25  #Tautology    : 57
% 2.16/1.25  #SimpNegUnit  : 5
% 2.16/1.25  #BackRed      : 1
% 2.16/1.25  
% 2.16/1.25  #Partial instantiations: 0
% 2.16/1.25  #Strategies tried      : 1
% 2.16/1.25  
% 2.16/1.25  Timing (in seconds)
% 2.16/1.25  ----------------------
% 2.16/1.25  Preprocessing        : 0.27
% 2.16/1.25  Parsing              : 0.15
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.24
% 2.16/1.25  Inferencing          : 0.10
% 2.16/1.25  Reduction            : 0.07
% 2.16/1.25  Demodulation         : 0.05
% 2.16/1.25  BG Simplification    : 0.01
% 2.16/1.25  Subsumption          : 0.03
% 2.16/1.26  Abstraction          : 0.01
% 2.16/1.26  MUC search           : 0.00
% 2.16/1.26  Cooper               : 0.00
% 2.16/1.26  Total                : 0.53
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
