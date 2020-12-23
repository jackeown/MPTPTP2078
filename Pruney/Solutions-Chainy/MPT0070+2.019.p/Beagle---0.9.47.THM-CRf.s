%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.73s
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_86,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_30])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_469,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(k3_xboole_0(A_60,C_61),k3_xboole_0(B_62,C_61))
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_531,plain,(
    ! [A_64] :
      ( r1_tarski(k3_xboole_0(A_64,'#skF_5'),k1_xboole_0)
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_469])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_534,plain,(
    ! [A_64] :
      ( k4_xboole_0(k3_xboole_0(A_64,'#skF_5'),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_531,c_16])).

tff(c_622,plain,(
    ! [A_68] :
      ( k3_xboole_0(A_68,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_68,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_534])).

tff(c_629,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_622])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.53  
% 2.69/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.69/1.53  
% 2.69/1.53  %Foreground sorts:
% 2.69/1.53  
% 2.69/1.53  
% 2.69/1.53  %Background operators:
% 2.69/1.53  
% 2.69/1.53  
% 2.69/1.53  %Foreground operators:
% 2.69/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.69/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.53  
% 2.73/1.54  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.73/1.54  tff(f_78, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.73/1.54  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.73/1.54  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.73/1.54  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.73/1.54  tff(c_86, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.54  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.54  tff(c_90, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_30])).
% 2.73/1.54  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.54  tff(c_24, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.54  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.54  tff(c_104, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.54  tff(c_112, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_104])).
% 2.73/1.54  tff(c_469, plain, (![A_60, C_61, B_62]: (r1_tarski(k3_xboole_0(A_60, C_61), k3_xboole_0(B_62, C_61)) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.54  tff(c_531, plain, (![A_64]: (r1_tarski(k3_xboole_0(A_64, '#skF_5'), k1_xboole_0) | ~r1_tarski(A_64, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_469])).
% 2.73/1.54  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.54  tff(c_534, plain, (![A_64]: (k4_xboole_0(k3_xboole_0(A_64, '#skF_5'), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_531, c_16])).
% 2.73/1.54  tff(c_622, plain, (![A_68]: (k3_xboole_0(A_68, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_68, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_534])).
% 2.73/1.54  tff(c_629, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_622])).
% 2.73/1.54  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_629])).
% 2.73/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.54  
% 2.73/1.54  Inference rules
% 2.73/1.54  ----------------------
% 2.73/1.54  #Ref     : 0
% 2.73/1.54  #Sup     : 143
% 2.73/1.54  #Fact    : 0
% 2.73/1.54  #Define  : 0
% 2.73/1.54  #Split   : 4
% 2.73/1.54  #Chain   : 0
% 2.73/1.54  #Close   : 0
% 2.73/1.54  
% 2.73/1.54  Ordering : KBO
% 2.73/1.54  
% 2.73/1.54  Simplification rules
% 2.73/1.54  ----------------------
% 2.73/1.54  #Subsume      : 8
% 2.73/1.54  #Demod        : 71
% 2.73/1.54  #Tautology    : 91
% 2.73/1.54  #SimpNegUnit  : 7
% 2.73/1.54  #BackRed      : 3
% 2.73/1.54  
% 2.73/1.54  #Partial instantiations: 0
% 2.73/1.54  #Strategies tried      : 1
% 2.73/1.54  
% 2.73/1.54  Timing (in seconds)
% 2.73/1.54  ----------------------
% 2.73/1.54  Preprocessing        : 0.38
% 2.73/1.54  Parsing              : 0.21
% 2.73/1.54  CNF conversion       : 0.02
% 2.73/1.54  Main loop            : 0.32
% 2.73/1.54  Inferencing          : 0.12
% 2.73/1.54  Reduction            : 0.11
% 2.73/1.54  Demodulation         : 0.09
% 2.73/1.54  BG Simplification    : 0.01
% 2.73/1.54  Subsumption          : 0.05
% 2.73/1.54  Abstraction          : 0.01
% 2.73/1.54  MUC search           : 0.00
% 2.73/1.54  Cooper               : 0.00
% 2.73/1.54  Total                : 0.72
% 2.73/1.54  Index Insertion      : 0.00
% 2.73/1.54  Index Deletion       : 0.00
% 2.73/1.54  Index Matching       : 0.00
% 2.73/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
