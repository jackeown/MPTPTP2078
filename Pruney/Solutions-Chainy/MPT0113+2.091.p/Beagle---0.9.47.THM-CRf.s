%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:23 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  62 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_143,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_155,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_24])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_25,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_10,c_25])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_179,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    ! [C_41] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_41)) = k4_xboole_0(k1_xboole_0,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_179])).

tff(c_887,plain,(
    ! [C_73] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_73)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_213])).

tff(c_955,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_887])).

tff(c_977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_955])).

tff(c_978,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1159,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_xboole_0(A_89,C_90)
      | ~ r1_xboole_0(B_91,C_90)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1179,plain,(
    ! [A_94,B_95,A_96] :
      ( r1_xboole_0(A_94,B_95)
      | ~ r1_tarski(A_94,k4_xboole_0(A_96,B_95)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1159])).

tff(c_1202,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1179])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_978,c_1202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:07:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.43  
% 2.58/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.43  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.58/1.43  
% 2.58/1.43  %Foreground sorts:
% 2.58/1.43  
% 2.58/1.43  
% 2.58/1.43  %Background operators:
% 2.58/1.43  
% 2.58/1.43  
% 2.58/1.43  %Foreground operators:
% 2.58/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.43  
% 2.58/1.44  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.58/1.44  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.58/1.44  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.58/1.44  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.58/1.44  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.44  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.58/1.44  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.58/1.44  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.58/1.44  tff(c_143, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.44  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.44  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.58/1.44  tff(c_155, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_143, c_24])).
% 2.58/1.44  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.44  tff(c_25, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.44  tff(c_35, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_10, c_25])).
% 2.58/1.44  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.44  tff(c_60, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.44  tff(c_72, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_60])).
% 2.58/1.44  tff(c_20, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.44  tff(c_71, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_60])).
% 2.58/1.44  tff(c_179, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.44  tff(c_213, plain, (![C_41]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_41))=k4_xboole_0(k1_xboole_0, C_41))), inference(superposition, [status(thm), theory('equality')], [c_71, c_179])).
% 2.58/1.44  tff(c_887, plain, (![C_73]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_73))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_213])).
% 2.58/1.44  tff(c_955, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35, c_887])).
% 2.58/1.44  tff(c_977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_955])).
% 2.58/1.44  tff(c_978, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.58/1.44  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.44  tff(c_1159, plain, (![A_89, C_90, B_91]: (r1_xboole_0(A_89, C_90) | ~r1_xboole_0(B_91, C_90) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.44  tff(c_1179, plain, (![A_94, B_95, A_96]: (r1_xboole_0(A_94, B_95) | ~r1_tarski(A_94, k4_xboole_0(A_96, B_95)))), inference(resolution, [status(thm)], [c_16, c_1159])).
% 2.58/1.44  tff(c_1202, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_1179])).
% 2.58/1.44  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_978, c_1202])).
% 2.58/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.44  
% 2.58/1.44  Inference rules
% 2.58/1.44  ----------------------
% 2.58/1.44  #Ref     : 0
% 2.58/1.44  #Sup     : 302
% 2.58/1.44  #Fact    : 0
% 2.58/1.44  #Define  : 0
% 2.58/1.44  #Split   : 1
% 2.58/1.44  #Chain   : 0
% 2.58/1.44  #Close   : 0
% 2.58/1.44  
% 2.58/1.44  Ordering : KBO
% 2.58/1.44  
% 2.58/1.44  Simplification rules
% 2.58/1.44  ----------------------
% 2.58/1.44  #Subsume      : 11
% 2.58/1.44  #Demod        : 170
% 2.58/1.44  #Tautology    : 197
% 2.58/1.44  #SimpNegUnit  : 2
% 2.58/1.44  #BackRed      : 0
% 2.58/1.44  
% 2.58/1.44  #Partial instantiations: 0
% 2.58/1.44  #Strategies tried      : 1
% 2.58/1.44  
% 2.58/1.44  Timing (in seconds)
% 2.58/1.44  ----------------------
% 2.58/1.44  Preprocessing        : 0.29
% 2.58/1.44  Parsing              : 0.16
% 2.58/1.44  CNF conversion       : 0.02
% 2.58/1.44  Main loop            : 0.36
% 2.58/1.44  Inferencing          : 0.14
% 2.58/1.44  Reduction            : 0.12
% 2.58/1.44  Demodulation         : 0.09
% 2.58/1.44  BG Simplification    : 0.01
% 2.58/1.44  Subsumption          : 0.05
% 2.58/1.44  Abstraction          : 0.02
% 2.58/1.44  MUC search           : 0.00
% 2.58/1.44  Cooper               : 0.00
% 2.58/1.44  Total                : 0.67
% 2.58/1.44  Index Insertion      : 0.00
% 2.58/1.44  Index Deletion       : 0.00
% 2.58/1.44  Index Matching       : 0.00
% 2.58/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
