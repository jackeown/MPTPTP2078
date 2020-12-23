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
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   36 (  49 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  48 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_29,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_84])).

tff(c_104,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_99])).

tff(c_109,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12])).

tff(c_112,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_109])).

tff(c_386,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k4_xboole_0(A_35,B_36),k3_xboole_0(A_35,C_37)) = k4_xboole_0(A_35,k4_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_413,plain,(
    ! [C_37] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_37)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_386])).

tff(c_436,plain,(
    ! [C_37] : k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_37)) = k3_xboole_0('#skF_1',C_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_413])).

tff(c_144,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k3_xboole_0(A_24,B_25),k3_xboole_0(A_24,C_26)) = k3_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [C_26] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_26)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_144])).

tff(c_16,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_253,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_16])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.33  
% 2.29/1.33  %Foreground sorts:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Background operators:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Foreground operators:
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.33  
% 2.29/1.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.29/1.34  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.29/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.29/1.34  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.29/1.34  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.29/1.34  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.29/1.34  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.29/1.34  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.34  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.34  tff(c_29, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.34  tff(c_37, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_29])).
% 2.29/1.34  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.34  tff(c_84, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.34  tff(c_99, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37, c_84])).
% 2.29/1.34  tff(c_104, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_99])).
% 2.29/1.34  tff(c_109, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104, c_12])).
% 2.29/1.34  tff(c_112, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_37, c_109])).
% 2.29/1.34  tff(c_386, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k4_xboole_0(A_35, B_36), k3_xboole_0(A_35, C_37))=k4_xboole_0(A_35, k4_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.34  tff(c_413, plain, (![C_37]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_37))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_37)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_386])).
% 2.29/1.34  tff(c_436, plain, (![C_37]: (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_37))=k3_xboole_0('#skF_1', C_37))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_413])).
% 2.29/1.34  tff(c_144, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k3_xboole_0(A_24, B_25), k3_xboole_0(A_24, C_26))=k3_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.34  tff(c_171, plain, (![C_26]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_26))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_26)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_144])).
% 2.29/1.34  tff(c_16, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.34  tff(c_253, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_16])).
% 2.29/1.34  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_436, c_253])).
% 2.29/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  Inference rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Ref     : 0
% 2.29/1.34  #Sup     : 128
% 2.29/1.34  #Fact    : 0
% 2.29/1.34  #Define  : 0
% 2.29/1.34  #Split   : 0
% 2.29/1.34  #Chain   : 0
% 2.29/1.34  #Close   : 0
% 2.29/1.34  
% 2.29/1.34  Ordering : KBO
% 2.29/1.34  
% 2.29/1.34  Simplification rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Subsume      : 0
% 2.29/1.34  #Demod        : 91
% 2.29/1.34  #Tautology    : 78
% 2.29/1.34  #SimpNegUnit  : 0
% 2.29/1.34  #BackRed      : 4
% 2.29/1.34  
% 2.29/1.34  #Partial instantiations: 0
% 2.29/1.34  #Strategies tried      : 1
% 2.29/1.34  
% 2.29/1.34  Timing (in seconds)
% 2.29/1.34  ----------------------
% 2.29/1.34  Preprocessing        : 0.29
% 2.29/1.34  Parsing              : 0.16
% 2.29/1.34  CNF conversion       : 0.02
% 2.29/1.34  Main loop            : 0.25
% 2.29/1.34  Inferencing          : 0.10
% 2.29/1.34  Reduction            : 0.08
% 2.29/1.34  Demodulation         : 0.07
% 2.29/1.34  BG Simplification    : 0.02
% 2.29/1.34  Subsumption          : 0.03
% 2.29/1.34  Abstraction          : 0.02
% 2.29/1.34  MUC search           : 0.00
% 2.29/1.34  Cooper               : 0.00
% 2.29/1.34  Total                : 0.56
% 2.29/1.34  Index Insertion      : 0.00
% 2.29/1.34  Index Deletion       : 0.00
% 2.29/1.34  Index Matching       : 0.00
% 2.29/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
