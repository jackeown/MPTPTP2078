%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  19 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k3_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_49,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_72,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k5_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,k3_xboole_0(A_13,B_14)),k3_xboole_0(A_13,B_14)) = k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_72])).

tff(c_87,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4,c_84])).

tff(c_10,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.22  
% 1.82/1.23  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.82/1.23  tff(f_29, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.82/1.23  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.82/1.23  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 1.82/1.23  tff(f_36, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.82/1.23  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.23  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.23  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.23  tff(c_38, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.23  tff(c_44, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 1.82/1.23  tff(c_49, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_44])).
% 1.82/1.23  tff(c_72, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k5_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.23  tff(c_84, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, k3_xboole_0(A_13, B_14)), k3_xboole_0(A_13, B_14))=k5_xboole_0(A_13, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_72])).
% 1.82/1.23  tff(c_87, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4, c_84])).
% 1.82/1.23  tff(c_10, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.82/1.23  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_10])).
% 1.82/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  Inference rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Ref     : 0
% 1.82/1.23  #Sup     : 19
% 1.82/1.23  #Fact    : 0
% 1.82/1.23  #Define  : 0
% 1.82/1.23  #Split   : 0
% 1.82/1.23  #Chain   : 0
% 1.82/1.23  #Close   : 0
% 1.82/1.23  
% 1.82/1.23  Ordering : KBO
% 1.82/1.23  
% 1.82/1.23  Simplification rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Subsume      : 0
% 1.82/1.23  #Demod        : 10
% 1.82/1.23  #Tautology    : 13
% 1.82/1.23  #SimpNegUnit  : 0
% 1.82/1.23  #BackRed      : 1
% 1.82/1.23  
% 1.82/1.23  #Partial instantiations: 0
% 1.82/1.23  #Strategies tried      : 1
% 1.82/1.23  
% 1.82/1.23  Timing (in seconds)
% 1.82/1.23  ----------------------
% 1.82/1.23  Preprocessing        : 0.35
% 1.82/1.23  Parsing              : 0.20
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.10
% 1.82/1.23  Inferencing          : 0.04
% 1.82/1.23  Reduction            : 0.03
% 1.82/1.23  Demodulation         : 0.02
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.01
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.87/1.23  Total                : 0.47
% 1.87/1.24  Index Insertion      : 0.00
% 1.87/1.24  Index Deletion       : 0.00
% 1.87/1.24  Index Matching       : 0.00
% 1.87/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
