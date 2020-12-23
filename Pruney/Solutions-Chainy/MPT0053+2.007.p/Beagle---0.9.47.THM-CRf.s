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
% DateTime   : Thu Dec  3 09:42:51 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [B_11,A_12] : k2_xboole_0(B_11,A_12) = k2_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_4])).

tff(c_157,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_157])).

tff(c_181,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_169])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),k2_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_867,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_166])).

tff(c_12,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.31  
% 2.35/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.31  %$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.35/1.31  
% 2.35/1.31  %Foreground sorts:
% 2.35/1.31  
% 2.35/1.31  
% 2.35/1.31  %Background operators:
% 2.35/1.31  
% 2.35/1.31  
% 2.35/1.31  %Foreground operators:
% 2.35/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.31  
% 2.35/1.32  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.35/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.35/1.32  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.35/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.35/1.32  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 2.35/1.32  tff(f_38, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.35/1.32  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.32  tff(c_29, plain, (![B_11, A_12]: (k2_xboole_0(B_11, A_12)=k2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.32  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.32  tff(c_45, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_29, c_4])).
% 2.35/1.32  tff(c_157, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.32  tff(c_169, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_45, c_157])).
% 2.35/1.32  tff(c_181, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_169])).
% 2.35/1.32  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.32  tff(c_166, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), k2_xboole_0(A_7, B_8))=k4_xboole_0(A_7, k2_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_157])).
% 2.35/1.32  tff(c_867, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_166])).
% 2.35/1.32  tff(c_12, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.35/1.32  tff(c_870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_867, c_12])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.32  #Sup     : 208
% 2.35/1.32  #Fact    : 0
% 2.35/1.32  #Define  : 0
% 2.35/1.32  #Split   : 0
% 2.35/1.32  #Chain   : 0
% 2.35/1.32  #Close   : 0
% 2.35/1.32  
% 2.35/1.32  Ordering : KBO
% 2.35/1.32  
% 2.35/1.32  Simplification rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Subsume      : 17
% 2.35/1.32  #Demod        : 312
% 2.35/1.32  #Tautology    : 178
% 2.35/1.32  #SimpNegUnit  : 0
% 2.35/1.32  #BackRed      : 1
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.32  Preprocessing        : 0.24
% 2.35/1.32  Parsing              : 0.13
% 2.35/1.32  CNF conversion       : 0.01
% 2.35/1.32  Main loop            : 0.32
% 2.35/1.32  Inferencing          : 0.10
% 2.35/1.32  Reduction            : 0.17
% 2.35/1.32  Demodulation         : 0.15
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.03
% 2.35/1.32  Abstraction          : 0.02
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.58
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
