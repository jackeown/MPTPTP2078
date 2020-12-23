%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:57 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  22 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

tff(c_103,plain,(
    ! [A_43,D_44,C_45,B_46] : k2_enumset1(A_43,D_44,C_45,B_46) = k2_enumset1(A_43,B_46,C_45,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,C_3,D_4,B_2] : k2_enumset1(A_1,C_3,D_4,B_2) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_43,B_46,D_44,C_45] : k2_enumset1(A_43,B_46,D_44,C_45) = k2_enumset1(A_43,B_46,C_45,D_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2])).

tff(c_6,plain,(
    ! [B_10,C_11,A_9,D_12] : k2_enumset1(B_10,C_11,A_9,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5,D_8,C_7,B_6] : k2_enumset1(A_5,D_8,C_7,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_17])).

tff(c_19,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_20,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_19])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:08:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.36  
% 2.47/1.36  %Foreground sorts:
% 2.47/1.36  
% 2.47/1.36  
% 2.47/1.36  %Background operators:
% 2.47/1.36  
% 2.47/1.36  
% 2.47/1.36  %Foreground operators:
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.36  
% 2.47/1.37  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 2.47/1.37  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 2.47/1.37  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_enumset1)).
% 2.47/1.37  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 2.47/1.37  tff(c_103, plain, (![A_43, D_44, C_45, B_46]: (k2_enumset1(A_43, D_44, C_45, B_46)=k2_enumset1(A_43, B_46, C_45, D_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.37  tff(c_2, plain, (![A_1, C_3, D_4, B_2]: (k2_enumset1(A_1, C_3, D_4, B_2)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.37  tff(c_124, plain, (![A_43, B_46, D_44, C_45]: (k2_enumset1(A_43, B_46, D_44, C_45)=k2_enumset1(A_43, B_46, C_45, D_44))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2])).
% 2.47/1.37  tff(c_6, plain, (![B_10, C_11, A_9, D_12]: (k2_enumset1(B_10, C_11, A_9, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_4, plain, (![A_5, D_8, C_7, B_6]: (k2_enumset1(A_5, D_8, C_7, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.37  tff(c_16, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.47/1.37  tff(c_17, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.47/1.37  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_17])).
% 2.47/1.37  tff(c_19, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 2.47/1.37  tff(c_20, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_19])).
% 2.47/1.37  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_20])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 122
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 0
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 22
% 2.47/1.37  #Demod        : 6
% 2.47/1.37  #Tautology    : 30
% 2.47/1.37  #SimpNegUnit  : 0
% 2.47/1.37  #BackRed      : 1
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.47/1.37  Preprocessing        : 0.30
% 2.47/1.37  Parsing              : 0.16
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.25
% 2.47/1.37  Inferencing          : 0.08
% 2.47/1.37  Reduction            : 0.11
% 2.47/1.37  Demodulation         : 0.10
% 2.47/1.37  BG Simplification    : 0.02
% 2.47/1.37  Subsumption          : 0.04
% 2.47/1.37  Abstraction          : 0.01
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.57
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
