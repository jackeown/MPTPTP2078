%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:39 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_72,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k3_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6])).

tff(c_89,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_142,plain,(
    ! [C_30,A_31,B_32] :
      ( k2_wellord1(k2_wellord1(C_30,A_31),B_32) = k2_wellord1(C_30,k3_xboole_0(A_31,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    k2_wellord1(k2_wellord1('#skF_2','#skF_1'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_151,plain,
    ( k2_wellord1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_16])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_89,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.14  %$ v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.14  
% 1.68/1.14  %Foreground sorts:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Background operators:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Foreground operators:
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.14  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.68/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.68/1.14  
% 1.68/1.14  tff(f_46, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 1.68/1.14  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.68/1.14  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.68/1.14  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.68/1.14  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 1.68/1.14  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.14  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.14  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.14  tff(c_53, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.14  tff(c_68, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.68/1.14  tff(c_72, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 1.68/1.14  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.14  tff(c_77, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k3_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_72, c_6])).
% 1.68/1.14  tff(c_89, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 1.68/1.14  tff(c_142, plain, (![C_30, A_31, B_32]: (k2_wellord1(k2_wellord1(C_30, A_31), B_32)=k2_wellord1(C_30, k3_xboole_0(A_31, B_32)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.14  tff(c_16, plain, (k2_wellord1(k2_wellord1('#skF_2', '#skF_1'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.14  tff(c_151, plain, (k2_wellord1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_142, c_16])).
% 1.68/1.14  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_89, c_151])).
% 1.68/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  Inference rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Ref     : 0
% 1.68/1.14  #Sup     : 34
% 1.68/1.14  #Fact    : 0
% 1.68/1.14  #Define  : 0
% 1.68/1.14  #Split   : 0
% 1.68/1.14  #Chain   : 0
% 1.68/1.14  #Close   : 0
% 1.68/1.14  
% 1.68/1.14  Ordering : KBO
% 1.68/1.14  
% 1.68/1.14  Simplification rules
% 1.68/1.14  ----------------------
% 1.68/1.15  #Subsume      : 0
% 1.68/1.15  #Demod        : 11
% 1.68/1.15  #Tautology    : 26
% 1.68/1.15  #SimpNegUnit  : 0
% 1.68/1.15  #BackRed      : 0
% 1.68/1.15  
% 1.68/1.15  #Partial instantiations: 0
% 1.68/1.15  #Strategies tried      : 1
% 1.68/1.15  
% 1.68/1.15  Timing (in seconds)
% 1.68/1.15  ----------------------
% 1.68/1.15  Preprocessing        : 0.28
% 1.68/1.15  Parsing              : 0.15
% 1.68/1.15  CNF conversion       : 0.02
% 1.68/1.15  Main loop            : 0.11
% 1.68/1.15  Inferencing          : 0.05
% 1.68/1.15  Reduction            : 0.04
% 1.68/1.15  Demodulation         : 0.03
% 1.68/1.15  BG Simplification    : 0.01
% 1.68/1.15  Subsumption          : 0.01
% 1.68/1.15  Abstraction          : 0.01
% 1.68/1.15  MUC search           : 0.00
% 1.68/1.15  Cooper               : 0.00
% 1.68/1.15  Total                : 0.42
% 1.68/1.15  Index Insertion      : 0.00
% 1.68/1.15  Index Deletion       : 0.00
% 1.68/1.15  Index Matching       : 0.00
% 1.68/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
