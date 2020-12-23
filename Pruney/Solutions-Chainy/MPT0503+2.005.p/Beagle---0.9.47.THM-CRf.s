%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(k7_relat_1(B,A),A) = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_29,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_48,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = k3_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_65,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_109,plain,(
    ! [C_16,A_17,B_18] :
      ( k7_relat_1(k7_relat_1(C_16,A_17),B_18) = k7_relat_1(C_16,k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_118,plain,
    ( k7_relat_1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_10])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_65,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  %$ v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.61/1.12  
% 1.61/1.12  %Foreground sorts:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Background operators:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Foreground operators:
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.12  
% 1.72/1.12  tff(f_40, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(k7_relat_1(B, A), A) = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_relat_1)).
% 1.72/1.12  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.72/1.12  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.72/1.12  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.72/1.12  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.72/1.12  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.72/1.12  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.12  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.12  tff(c_29, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.12  tff(c_44, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_29])).
% 1.72/1.12  tff(c_48, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 1.72/1.12  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.12  tff(c_53, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=k3_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6])).
% 1.72/1.12  tff(c_65, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_53])).
% 1.72/1.12  tff(c_109, plain, (![C_16, A_17, B_18]: (k7_relat_1(k7_relat_1(C_16, A_17), B_18)=k7_relat_1(C_16, k3_xboole_0(A_17, B_18)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.12  tff(c_10, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.72/1.12  tff(c_118, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_10])).
% 1.72/1.12  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_65, c_118])).
% 1.72/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.12  
% 1.72/1.12  Inference rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Ref     : 0
% 1.72/1.12  #Sup     : 28
% 1.72/1.12  #Fact    : 0
% 1.72/1.12  #Define  : 0
% 1.72/1.12  #Split   : 0
% 1.72/1.12  #Chain   : 0
% 1.72/1.12  #Close   : 0
% 1.72/1.12  
% 1.72/1.12  Ordering : KBO
% 1.72/1.13  
% 1.72/1.13  Simplification rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Subsume      : 0
% 1.72/1.13  #Demod        : 11
% 1.72/1.13  #Tautology    : 20
% 1.72/1.13  #SimpNegUnit  : 0
% 1.72/1.13  #BackRed      : 0
% 1.72/1.13  
% 1.72/1.13  #Partial instantiations: 0
% 1.72/1.13  #Strategies tried      : 1
% 1.72/1.13  
% 1.72/1.13  Timing (in seconds)
% 1.72/1.13  ----------------------
% 1.72/1.13  Preprocessing        : 0.25
% 1.72/1.13  Parsing              : 0.14
% 1.72/1.13  CNF conversion       : 0.01
% 1.72/1.13  Main loop            : 0.11
% 1.72/1.13  Inferencing          : 0.06
% 1.72/1.13  Reduction            : 0.03
% 1.72/1.13  Demodulation         : 0.03
% 1.72/1.13  BG Simplification    : 0.01
% 1.72/1.13  Subsumption          : 0.01
% 1.72/1.13  Abstraction          : 0.01
% 1.72/1.13  MUC search           : 0.00
% 1.72/1.13  Cooper               : 0.00
% 1.72/1.13  Total                : 0.39
% 1.72/1.13  Index Insertion      : 0.00
% 1.72/1.13  Index Deletion       : 0.00
% 1.72/1.13  Index Matching       : 0.00
% 1.72/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
