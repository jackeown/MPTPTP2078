%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:37 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  22 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_wellord1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k7_relat_1(k8_relat_1(A_4,B_5),A_4) = k2_wellord1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_8,C_9,B_10] :
      ( k8_relat_1(A_8,k7_relat_1(C_9,B_10)) = k7_relat_1(k8_relat_1(A_8,C_9),B_10)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_2','#skF_1')) != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_27,plain,
    ( k7_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_1') != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_36,plain,(
    k7_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_27])).

tff(c_40,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_36])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.08  
% 1.61/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.08  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_wellord1 > #nlpp > #skF_2 > #skF_1
% 1.61/1.08  
% 1.61/1.08  %Foreground sorts:
% 1.61/1.08  
% 1.61/1.08  
% 1.61/1.08  %Background operators:
% 1.61/1.08  
% 1.61/1.08  
% 1.61/1.08  %Foreground operators:
% 1.61/1.08  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.08  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.61/1.08  
% 1.61/1.09  tff(f_38, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 1.61/1.09  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 1.61/1.09  tff(f_29, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 1.61/1.09  tff(c_8, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.09  tff(c_4, plain, (![A_4, B_5]: (k7_relat_1(k8_relat_1(A_4, B_5), A_4)=k2_wellord1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.09  tff(c_18, plain, (![A_8, C_9, B_10]: (k8_relat_1(A_8, k7_relat_1(C_9, B_10))=k7_relat_1(k8_relat_1(A_8, C_9), B_10) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.09  tff(c_6, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_2', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.09  tff(c_27, plain, (k7_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_6])).
% 1.61/1.09  tff(c_36, plain, (k7_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_27])).
% 1.61/1.09  tff(c_40, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_36])).
% 1.61/1.09  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_40])).
% 1.61/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  Inference rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Ref     : 0
% 1.61/1.09  #Sup     : 8
% 1.61/1.09  #Fact    : 0
% 1.61/1.09  #Define  : 0
% 1.61/1.09  #Split   : 0
% 1.61/1.09  #Chain   : 0
% 1.61/1.09  #Close   : 0
% 1.61/1.09  
% 1.61/1.09  Ordering : KBO
% 1.61/1.09  
% 1.61/1.09  Simplification rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Subsume      : 0
% 1.61/1.09  #Demod        : 2
% 1.61/1.09  #Tautology    : 4
% 1.61/1.09  #SimpNegUnit  : 0
% 1.61/1.09  #BackRed      : 0
% 1.61/1.09  
% 1.61/1.09  #Partial instantiations: 0
% 1.61/1.09  #Strategies tried      : 1
% 1.61/1.09  
% 1.61/1.09  Timing (in seconds)
% 1.61/1.09  ----------------------
% 1.61/1.09  Preprocessing        : 0.26
% 1.61/1.09  Parsing              : 0.13
% 1.61/1.09  CNF conversion       : 0.01
% 1.61/1.09  Main loop            : 0.07
% 1.61/1.09  Inferencing          : 0.03
% 1.61/1.09  Reduction            : 0.02
% 1.61/1.09  Demodulation         : 0.01
% 1.61/1.09  BG Simplification    : 0.01
% 1.61/1.09  Subsumption          : 0.01
% 1.61/1.09  Abstraction          : 0.01
% 1.61/1.09  MUC search           : 0.00
% 1.61/1.09  Cooper               : 0.00
% 1.61/1.09  Total                : 0.35
% 1.61/1.09  Index Insertion      : 0.00
% 1.61/1.09  Index Deletion       : 0.00
% 1.61/1.09  Index Matching       : 0.00
% 1.61/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
