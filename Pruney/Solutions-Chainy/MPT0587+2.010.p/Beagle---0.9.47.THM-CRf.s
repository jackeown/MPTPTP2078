%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:03 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k3_xboole_0(k1_relat_1(B_8),A_7) = k1_relat_1(k7_relat_1(B_8,A_7))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,k4_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_23])).

tff(c_96,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_147,plain,(
    ! [B_23,B_24] :
      ( k1_relat_1(k7_relat_1(B_23,k4_xboole_0(k1_relat_1(B_23),B_24))) = k4_xboole_0(k1_relat_1(B_23),B_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_6,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k6_subset_1(k1_relat_1('#skF_2'),'#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_10])).

tff(c_162,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_13])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.82/1.18  
% 1.82/1.18  %Foreground sorts:
% 1.82/1.18  
% 1.82/1.18  
% 1.82/1.18  %Background operators:
% 1.82/1.18  
% 1.82/1.18  
% 1.82/1.18  %Foreground operators:
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.82/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.18  
% 1.82/1.19  tff(f_40, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 1.82/1.19  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.82/1.19  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.82/1.19  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.82/1.19  tff(f_31, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.82/1.19  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.82/1.19  tff(c_8, plain, (![B_8, A_7]: (k3_xboole_0(k1_relat_1(B_8), A_7)=k1_relat_1(k7_relat_1(B_8, A_7)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.19  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.19  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.19  tff(c_23, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.19  tff(c_32, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k3_xboole_0(A_3, k4_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_23])).
% 1.82/1.19  tff(c_96, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 1.82/1.19  tff(c_147, plain, (![B_23, B_24]: (k1_relat_1(k7_relat_1(B_23, k4_xboole_0(k1_relat_1(B_23), B_24)))=k4_xboole_0(k1_relat_1(B_23), B_24) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_8, c_96])).
% 1.82/1.19  tff(c_6, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.19  tff(c_10, plain, (k1_relat_1(k7_relat_1('#skF_2', k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.82/1.19  tff(c_13, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_10])).
% 1.82/1.19  tff(c_162, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_147, c_13])).
% 1.82/1.19  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_162])).
% 1.82/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  Inference rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Ref     : 0
% 1.82/1.19  #Sup     : 43
% 1.82/1.19  #Fact    : 0
% 1.82/1.19  #Define  : 0
% 1.82/1.19  #Split   : 0
% 1.82/1.19  #Chain   : 0
% 1.82/1.19  #Close   : 0
% 1.82/1.19  
% 1.82/1.19  Ordering : KBO
% 1.82/1.19  
% 1.82/1.19  Simplification rules
% 1.82/1.19  ----------------------
% 1.82/1.19  #Subsume      : 1
% 1.82/1.19  #Demod        : 25
% 1.82/1.19  #Tautology    : 24
% 1.82/1.19  #SimpNegUnit  : 0
% 1.82/1.19  #BackRed      : 0
% 1.82/1.19  
% 1.82/1.19  #Partial instantiations: 0
% 1.82/1.19  #Strategies tried      : 1
% 1.82/1.19  
% 1.82/1.19  Timing (in seconds)
% 1.82/1.19  ----------------------
% 1.82/1.19  Preprocessing        : 0.26
% 1.82/1.19  Parsing              : 0.14
% 1.82/1.19  CNF conversion       : 0.01
% 1.82/1.19  Main loop            : 0.12
% 1.82/1.19  Inferencing          : 0.05
% 1.82/1.20  Reduction            : 0.04
% 1.82/1.20  Demodulation         : 0.03
% 1.82/1.20  BG Simplification    : 0.01
% 1.82/1.20  Subsumption          : 0.01
% 1.82/1.20  Abstraction          : 0.01
% 1.82/1.20  MUC search           : 0.00
% 1.82/1.20  Cooper               : 0.00
% 1.82/1.20  Total                : 0.40
% 1.82/1.20  Index Insertion      : 0.00
% 1.82/1.20  Index Deletion       : 0.00
% 1.82/1.20  Index Matching       : 0.00
% 1.82/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
