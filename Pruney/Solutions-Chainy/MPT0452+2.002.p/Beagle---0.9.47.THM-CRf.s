%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:41 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  49 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_xboole_0 > #nlpp > k4_relat_1 > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k3_relat_1(A) = k3_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_relat_1(k4_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] :
      ( k2_relat_1(k4_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_11] :
      ( k2_xboole_0(k1_relat_1(A_11),k2_relat_1(A_11)) = k3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_5] :
      ( k2_xboole_0(k1_relat_1(k4_relat_1(A_5)),k1_relat_1(A_5)) = k3_relat_1(k4_relat_1(A_5))
      | ~ v1_relat_1(k4_relat_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_99,plain,(
    ! [A_13] :
      ( k2_xboole_0(k1_relat_1(A_13),k1_relat_1(k4_relat_1(A_13))) = k3_relat_1(k4_relat_1(A_13))
      | ~ v1_relat_1(k4_relat_1(A_13))
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_114,plain,(
    ! [A_14] :
      ( k2_xboole_0(k1_relat_1(A_14),k2_relat_1(A_14)) = k3_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_99])).

tff(c_4,plain,(
    ! [A_3] :
      ( k2_xboole_0(k1_relat_1(A_3),k2_relat_1(A_3)) = k3_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [A_15] :
      ( k3_relat_1(k4_relat_1(A_15)) = k3_relat_1(A_15)
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(k4_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_4])).

tff(c_141,plain,(
    ! [A_16] :
      ( k3_relat_1(k4_relat_1(A_16)) = k3_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_12,plain,(
    k3_relat_1(k4_relat_1('#skF_1')) != k3_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_147,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_12])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:12:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  %$ v1_relat_1 > k2_xboole_0 > #nlpp > k4_relat_1 > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.77/1.16  
% 1.77/1.16  %Foreground sorts:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Background operators:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Foreground operators:
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.16  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.77/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.16  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.77/1.16  
% 1.77/1.17  tff(f_46, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k3_relat_1(A) = k3_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relat_1)).
% 1.77/1.17  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.77/1.17  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 1.77/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.77/1.17  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.77/1.17  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.17  tff(c_6, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.17  tff(c_10, plain, (![A_5]: (k1_relat_1(k4_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.17  tff(c_8, plain, (![A_5]: (k2_relat_1(k4_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.17  tff(c_67, plain, (![A_11]: (k2_xboole_0(k1_relat_1(A_11), k2_relat_1(A_11))=k3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.17  tff(c_79, plain, (![A_5]: (k2_xboole_0(k1_relat_1(k4_relat_1(A_5)), k1_relat_1(A_5))=k3_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_67])).
% 1.77/1.17  tff(c_99, plain, (![A_13]: (k2_xboole_0(k1_relat_1(A_13), k1_relat_1(k4_relat_1(A_13)))=k3_relat_1(k4_relat_1(A_13)) | ~v1_relat_1(k4_relat_1(A_13)) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_79])).
% 1.77/1.17  tff(c_114, plain, (![A_14]: (k2_xboole_0(k1_relat_1(A_14), k2_relat_1(A_14))=k3_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_10, c_99])).
% 1.77/1.17  tff(c_4, plain, (![A_3]: (k2_xboole_0(k1_relat_1(A_3), k2_relat_1(A_3))=k3_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.17  tff(c_136, plain, (![A_15]: (k3_relat_1(k4_relat_1(A_15))=k3_relat_1(A_15) | ~v1_relat_1(A_15) | ~v1_relat_1(k4_relat_1(A_15)) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_114, c_4])).
% 1.77/1.17  tff(c_141, plain, (![A_16]: (k3_relat_1(k4_relat_1(A_16))=k3_relat_1(A_16) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_6, c_136])).
% 1.77/1.17  tff(c_12, plain, (k3_relat_1(k4_relat_1('#skF_1'))!=k3_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.17  tff(c_147, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_12])).
% 1.77/1.17  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_147])).
% 1.77/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  Inference rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Ref     : 0
% 1.77/1.17  #Sup     : 34
% 1.77/1.17  #Fact    : 0
% 1.77/1.17  #Define  : 0
% 1.77/1.17  #Split   : 0
% 1.77/1.17  #Chain   : 0
% 1.77/1.17  #Close   : 0
% 1.77/1.17  
% 1.77/1.17  Ordering : KBO
% 1.77/1.17  
% 1.77/1.17  Simplification rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Subsume      : 1
% 1.77/1.17  #Demod        : 4
% 1.77/1.17  #Tautology    : 21
% 1.77/1.17  #SimpNegUnit  : 0
% 1.77/1.17  #BackRed      : 0
% 1.77/1.17  
% 1.77/1.17  #Partial instantiations: 0
% 1.77/1.17  #Strategies tried      : 1
% 1.77/1.17  
% 1.77/1.17  Timing (in seconds)
% 1.77/1.17  ----------------------
% 1.77/1.17  Preprocessing        : 0.25
% 1.77/1.17  Parsing              : 0.14
% 1.77/1.17  CNF conversion       : 0.01
% 1.77/1.17  Main loop            : 0.15
% 1.77/1.17  Inferencing          : 0.06
% 1.77/1.17  Reduction            : 0.05
% 1.77/1.17  Demodulation         : 0.04
% 1.77/1.17  BG Simplification    : 0.01
% 1.77/1.17  Subsumption          : 0.02
% 1.77/1.17  Abstraction          : 0.01
% 1.77/1.17  MUC search           : 0.00
% 1.77/1.17  Cooper               : 0.00
% 1.77/1.17  Total                : 0.42
% 1.77/1.17  Index Insertion      : 0.00
% 1.77/1.17  Index Deletion       : 0.00
% 1.77/1.17  Index Matching       : 0.00
% 1.77/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
