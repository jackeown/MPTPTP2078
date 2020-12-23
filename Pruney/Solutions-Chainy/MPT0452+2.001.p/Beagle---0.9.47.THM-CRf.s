%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:41 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  56 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k3_relat_1(A) = k3_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(B_16,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_tarski(k2_tarski(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [B_16,A_15] : k2_xboole_0(B_16,A_15) = k2_xboole_0(A_15,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4])).

tff(c_10,plain,(
    ! [A_7] :
      ( k2_relat_1(k4_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_relat_1(k4_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_20] :
      ( k2_xboole_0(k2_relat_1(A_20),k2_relat_1(k4_relat_1(A_20))) = k3_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_140])).

tff(c_169,plain,(
    ! [A_7] :
      ( k2_xboole_0(k2_relat_1(A_7),k1_relat_1(A_7)) = k3_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_188,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(k4_relat_1(A_22))
      | ~ v1_relat_1(k4_relat_1(A_22))
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_169])).

tff(c_6,plain,(
    ! [A_5] :
      ( k2_xboole_0(k1_relat_1(A_5),k2_relat_1(A_5)) = k3_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    ! [A_24] :
      ( k3_relat_1(k4_relat_1(A_24)) = k3_relat_1(A_24)
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(k4_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6])).

tff(c_230,plain,(
    ! [A_25] :
      ( k3_relat_1(k4_relat_1(A_25)) = k3_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_14,plain,(
    k3_relat_1(k4_relat_1('#skF_1')) != k3_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_236,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_14])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.19  %$ v1_relat_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.89/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.19  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.89/1.19  
% 1.92/1.20  tff(f_48, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k3_relat_1(A) = k3_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relat_1)).
% 1.92/1.20  tff(f_37, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.92/1.20  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.92/1.20  tff(f_29, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.92/1.20  tff(f_43, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.92/1.20  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.92/1.20  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.20  tff(c_8, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.20  tff(c_60, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.20  tff(c_84, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(B_16, A_15))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 1.92/1.20  tff(c_4, plain, (![A_3, B_4]: (k3_tarski(k2_tarski(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.20  tff(c_90, plain, (![B_16, A_15]: (k2_xboole_0(B_16, A_15)=k2_xboole_0(A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_84, c_4])).
% 1.92/1.20  tff(c_10, plain, (![A_7]: (k2_relat_1(k4_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.20  tff(c_12, plain, (![A_7]: (k1_relat_1(k4_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.20  tff(c_140, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.20  tff(c_157, plain, (![A_20]: (k2_xboole_0(k2_relat_1(A_20), k2_relat_1(k4_relat_1(A_20)))=k3_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_12, c_140])).
% 1.92/1.20  tff(c_169, plain, (![A_7]: (k2_xboole_0(k2_relat_1(A_7), k1_relat_1(A_7))=k3_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_157])).
% 1.92/1.20  tff(c_188, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(k4_relat_1(A_22)) | ~v1_relat_1(k4_relat_1(A_22)) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_169])).
% 1.92/1.20  tff(c_6, plain, (![A_5]: (k2_xboole_0(k1_relat_1(A_5), k2_relat_1(A_5))=k3_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.20  tff(c_225, plain, (![A_24]: (k3_relat_1(k4_relat_1(A_24))=k3_relat_1(A_24) | ~v1_relat_1(A_24) | ~v1_relat_1(k4_relat_1(A_24)) | ~v1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_188, c_6])).
% 1.92/1.20  tff(c_230, plain, (![A_25]: (k3_relat_1(k4_relat_1(A_25))=k3_relat_1(A_25) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_8, c_225])).
% 1.92/1.20  tff(c_14, plain, (k3_relat_1(k4_relat_1('#skF_1'))!=k3_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.20  tff(c_236, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_14])).
% 1.92/1.20  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_236])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 56
% 1.92/1.20  #Fact    : 0
% 1.92/1.20  #Define  : 0
% 1.92/1.20  #Split   : 0
% 1.92/1.20  #Chain   : 0
% 1.92/1.20  #Close   : 0
% 1.92/1.20  
% 1.92/1.20  Ordering : KBO
% 1.92/1.20  
% 1.92/1.20  Simplification rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Subsume      : 2
% 1.92/1.20  #Demod        : 7
% 1.92/1.20  #Tautology    : 38
% 1.92/1.20  #SimpNegUnit  : 0
% 1.92/1.20  #BackRed      : 0
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.92/1.20  Preprocessing        : 0.26
% 1.92/1.20  Parsing              : 0.14
% 1.92/1.20  CNF conversion       : 0.01
% 1.92/1.20  Main loop            : 0.18
% 1.92/1.20  Inferencing          : 0.07
% 1.92/1.20  Reduction            : 0.06
% 1.92/1.20  Demodulation         : 0.05
% 1.92/1.20  BG Simplification    : 0.01
% 1.92/1.20  Subsumption          : 0.03
% 1.92/1.20  Abstraction          : 0.01
% 1.92/1.20  MUC search           : 0.00
% 1.92/1.20  Cooper               : 0.00
% 1.92/1.20  Total                : 0.46
% 1.92/1.20  Index Insertion      : 0.00
% 1.92/1.20  Index Deletion       : 0.00
% 1.92/1.20  Index Matching       : 0.00
% 1.92/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
