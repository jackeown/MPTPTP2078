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
% DateTime   : Thu Dec  3 10:00:46 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  38 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_34,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_23])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [A_1] : k5_relat_1(k6_relat_1(A_1),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_93,plain,(
    ! [A_14] :
      ( k7_relat_1(k1_xboole_0,A_14) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_66])).

tff(c_109,plain,(
    ! [A_16] : k7_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_93])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k2_relat_1(k7_relat_1(B_3,A_2)) = k9_relat_1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_16] :
      ( k9_relat_1(k1_xboole_0,A_16) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_4])).

tff(c_119,plain,(
    ! [A_16] : k9_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_6,c_114])).

tff(c_18,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:17:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.09  
% 1.52/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.09  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.52/1.09  
% 1.52/1.09  %Foreground sorts:
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  %Background operators:
% 1.52/1.09  
% 1.52/1.09  
% 1.52/1.09  %Foreground operators:
% 1.52/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.52/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.52/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.52/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.52/1.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.52/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.52/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.52/1.09  
% 1.67/1.10  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.67/1.10  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.67/1.10  tff(f_34, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.67/1.10  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.67/1.10  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.67/1.10  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.67/1.10  tff(f_48, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.67/1.10  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.10  tff(c_23, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.10  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_23])).
% 1.67/1.10  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.10  tff(c_86, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.10  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.10  tff(c_57, plain, (![A_10]: (k5_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.10  tff(c_66, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_57])).
% 1.67/1.10  tff(c_93, plain, (![A_14]: (k7_relat_1(k1_xboole_0, A_14)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86, c_66])).
% 1.67/1.10  tff(c_109, plain, (![A_16]: (k7_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25, c_93])).
% 1.67/1.10  tff(c_4, plain, (![B_3, A_2]: (k2_relat_1(k7_relat_1(B_3, A_2))=k9_relat_1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.10  tff(c_114, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_109, c_4])).
% 1.67/1.10  tff(c_119, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25, c_6, c_114])).
% 1.67/1.10  tff(c_18, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.10  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_18])).
% 1.67/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  Inference rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Ref     : 0
% 1.67/1.10  #Sup     : 31
% 1.67/1.10  #Fact    : 0
% 1.67/1.10  #Define  : 0
% 1.67/1.10  #Split   : 0
% 1.67/1.10  #Chain   : 0
% 1.67/1.10  #Close   : 0
% 1.67/1.10  
% 1.67/1.10  Ordering : KBO
% 1.67/1.10  
% 1.67/1.10  Simplification rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Subsume      : 0
% 1.67/1.10  #Demod        : 12
% 1.67/1.10  #Tautology    : 23
% 1.67/1.10  #SimpNegUnit  : 0
% 1.67/1.10  #BackRed      : 1
% 1.67/1.10  
% 1.67/1.10  #Partial instantiations: 0
% 1.67/1.10  #Strategies tried      : 1
% 1.67/1.10  
% 1.67/1.10  Timing (in seconds)
% 1.67/1.10  ----------------------
% 1.67/1.11  Preprocessing        : 0.25
% 1.67/1.11  Parsing              : 0.14
% 1.67/1.11  CNF conversion       : 0.01
% 1.67/1.11  Main loop            : 0.12
% 1.67/1.11  Inferencing          : 0.05
% 1.67/1.11  Reduction            : 0.03
% 1.67/1.11  Demodulation         : 0.03
% 1.67/1.11  BG Simplification    : 0.01
% 1.67/1.11  Subsumption          : 0.02
% 1.67/1.11  Abstraction          : 0.01
% 1.67/1.11  MUC search           : 0.00
% 1.67/1.11  Cooper               : 0.00
% 1.67/1.11  Total                : 0.39
% 1.67/1.11  Index Insertion      : 0.00
% 1.67/1.11  Index Deletion       : 0.00
% 1.67/1.11  Index Matching       : 0.00
% 1.67/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
