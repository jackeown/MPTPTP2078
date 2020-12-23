%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:43 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_21,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_2] : k7_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_7,A_8] :
      ( k2_relat_1(k7_relat_1(B_7,A_8)) = k9_relat_1(B_7,A_8)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    ! [A_2] :
      ( k9_relat_1(k1_xboole_0,A_2) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_50,plain,(
    ! [A_2] : k9_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_8,c_46])).

tff(c_14,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.12  
% 1.58/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.12  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.58/1.12  
% 1.58/1.12  %Foreground sorts:
% 1.58/1.12  
% 1.58/1.12  
% 1.58/1.12  %Background operators:
% 1.58/1.12  
% 1.58/1.12  
% 1.58/1.12  %Foreground operators:
% 1.58/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.58/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.58/1.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.58/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.58/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.58/1.12  
% 1.58/1.13  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.58/1.13  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.58/1.13  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.58/1.13  tff(f_29, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.58/1.13  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.58/1.13  tff(f_40, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.58/1.13  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.58/1.13  tff(c_19, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.13  tff(c_21, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_19])).
% 1.58/1.13  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.58/1.13  tff(c_4, plain, (![A_2]: (k7_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.13  tff(c_37, plain, (![B_7, A_8]: (k2_relat_1(k7_relat_1(B_7, A_8))=k9_relat_1(B_7, A_8) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.13  tff(c_46, plain, (![A_2]: (k9_relat_1(k1_xboole_0, A_2)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.58/1.13  tff(c_50, plain, (![A_2]: (k9_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_21, c_8, c_46])).
% 1.58/1.13  tff(c_14, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.58/1.13  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 1.58/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.13  
% 1.58/1.13  Inference rules
% 1.58/1.13  ----------------------
% 1.58/1.13  #Ref     : 0
% 1.58/1.13  #Sup     : 12
% 1.58/1.13  #Fact    : 0
% 1.58/1.13  #Define  : 0
% 1.58/1.13  #Split   : 0
% 1.58/1.13  #Chain   : 0
% 1.58/1.13  #Close   : 0
% 1.58/1.13  
% 1.58/1.13  Ordering : KBO
% 1.58/1.13  
% 1.58/1.13  Simplification rules
% 1.58/1.13  ----------------------
% 1.58/1.13  #Subsume      : 0
% 1.58/1.13  #Demod        : 3
% 1.58/1.13  #Tautology    : 10
% 1.58/1.13  #SimpNegUnit  : 0
% 1.58/1.13  #BackRed      : 1
% 1.58/1.13  
% 1.58/1.13  #Partial instantiations: 0
% 1.58/1.13  #Strategies tried      : 1
% 1.58/1.13  
% 1.58/1.13  Timing (in seconds)
% 1.58/1.13  ----------------------
% 1.58/1.13  Preprocessing        : 0.26
% 1.58/1.13  Parsing              : 0.15
% 1.58/1.13  CNF conversion       : 0.01
% 1.58/1.13  Main loop            : 0.08
% 1.58/1.13  Inferencing          : 0.04
% 1.58/1.13  Reduction            : 0.02
% 1.58/1.13  Demodulation         : 0.02
% 1.58/1.13  BG Simplification    : 0.01
% 1.58/1.13  Subsumption          : 0.01
% 1.58/1.13  Abstraction          : 0.00
% 1.58/1.13  MUC search           : 0.00
% 1.58/1.13  Cooper               : 0.00
% 1.58/1.13  Total                : 0.36
% 1.58/1.13  Index Insertion      : 0.00
% 1.58/1.13  Index Deletion       : 0.00
% 1.58/1.13  Index Matching       : 0.00
% 1.58/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
