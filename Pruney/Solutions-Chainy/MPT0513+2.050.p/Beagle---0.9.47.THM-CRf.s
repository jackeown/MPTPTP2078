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
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_45,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_36,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33,plain,(
    ! [A_12,B_13] :
      ( v1_xboole_0(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [B_7,A_8] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_25,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_41,plain,(
    ! [A_14,B_15] :
      ( k7_relat_1(A_14,B_15) = k1_xboole_0
      | ~ v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_33,c_25])).

tff(c_45,plain,(
    ! [B_15] :
      ( k7_relat_1(k1_xboole_0,B_15) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_41])).

tff(c_49,plain,(
    ! [B_15] : k7_relat_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_45])).

tff(c_14,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.08  
% 1.52/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.08  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.52/1.08  
% 1.52/1.08  %Foreground sorts:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Background operators:
% 1.52/1.08  
% 1.52/1.08  
% 1.52/1.08  %Foreground operators:
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.52/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.52/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.52/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.52/1.08  
% 1.52/1.09  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.52/1.09  tff(f_36, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.52/1.09  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.52/1.09  tff(f_44, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_relat_1)).
% 1.52/1.09  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.52/1.09  tff(f_48, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.52/1.09  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.52/1.09  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.09  tff(c_18, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_6])).
% 1.52/1.09  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.52/1.09  tff(c_33, plain, (![A_12, B_13]: (v1_xboole_0(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.52/1.09  tff(c_22, plain, (![B_7, A_8]: (~v1_xboole_0(B_7) | B_7=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.52/1.09  tff(c_25, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.52/1.09  tff(c_41, plain, (![A_14, B_15]: (k7_relat_1(A_14, B_15)=k1_xboole_0 | ~v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_33, c_25])).
% 1.52/1.09  tff(c_45, plain, (![B_15]: (k7_relat_1(k1_xboole_0, B_15)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_41])).
% 1.52/1.09  tff(c_49, plain, (![B_15]: (k7_relat_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_45])).
% 1.52/1.09  tff(c_14, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.52/1.09  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_14])).
% 1.52/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.09  
% 1.52/1.09  Inference rules
% 1.52/1.09  ----------------------
% 1.52/1.09  #Ref     : 0
% 1.52/1.09  #Sup     : 9
% 1.52/1.09  #Fact    : 0
% 1.52/1.09  #Define  : 0
% 1.52/1.09  #Split   : 0
% 1.52/1.09  #Chain   : 0
% 1.52/1.09  #Close   : 0
% 1.52/1.09  
% 1.52/1.09  Ordering : KBO
% 1.52/1.09  
% 1.52/1.09  Simplification rules
% 1.52/1.09  ----------------------
% 1.52/1.09  #Subsume      : 0
% 1.52/1.09  #Demod        : 2
% 1.52/1.09  #Tautology    : 3
% 1.52/1.09  #SimpNegUnit  : 0
% 1.52/1.09  #BackRed      : 1
% 1.52/1.09  
% 1.52/1.09  #Partial instantiations: 0
% 1.52/1.09  #Strategies tried      : 1
% 1.52/1.09  
% 1.52/1.09  Timing (in seconds)
% 1.52/1.09  ----------------------
% 1.52/1.09  Preprocessing        : 0.23
% 1.52/1.09  Parsing              : 0.13
% 1.52/1.09  CNF conversion       : 0.01
% 1.52/1.09  Main loop            : 0.09
% 1.52/1.09  Inferencing          : 0.04
% 1.52/1.09  Reduction            : 0.02
% 1.52/1.09  Demodulation         : 0.02
% 1.52/1.09  BG Simplification    : 0.01
% 1.52/1.09  Subsumption          : 0.02
% 1.52/1.09  Abstraction          : 0.00
% 1.52/1.09  MUC search           : 0.00
% 1.52/1.09  Cooper               : 0.00
% 1.52/1.09  Total                : 0.35
% 1.52/1.09  Index Insertion      : 0.00
% 1.52/1.09  Index Deletion       : 0.00
% 1.52/1.09  Index Matching       : 0.00
% 1.52/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
