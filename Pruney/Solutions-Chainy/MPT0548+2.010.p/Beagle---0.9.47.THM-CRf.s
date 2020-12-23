%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:36 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2] : k7_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [B_7,A_8] :
      ( k2_relat_1(k7_relat_1(B_7,A_8)) = k9_relat_1(B_7,A_8)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_2] :
      ( k9_relat_1(k1_xboole_0,A_2) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_48,plain,(
    ! [A_2] : k9_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10,c_44])).

tff(c_14,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  
% 1.48/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  %$ v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.48/1.08  
% 1.48/1.08  %Foreground sorts:
% 1.48/1.08  
% 1.48/1.08  
% 1.48/1.08  %Background operators:
% 1.48/1.08  
% 1.48/1.08  
% 1.48/1.08  %Foreground operators:
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.48/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.48/1.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.48/1.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.48/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.48/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.48/1.08  
% 1.48/1.09  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.48/1.09  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.48/1.09  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.48/1.09  tff(f_32, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.48/1.09  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.48/1.09  tff(f_42, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.48/1.09  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.48/1.09  tff(c_30, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.48/1.09  tff(c_34, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_30])).
% 1.48/1.09  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.48/1.09  tff(c_6, plain, (![A_2]: (k7_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.48/1.09  tff(c_35, plain, (![B_7, A_8]: (k2_relat_1(k7_relat_1(B_7, A_8))=k9_relat_1(B_7, A_8) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.48/1.09  tff(c_44, plain, (![A_2]: (k9_relat_1(k1_xboole_0, A_2)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 1.48/1.09  tff(c_48, plain, (![A_2]: (k9_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10, c_44])).
% 1.48/1.09  tff(c_14, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.48/1.09  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 1.48/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.09  
% 1.48/1.09  Inference rules
% 1.48/1.09  ----------------------
% 1.48/1.09  #Ref     : 0
% 1.48/1.09  #Sup     : 10
% 1.48/1.09  #Fact    : 0
% 1.48/1.09  #Define  : 0
% 1.48/1.09  #Split   : 0
% 1.48/1.09  #Chain   : 0
% 1.48/1.09  #Close   : 0
% 1.48/1.09  
% 1.48/1.09  Ordering : KBO
% 1.48/1.09  
% 1.48/1.09  Simplification rules
% 1.48/1.09  ----------------------
% 1.48/1.09  #Subsume      : 0
% 1.48/1.09  #Demod        : 3
% 1.48/1.09  #Tautology    : 8
% 1.48/1.09  #SimpNegUnit  : 0
% 1.48/1.09  #BackRed      : 1
% 1.48/1.09  
% 1.48/1.09  #Partial instantiations: 0
% 1.48/1.09  #Strategies tried      : 1
% 1.48/1.09  
% 1.48/1.09  Timing (in seconds)
% 1.48/1.09  ----------------------
% 1.62/1.09  Preprocessing        : 0.23
% 1.62/1.09  Parsing              : 0.13
% 1.62/1.09  CNF conversion       : 0.01
% 1.62/1.09  Main loop            : 0.08
% 1.62/1.09  Inferencing          : 0.04
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.02
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.01
% 1.62/1.09  Abstraction          : 0.00
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.09  Total                : 0.33
% 1.62/1.09  Index Insertion      : 0.00
% 1.62/1.09  Index Deletion       : 0.00
% 1.62/1.09  Index Matching       : 0.00
% 1.62/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
