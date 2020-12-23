%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:06 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  27 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8] :
      ( k7_relat_1(A_8,k1_relat_1(A_8)) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [C_14,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_14,A_15),B_16) = k7_relat_1(C_14,k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_19,B_20] :
      ( k7_relat_1(A_19,k3_xboole_0(k1_relat_1(A_19),B_20)) = k7_relat_1(A_19,B_20)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_176,plain,(
    ! [A_21,B_22] :
      ( k7_relat_1(A_21,k3_xboole_0(B_22,k1_relat_1(A_21))) = k7_relat_1(A_21,B_22)
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_10,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_193,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_13])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  %$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.68/1.17  
% 1.68/1.17  %Foreground sorts:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Background operators:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Foreground operators:
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.68/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.17  
% 1.90/1.18  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.90/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.90/1.18  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.90/1.18  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.90/1.18  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.90/1.18  tff(c_8, plain, (![A_8]: (k7_relat_1(A_8, k1_relat_1(A_8))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.18  tff(c_79, plain, (![C_14, A_15, B_16]: (k7_relat_1(k7_relat_1(C_14, A_15), B_16)=k7_relat_1(C_14, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.18  tff(c_141, plain, (![A_19, B_20]: (k7_relat_1(A_19, k3_xboole_0(k1_relat_1(A_19), B_20))=k7_relat_1(A_19, B_20) | ~v1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_8, c_79])).
% 1.90/1.18  tff(c_176, plain, (![A_21, B_22]: (k7_relat_1(A_21, k3_xboole_0(B_22, k1_relat_1(A_21)))=k7_relat_1(A_21, B_22) | ~v1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 1.90/1.18  tff(c_10, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.18  tff(c_13, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.90/1.18  tff(c_193, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_13])).
% 1.90/1.18  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_193])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 53
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 7
% 1.90/1.18  #Demod        : 3
% 1.90/1.18  #Tautology    : 20
% 1.90/1.18  #SimpNegUnit  : 0
% 1.90/1.18  #BackRed      : 0
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.18  Preprocessing        : 0.27
% 1.90/1.18  Parsing              : 0.14
% 1.90/1.18  CNF conversion       : 0.01
% 1.90/1.19  Main loop            : 0.16
% 1.90/1.19  Inferencing          : 0.07
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.04
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
