%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [C_39,A_40,B_41] :
      ( k7_relat_1(k7_relat_1(C_39,A_40),B_41) = k7_relat_1(C_39,k3_xboole_0(A_40,B_41))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [A_49,B_50] :
      ( k7_relat_1(A_49,k3_xboole_0(k1_relat_1(A_49),B_50)) = k7_relat_1(A_49,B_50)
      | ~ v1_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_94])).

tff(c_18,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_18])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.19  %$ v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.19  
% 1.87/1.20  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.87/1.20  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.87/1.20  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.87/1.20  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.20  tff(c_16, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.20  tff(c_94, plain, (![C_39, A_40, B_41]: (k7_relat_1(k7_relat_1(C_39, A_40), B_41)=k7_relat_1(C_39, k3_xboole_0(A_40, B_41)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.20  tff(c_162, plain, (![A_49, B_50]: (k7_relat_1(A_49, k3_xboole_0(k1_relat_1(A_49), B_50))=k7_relat_1(A_49, B_50) | ~v1_relat_1(A_49) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_16, c_94])).
% 1.87/1.20  tff(c_18, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.20  tff(c_175, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_162, c_18])).
% 1.87/1.20  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_175])).
% 1.87/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  Inference rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Ref     : 0
% 1.87/1.20  #Sup     : 41
% 1.87/1.20  #Fact    : 0
% 1.87/1.20  #Define  : 0
% 1.87/1.20  #Split   : 0
% 1.87/1.20  #Chain   : 0
% 1.87/1.20  #Close   : 0
% 1.87/1.20  
% 1.87/1.20  Ordering : KBO
% 1.87/1.20  
% 1.87/1.20  Simplification rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Subsume      : 0
% 1.87/1.20  #Demod        : 4
% 1.87/1.20  #Tautology    : 24
% 1.87/1.20  #SimpNegUnit  : 0
% 1.87/1.20  #BackRed      : 0
% 1.87/1.20  
% 1.87/1.20  #Partial instantiations: 0
% 1.87/1.20  #Strategies tried      : 1
% 1.87/1.20  
% 1.87/1.20  Timing (in seconds)
% 1.87/1.20  ----------------------
% 1.87/1.20  Preprocessing        : 0.29
% 1.87/1.20  Parsing              : 0.16
% 1.87/1.20  CNF conversion       : 0.02
% 1.87/1.20  Main loop            : 0.14
% 1.87/1.20  Inferencing          : 0.07
% 1.87/1.20  Reduction            : 0.04
% 1.87/1.20  Demodulation         : 0.03
% 1.87/1.20  BG Simplification    : 0.01
% 1.87/1.20  Subsumption          : 0.02
% 1.87/1.20  Abstraction          : 0.01
% 1.87/1.20  MUC search           : 0.00
% 1.87/1.20  Cooper               : 0.00
% 1.87/1.20  Total                : 0.46
% 1.87/1.21  Index Insertion      : 0.00
% 1.87/1.21  Index Deletion       : 0.00
% 1.87/1.21  Index Matching       : 0.00
% 1.87/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
