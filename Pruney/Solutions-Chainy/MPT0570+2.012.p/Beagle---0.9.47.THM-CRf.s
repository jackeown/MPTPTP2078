%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(k2_relat_1(B_19),A_20)
      | k10_relat_1(B_19,A_20) != k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [B_23,A_24] :
      ( k3_xboole_0(k2_relat_1(B_23),A_24) = k1_xboole_0
      | k10_relat_1(B_23,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_143,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,k2_relat_1(B_28)) = k1_xboole_0
      | k10_relat_1(B_28,A_27) != k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_63])).

tff(c_190,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_160])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.26  
% 1.88/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.27  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.27  
% 1.88/1.27  %Foreground sorts:
% 1.88/1.27  
% 1.88/1.27  
% 1.88/1.27  %Background operators:
% 1.88/1.27  
% 1.88/1.27  
% 1.88/1.27  %Foreground operators:
% 1.88/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.27  
% 1.88/1.27  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.88/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.88/1.27  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.88/1.27  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.88/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.88/1.27  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.27  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.27  tff(c_14, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.27  tff(c_79, plain, (![B_19, A_20]: (r1_xboole_0(k2_relat_1(B_19), A_20) | k10_relat_1(B_19, A_20)!=k1_xboole_0 | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.27  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.27  tff(c_97, plain, (![B_23, A_24]: (k3_xboole_0(k2_relat_1(B_23), A_24)=k1_xboole_0 | k10_relat_1(B_23, A_24)!=k1_xboole_0 | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_79, c_4])).
% 1.88/1.27  tff(c_143, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k2_relat_1(B_28))=k1_xboole_0 | k10_relat_1(B_28, A_27)!=k1_xboole_0 | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 1.88/1.27  tff(c_16, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.27  tff(c_59, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.27  tff(c_63, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_16, c_59])).
% 1.88/1.27  tff(c_160, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_63])).
% 1.88/1.27  tff(c_190, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_160])).
% 1.88/1.27  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_190])).
% 1.88/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.27  
% 1.88/1.27  Inference rules
% 1.88/1.27  ----------------------
% 1.88/1.27  #Ref     : 0
% 1.88/1.27  #Sup     : 42
% 1.88/1.27  #Fact    : 0
% 1.88/1.27  #Define  : 0
% 1.88/1.28  #Split   : 0
% 1.88/1.28  #Chain   : 0
% 1.88/1.28  #Close   : 0
% 1.88/1.28  
% 1.88/1.28  Ordering : KBO
% 1.88/1.28  
% 1.88/1.28  Simplification rules
% 1.88/1.28  ----------------------
% 1.88/1.28  #Subsume      : 3
% 1.88/1.28  #Demod        : 4
% 1.88/1.28  #Tautology    : 20
% 1.88/1.28  #SimpNegUnit  : 1
% 1.88/1.28  #BackRed      : 0
% 1.88/1.28  
% 1.88/1.28  #Partial instantiations: 0
% 1.88/1.28  #Strategies tried      : 1
% 1.88/1.28  
% 1.88/1.28  Timing (in seconds)
% 1.88/1.28  ----------------------
% 1.88/1.28  Preprocessing        : 0.29
% 1.88/1.28  Parsing              : 0.16
% 1.88/1.28  CNF conversion       : 0.02
% 1.88/1.28  Main loop            : 0.14
% 1.88/1.28  Inferencing          : 0.06
% 1.88/1.28  Reduction            : 0.04
% 1.88/1.28  Demodulation         : 0.03
% 1.88/1.28  BG Simplification    : 0.01
% 1.88/1.28  Subsumption          : 0.02
% 1.88/1.28  Abstraction          : 0.01
% 1.88/1.28  MUC search           : 0.00
% 1.88/1.28  Cooper               : 0.00
% 1.88/1.28  Total                : 0.45
% 1.88/1.28  Index Insertion      : 0.00
% 1.88/1.28  Index Deletion       : 0.00
% 1.88/1.28  Index Matching       : 0.00
% 1.88/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
