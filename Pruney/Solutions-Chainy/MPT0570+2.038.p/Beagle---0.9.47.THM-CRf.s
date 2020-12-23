%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  65 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(k2_relat_1(B_24),A_25)
      | k10_relat_1(B_24,A_25) != k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k2_relat_1(B_33),A_34) = k1_xboole_0
      | k10_relat_1(B_33,A_34) != k1_xboole_0
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_xboole_0(A_19,C_20)
      | ~ r1_xboole_0(B_21,C_20)
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    ! [A_26,B_27,A_28] :
      ( r1_xboole_0(A_26,B_27)
      | ~ r1_tarski(A_26,A_28)
      | k3_xboole_0(A_28,B_27) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_51])).

tff(c_76,plain,(
    ! [B_27] :
      ( r1_xboole_0('#skF_1',B_27)
      | k3_xboole_0(k2_relat_1('#skF_2'),B_27) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_107,plain,(
    ! [A_34] :
      ( r1_xboole_0('#skF_1',A_34)
      | k10_relat_1('#skF_2',A_34) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_76])).

tff(c_125,plain,(
    ! [A_35] :
      ( r1_xboole_0('#skF_1',A_35)
      | k10_relat_1('#skF_2',A_35) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_107])).

tff(c_133,plain,(
    ! [A_36] :
      ( k3_xboole_0('#skF_1',A_36) = k1_xboole_0
      | k10_relat_1('#skF_2',A_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_6])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_140])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.65/1.15  
% 1.65/1.15  %Foreground sorts:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Background operators:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Foreground operators:
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.65/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.65/1.15  
% 1.65/1.15  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 1.65/1.15  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.65/1.15  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.65/1.15  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.65/1.15  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.65/1.15  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.15  tff(c_16, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.15  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.15  tff(c_61, plain, (![B_24, A_25]: (r1_xboole_0(k2_relat_1(B_24), A_25) | k10_relat_1(B_24, A_25)!=k1_xboole_0 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.15  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.15  tff(c_97, plain, (![B_33, A_34]: (k3_xboole_0(k2_relat_1(B_33), A_34)=k1_xboole_0 | k10_relat_1(B_33, A_34)!=k1_xboole_0 | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.65/1.15  tff(c_18, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.15  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.15  tff(c_51, plain, (![A_19, C_20, B_21]: (r1_xboole_0(A_19, C_20) | ~r1_xboole_0(B_21, C_20) | ~r1_tarski(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.15  tff(c_73, plain, (![A_26, B_27, A_28]: (r1_xboole_0(A_26, B_27) | ~r1_tarski(A_26, A_28) | k3_xboole_0(A_28, B_27)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_51])).
% 1.65/1.15  tff(c_76, plain, (![B_27]: (r1_xboole_0('#skF_1', B_27) | k3_xboole_0(k2_relat_1('#skF_2'), B_27)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_73])).
% 1.65/1.15  tff(c_107, plain, (![A_34]: (r1_xboole_0('#skF_1', A_34) | k10_relat_1('#skF_2', A_34)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_76])).
% 1.65/1.15  tff(c_125, plain, (![A_35]: (r1_xboole_0('#skF_1', A_35) | k10_relat_1('#skF_2', A_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_107])).
% 1.65/1.15  tff(c_133, plain, (![A_36]: (k3_xboole_0('#skF_1', A_36)=k1_xboole_0 | k10_relat_1('#skF_2', A_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_125, c_2])).
% 1.65/1.15  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.15  tff(c_140, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_133, c_6])).
% 1.65/1.15  tff(c_150, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_140])).
% 1.65/1.15  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_150])).
% 1.65/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  Inference rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Ref     : 0
% 1.65/1.15  #Sup     : 29
% 1.65/1.15  #Fact    : 0
% 1.65/1.15  #Define  : 0
% 1.65/1.15  #Split   : 1
% 1.65/1.15  #Chain   : 0
% 1.65/1.15  #Close   : 0
% 1.65/1.15  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 0
% 1.65/1.16  #Demod        : 2
% 1.65/1.16  #Tautology    : 14
% 1.65/1.16  #SimpNegUnit  : 1
% 1.65/1.16  #BackRed      : 0
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.27
% 1.65/1.16  Parsing              : 0.15
% 1.65/1.16  CNF conversion       : 0.02
% 1.65/1.16  Main loop            : 0.13
% 1.65/1.16  Inferencing          : 0.05
% 1.65/1.16  Reduction            : 0.03
% 1.65/1.16  Demodulation         : 0.02
% 1.65/1.16  BG Simplification    : 0.01
% 1.65/1.16  Subsumption          : 0.03
% 1.65/1.16  Abstraction          : 0.01
% 1.65/1.16  MUC search           : 0.00
% 1.65/1.16  Cooper               : 0.00
% 1.65/1.16  Total                : 0.42
% 1.65/1.16  Index Insertion      : 0.00
% 1.65/1.16  Index Deletion       : 0.00
% 1.65/1.16  Index Matching       : 0.00
% 1.65/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
