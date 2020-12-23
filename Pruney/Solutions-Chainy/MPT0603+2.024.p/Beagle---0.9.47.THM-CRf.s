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
% DateTime   : Thu Dec  3 10:02:26 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  44 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_xboole_0(A_14,C_15)
      | ~ r1_xboole_0(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_14] :
      ( r1_xboole_0(A_14,'#skF_2')
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_39,plain,(
    ! [B_24,A_25] :
      ( k7_relat_1(B_24,A_25) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [B_26] :
      ( k7_relat_1(B_26,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_26)
      | ~ r1_tarski(k1_relat_1(B_26),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_59,plain,(
    ! [B_27] :
      ( k7_relat_1(k7_relat_1(B_27,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_27,'#skF_1'))
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_65,plain,(
    ! [A_28] :
      ( k7_relat_1(k7_relat_1(A_28,'#skF_1'),'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_12,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.13  
% 1.76/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.13  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.13  
% 1.76/1.13  %Foreground sorts:
% 1.76/1.13  
% 1.76/1.13  
% 1.76/1.13  %Background operators:
% 1.76/1.13  
% 1.76/1.13  
% 1.76/1.13  %Foreground operators:
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.76/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.13  
% 1.76/1.14  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.76/1.14  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.76/1.14  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.76/1.14  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.76/1.14  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.76/1.14  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.14  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.76/1.14  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.76/1.14  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.14  tff(c_19, plain, (![A_14, C_15, B_16]: (r1_xboole_0(A_14, C_15) | ~r1_xboole_0(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.14  tff(c_22, plain, (![A_14]: (r1_xboole_0(A_14, '#skF_2') | ~r1_tarski(A_14, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.76/1.14  tff(c_39, plain, (![B_24, A_25]: (k7_relat_1(B_24, A_25)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.14  tff(c_53, plain, (![B_26]: (k7_relat_1(B_26, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_26) | ~r1_tarski(k1_relat_1(B_26), '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_39])).
% 1.76/1.14  tff(c_59, plain, (![B_27]: (k7_relat_1(k7_relat_1(B_27, '#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_27, '#skF_1')) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.76/1.14  tff(c_65, plain, (![A_28]: (k7_relat_1(k7_relat_1(A_28, '#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_4, c_59])).
% 1.76/1.14  tff(c_12, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.76/1.14  tff(c_77, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_65, c_12])).
% 1.76/1.14  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_77])).
% 1.76/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  Inference rules
% 1.76/1.14  ----------------------
% 1.76/1.14  #Ref     : 0
% 1.76/1.14  #Sup     : 16
% 1.76/1.14  #Fact    : 0
% 1.76/1.14  #Define  : 0
% 1.76/1.14  #Split   : 0
% 1.76/1.14  #Chain   : 0
% 1.76/1.14  #Close   : 0
% 1.76/1.14  
% 1.76/1.14  Ordering : KBO
% 1.76/1.14  
% 1.76/1.14  Simplification rules
% 1.76/1.14  ----------------------
% 1.76/1.14  #Subsume      : 1
% 1.76/1.14  #Demod        : 1
% 1.76/1.14  #Tautology    : 2
% 1.76/1.14  #SimpNegUnit  : 0
% 1.76/1.14  #BackRed      : 0
% 1.76/1.14  
% 1.76/1.14  #Partial instantiations: 0
% 1.76/1.14  #Strategies tried      : 1
% 1.76/1.14  
% 1.76/1.14  Timing (in seconds)
% 1.76/1.14  ----------------------
% 1.76/1.14  Preprocessing        : 0.27
% 1.76/1.14  Parsing              : 0.15
% 1.76/1.14  CNF conversion       : 0.02
% 1.76/1.14  Main loop            : 0.13
% 1.76/1.14  Inferencing          : 0.06
% 1.76/1.14  Reduction            : 0.03
% 1.76/1.14  Demodulation         : 0.02
% 1.76/1.14  BG Simplification    : 0.01
% 1.76/1.14  Subsumption          : 0.03
% 1.76/1.15  Abstraction          : 0.01
% 1.76/1.15  MUC search           : 0.00
% 1.76/1.15  Cooper               : 0.00
% 1.76/1.15  Total                : 0.42
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.15  Index Matching       : 0.00
% 1.76/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
