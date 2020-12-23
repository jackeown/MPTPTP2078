%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:52 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.25s
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
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

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
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(k1_relat_1(B_19),A_20)
      | k9_relat_1(B_19,A_20) != k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [B_23,A_24] :
      ( k3_xboole_0(k1_relat_1(B_23),A_24) = k1_xboole_0
      | k9_relat_1(B_23,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_143,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,k1_relat_1(B_28)) = k1_xboole_0
      | k9_relat_1(B_28,A_27) != k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_1'
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
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
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.52  
% 2.16/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.53  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.53  
% 2.23/1.53  %Foreground sorts:
% 2.23/1.53  
% 2.23/1.53  
% 2.23/1.53  %Background operators:
% 2.23/1.53  
% 2.23/1.53  
% 2.23/1.53  %Foreground operators:
% 2.23/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.53  
% 2.25/1.54  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.25/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.25/1.54  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.25/1.54  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.25/1.54  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.25/1.54  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.54  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.54  tff(c_14, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.54  tff(c_79, plain, (![B_19, A_20]: (r1_xboole_0(k1_relat_1(B_19), A_20) | k9_relat_1(B_19, A_20)!=k1_xboole_0 | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.54  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.54  tff(c_97, plain, (![B_23, A_24]: (k3_xboole_0(k1_relat_1(B_23), A_24)=k1_xboole_0 | k9_relat_1(B_23, A_24)!=k1_xboole_0 | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_79, c_4])).
% 2.25/1.54  tff(c_143, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k1_relat_1(B_28))=k1_xboole_0 | k9_relat_1(B_28, A_27)!=k1_xboole_0 | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 2.25/1.54  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.54  tff(c_59, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.54  tff(c_63, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_16, c_59])).
% 2.25/1.54  tff(c_160, plain, (k1_xboole_0='#skF_1' | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_63])).
% 2.25/1.54  tff(c_190, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_160])).
% 2.25/1.54  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_190])).
% 2.25/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.54  
% 2.25/1.54  Inference rules
% 2.25/1.54  ----------------------
% 2.25/1.54  #Ref     : 0
% 2.25/1.54  #Sup     : 42
% 2.25/1.54  #Fact    : 0
% 2.25/1.54  #Define  : 0
% 2.25/1.54  #Split   : 0
% 2.25/1.54  #Chain   : 0
% 2.25/1.54  #Close   : 0
% 2.25/1.54  
% 2.25/1.54  Ordering : KBO
% 2.25/1.54  
% 2.25/1.54  Simplification rules
% 2.25/1.54  ----------------------
% 2.25/1.54  #Subsume      : 3
% 2.25/1.54  #Demod        : 4
% 2.25/1.54  #Tautology    : 20
% 2.25/1.54  #SimpNegUnit  : 1
% 2.25/1.54  #BackRed      : 0
% 2.25/1.54  
% 2.25/1.54  #Partial instantiations: 0
% 2.25/1.54  #Strategies tried      : 1
% 2.25/1.54  
% 2.25/1.54  Timing (in seconds)
% 2.25/1.54  ----------------------
% 2.25/1.54  Preprocessing        : 0.41
% 2.25/1.54  Parsing              : 0.21
% 2.25/1.55  CNF conversion       : 0.03
% 2.25/1.55  Main loop            : 0.22
% 2.25/1.55  Inferencing          : 0.09
% 2.25/1.55  Reduction            : 0.07
% 2.25/1.55  Demodulation         : 0.05
% 2.25/1.55  BG Simplification    : 0.02
% 2.25/1.55  Subsumption          : 0.04
% 2.25/1.55  Abstraction          : 0.01
% 2.25/1.55  MUC search           : 0.00
% 2.25/1.55  Cooper               : 0.00
% 2.25/1.55  Total                : 0.67
% 2.25/1.55  Index Insertion      : 0.00
% 2.25/1.55  Index Deletion       : 0.00
% 2.25/1.55  Index Matching       : 0.00
% 2.25/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
