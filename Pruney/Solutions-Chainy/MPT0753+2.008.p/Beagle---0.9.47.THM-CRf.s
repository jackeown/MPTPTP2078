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
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   43 (  72 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_3] :
      ( k7_relat_1(A_3,k1_relat_1(A_3)) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [B_10,A_11] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_10,A_11)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_16] :
      ( r1_tarski(k2_relat_1(A_16),k2_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v5_relat_1(B_2,A_1)
      | ~ r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_17] :
      ( v5_relat_1(A_17,k2_relat_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_16,plain,(
    v3_ordinal1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    ! [A_7] :
      ( v5_ordinal1(A_7)
      | ~ v3_ordinal1(k1_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    v5_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_18,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,
    ( ~ v5_ordinal1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,
    ( ~ v5_ordinal1('#skF_1')
    | ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14])).

tff(c_34,plain,(
    ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_22])).

tff(c_66,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_34])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.81/1.19  
% 1.81/1.19  %Foreground sorts:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Background operators:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Foreground operators:
% 1.81/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.19  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.81/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.19  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.81/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.19  
% 1.81/1.20  tff(f_58, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_ordinal1)).
% 1.81/1.20  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.81/1.20  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 1.81/1.20  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.81/1.20  tff(f_43, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_ordinal1)).
% 1.81/1.20  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.20  tff(c_6, plain, (![A_3]: (k7_relat_1(A_3, k1_relat_1(A_3))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.20  tff(c_44, plain, (![B_10, A_11]: (r1_tarski(k2_relat_1(k7_relat_1(B_10, A_11)), k2_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.20  tff(c_58, plain, (![A_16]: (r1_tarski(k2_relat_1(A_16), k2_relat_1(A_16)) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 1.81/1.20  tff(c_2, plain, (![B_2, A_1]: (v5_relat_1(B_2, A_1) | ~r1_tarski(k2_relat_1(B_2), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.20  tff(c_63, plain, (![A_17]: (v5_relat_1(A_17, k2_relat_1(A_17)) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.81/1.20  tff(c_16, plain, (v3_ordinal1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.20  tff(c_23, plain, (![A_7]: (v5_ordinal1(A_7) | ~v3_ordinal1(k1_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.20  tff(c_27, plain, (v5_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_23])).
% 1.81/1.20  tff(c_18, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.20  tff(c_14, plain, (~v5_ordinal1('#skF_1') | ~v1_funct_1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.81/1.20  tff(c_22, plain, (~v5_ordinal1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14])).
% 1.81/1.20  tff(c_34, plain, (~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_22])).
% 1.81/1.20  tff(c_66, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_63, c_34])).
% 1.81/1.20  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_66])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 9
% 1.81/1.20  #Fact    : 0
% 1.81/1.20  #Define  : 0
% 1.81/1.20  #Split   : 0
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.20  
% 1.81/1.20  Ordering : KBO
% 1.81/1.20  
% 1.81/1.20  Simplification rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Subsume      : 0
% 1.81/1.20  #Demod        : 4
% 1.81/1.20  #Tautology    : 4
% 1.81/1.20  #SimpNegUnit  : 0
% 1.81/1.20  #BackRed      : 0
% 1.81/1.20  
% 1.81/1.20  #Partial instantiations: 0
% 1.81/1.20  #Strategies tried      : 1
% 1.81/1.20  
% 1.81/1.20  Timing (in seconds)
% 1.81/1.20  ----------------------
% 1.81/1.21  Preprocessing        : 0.28
% 1.81/1.21  Parsing              : 0.16
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.10
% 1.81/1.21  Inferencing          : 0.05
% 1.81/1.21  Reduction            : 0.02
% 1.81/1.21  Demodulation         : 0.02
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.01
% 1.81/1.21  Abstraction          : 0.00
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.40
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
