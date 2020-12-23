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
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  94 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_5] :
      ( k8_relat_1(k2_relat_1(A_5),A_5) = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k8_relat_1(A_13,B_14),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,A_5)
      | ~ v1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_48])).

tff(c_71,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k2_relat_1(A_21),k2_relat_1(B_22))
      | ~ r1_tarski(A_21,B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v5_relat_1(B_2,A_1)
      | ~ r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_25,B_26] :
      ( v5_relat_1(A_25,k2_relat_1(B_26))
      | ~ r1_tarski(A_25,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_20,plain,(
    v3_ordinal1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_27,plain,(
    ! [A_10] :
      ( v5_ordinal1(A_10)
      | ~ v3_ordinal1(k1_relat_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31,plain,(
    v5_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_27])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,
    ( ~ v5_ordinal1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,
    ( ~ v5_ordinal1('#skF_1')
    | ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18])).

tff(c_38,plain,(
    ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_26])).

tff(c_80,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_77,c_38])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_80])).

tff(c_86,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_83])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:34:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.14  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.80/1.14  
% 1.80/1.14  %Foreground sorts:
% 1.80/1.14  
% 1.80/1.14  
% 1.80/1.14  %Background operators:
% 1.80/1.14  
% 1.80/1.14  
% 1.80/1.14  %Foreground operators:
% 1.80/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.80/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.14  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.80/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.14  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.80/1.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.80/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.14  
% 1.80/1.15  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_ordinal1)).
% 1.80/1.15  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 1.80/1.15  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.80/1.15  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.80/1.15  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.80/1.15  tff(f_54, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_ordinal1)).
% 1.80/1.15  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.80/1.15  tff(c_8, plain, (![A_5]: (k8_relat_1(k2_relat_1(A_5), A_5)=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.15  tff(c_48, plain, (![A_13, B_14]: (r1_tarski(k8_relat_1(A_13, B_14), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.15  tff(c_51, plain, (![A_5]: (r1_tarski(A_5, A_5) | ~v1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_48])).
% 1.80/1.15  tff(c_71, plain, (![A_21, B_22]: (r1_tarski(k2_relat_1(A_21), k2_relat_1(B_22)) | ~r1_tarski(A_21, B_22) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.80/1.15  tff(c_2, plain, (![B_2, A_1]: (v5_relat_1(B_2, A_1) | ~r1_tarski(k2_relat_1(B_2), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.15  tff(c_77, plain, (![A_25, B_26]: (v5_relat_1(A_25, k2_relat_1(B_26)) | ~r1_tarski(A_25, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_71, c_2])).
% 1.80/1.15  tff(c_20, plain, (v3_ordinal1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.80/1.15  tff(c_27, plain, (![A_10]: (v5_ordinal1(A_10) | ~v3_ordinal1(k1_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.15  tff(c_31, plain, (v5_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_27])).
% 1.80/1.15  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.80/1.15  tff(c_18, plain, (~v5_ordinal1('#skF_1') | ~v1_funct_1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.80/1.15  tff(c_26, plain, (~v5_ordinal1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18])).
% 1.80/1.15  tff(c_38, plain, (~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_26])).
% 1.80/1.15  tff(c_80, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_77, c_38])).
% 1.80/1.15  tff(c_83, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_80])).
% 1.80/1.15  tff(c_86, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_51, c_83])).
% 1.80/1.15  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_86])).
% 1.80/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.15  
% 1.80/1.15  Inference rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Ref     : 0
% 1.80/1.15  #Sup     : 11
% 1.80/1.15  #Fact    : 0
% 1.80/1.15  #Define  : 0
% 1.80/1.15  #Split   : 0
% 1.80/1.15  #Chain   : 0
% 1.80/1.15  #Close   : 0
% 1.80/1.15  
% 1.80/1.15  Ordering : KBO
% 1.80/1.15  
% 1.80/1.15  Simplification rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Subsume      : 0
% 1.80/1.15  #Demod        : 6
% 1.80/1.15  #Tautology    : 4
% 1.80/1.15  #SimpNegUnit  : 0
% 1.80/1.15  #BackRed      : 0
% 1.80/1.15  
% 1.80/1.15  #Partial instantiations: 0
% 1.80/1.15  #Strategies tried      : 1
% 1.80/1.15  
% 1.80/1.15  Timing (in seconds)
% 1.80/1.15  ----------------------
% 1.80/1.16  Preprocessing        : 0.27
% 1.80/1.16  Parsing              : 0.15
% 1.80/1.16  CNF conversion       : 0.02
% 1.80/1.16  Main loop            : 0.12
% 1.80/1.16  Inferencing          : 0.06
% 1.80/1.16  Reduction            : 0.03
% 1.80/1.16  Demodulation         : 0.02
% 1.80/1.16  BG Simplification    : 0.01
% 1.80/1.16  Subsumption          : 0.02
% 1.80/1.16  Abstraction          : 0.00
% 1.80/1.16  MUC search           : 0.00
% 1.80/1.16  Cooper               : 0.00
% 1.80/1.16  Total                : 0.43
% 1.80/1.16  Index Insertion      : 0.00
% 1.80/1.16  Index Deletion       : 0.00
% 1.80/1.16  Index Matching       : 0.00
% 1.80/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
