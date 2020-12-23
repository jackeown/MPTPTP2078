%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k7_relat_1(B_7,A_6),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,A_14)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_71,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k2_relat_1(A_21),k2_relat_1(B_22))
      | ~ r1_tarski(A_21,B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

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
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:20:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.18  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.18  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.95/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.18  
% 1.95/1.19  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_ordinal1)).
% 1.95/1.19  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.95/1.19  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.95/1.19  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.95/1.19  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.95/1.19  tff(f_54, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_ordinal1)).
% 1.95/1.19  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.19  tff(c_40, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.19  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k7_relat_1(B_7, A_6), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.19  tff(c_46, plain, (![A_14]: (r1_tarski(A_14, A_14) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_40, c_10])).
% 1.95/1.19  tff(c_71, plain, (![A_21, B_22]: (r1_tarski(k2_relat_1(A_21), k2_relat_1(B_22)) | ~r1_tarski(A_21, B_22) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.95/1.19  tff(c_2, plain, (![B_2, A_1]: (v5_relat_1(B_2, A_1) | ~r1_tarski(k2_relat_1(B_2), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.19  tff(c_77, plain, (![A_25, B_26]: (v5_relat_1(A_25, k2_relat_1(B_26)) | ~r1_tarski(A_25, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_71, c_2])).
% 1.95/1.19  tff(c_20, plain, (v3_ordinal1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.19  tff(c_27, plain, (![A_10]: (v5_ordinal1(A_10) | ~v3_ordinal1(k1_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.19  tff(c_31, plain, (v5_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_27])).
% 1.95/1.19  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.19  tff(c_18, plain, (~v5_ordinal1('#skF_1') | ~v1_funct_1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.19  tff(c_26, plain, (~v5_ordinal1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18])).
% 1.95/1.19  tff(c_38, plain, (~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_26])).
% 1.95/1.19  tff(c_80, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_77, c_38])).
% 1.95/1.19  tff(c_83, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_80])).
% 1.95/1.19  tff(c_86, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_46, c_83])).
% 1.95/1.19  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_86])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 11
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 0
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 0
% 1.95/1.19  #Demod        : 6
% 1.95/1.19  #Tautology    : 4
% 1.95/1.19  #SimpNegUnit  : 0
% 1.95/1.19  #BackRed      : 0
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.20  ----------------------
% 1.95/1.20  Preprocessing        : 0.26
% 1.95/1.20  Parsing              : 0.14
% 1.95/1.20  CNF conversion       : 0.02
% 1.95/1.20  Main loop            : 0.12
% 1.95/1.20  Inferencing          : 0.06
% 1.95/1.20  Reduction            : 0.03
% 1.95/1.20  Demodulation         : 0.02
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.02
% 1.95/1.20  Abstraction          : 0.00
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.41
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
