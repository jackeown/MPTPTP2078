%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:29 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  72 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_1'(A_13,B_14),B_14)
      | r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_46,plain,(
    ! [B_18,A_19] :
      ( v5_relat_1(B_18,A_19)
      | ~ r1_tarski(k2_relat_1(B_18),A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [B_20] :
      ( v5_relat_1(B_20,k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_43,c_46])).

tff(c_18,plain,(
    v3_ordinal1(k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25,plain,(
    ! [A_9] :
      ( v5_ordinal1(A_9)
      | ~ v3_ordinal1(k1_relat_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_29,plain,(
    v5_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_25])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,
    ( ~ v5_ordinal1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,
    ( ~ v5_ordinal1('#skF_2')
    | ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16])).

tff(c_36,plain,(
    ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_24])).

tff(c_59,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_36])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.10  %$ v5_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.65/1.10  
% 1.65/1.10  %Foreground sorts:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Background operators:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Foreground operators:
% 1.65/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.65/1.10  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.65/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.10  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.65/1.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.10  
% 1.65/1.10  tff(f_57, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_ordinal1)).
% 1.65/1.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.65/1.10  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.65/1.10  tff(f_42, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_ordinal1)).
% 1.65/1.10  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.10  tff(c_38, plain, (![A_13, B_14]: (~r2_hidden('#skF_1'(A_13, B_14), B_14) | r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.10  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.65/1.10  tff(c_46, plain, (![B_18, A_19]: (v5_relat_1(B_18, A_19) | ~r1_tarski(k2_relat_1(B_18), A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.10  tff(c_56, plain, (![B_20]: (v5_relat_1(B_20, k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_43, c_46])).
% 1.65/1.10  tff(c_18, plain, (v3_ordinal1(k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.10  tff(c_25, plain, (![A_9]: (v5_ordinal1(A_9) | ~v3_ordinal1(k1_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.10  tff(c_29, plain, (v5_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_25])).
% 1.65/1.10  tff(c_20, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.10  tff(c_16, plain, (~v5_ordinal1('#skF_2') | ~v1_funct_1('#skF_2') | ~v5_relat_1('#skF_2', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.10  tff(c_24, plain, (~v5_ordinal1('#skF_2') | ~v5_relat_1('#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16])).
% 1.65/1.10  tff(c_36, plain, (~v5_relat_1('#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_24])).
% 1.65/1.10  tff(c_59, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_36])).
% 1.65/1.10  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_59])).
% 1.65/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  Inference rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Ref     : 0
% 1.65/1.10  #Sup     : 6
% 1.65/1.10  #Fact    : 0
% 1.65/1.10  #Define  : 0
% 1.65/1.10  #Split   : 0
% 1.65/1.10  #Chain   : 0
% 1.65/1.10  #Close   : 0
% 1.65/1.10  
% 1.65/1.10  Ordering : KBO
% 1.65/1.10  
% 1.65/1.10  Simplification rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Subsume      : 0
% 1.65/1.10  #Demod        : 4
% 1.65/1.10  #Tautology    : 2
% 1.65/1.11  #SimpNegUnit  : 0
% 1.65/1.11  #BackRed      : 0
% 1.65/1.11  
% 1.65/1.11  #Partial instantiations: 0
% 1.65/1.11  #Strategies tried      : 1
% 1.65/1.11  
% 1.65/1.11  Timing (in seconds)
% 1.65/1.11  ----------------------
% 1.65/1.11  Preprocessing        : 0.25
% 1.65/1.11  Parsing              : 0.14
% 1.65/1.11  CNF conversion       : 0.02
% 1.65/1.11  Main loop            : 0.10
% 1.65/1.11  Inferencing          : 0.05
% 1.65/1.11  Reduction            : 0.02
% 1.65/1.11  Demodulation         : 0.02
% 1.65/1.11  BG Simplification    : 0.01
% 1.65/1.11  Subsumption          : 0.01
% 1.65/1.11  Abstraction          : 0.00
% 1.65/1.11  MUC search           : 0.00
% 1.65/1.11  Cooper               : 0.00
% 1.65/1.11  Total                : 0.37
% 1.65/1.11  Index Insertion      : 0.00
% 1.65/1.11  Index Deletion       : 0.00
% 1.65/1.11  Index Matching       : 0.00
% 1.65/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
