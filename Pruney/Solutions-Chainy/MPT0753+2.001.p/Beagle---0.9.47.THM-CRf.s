%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:29 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  65 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_13,A_14] :
      ( v5_relat_1(B_13,A_14)
      | ~ r1_tarski(k2_relat_1(B_13),A_14)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [B_15] :
      ( v5_relat_1(B_15,k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_18,plain,(
    v3_ordinal1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27,plain,(
    ! [A_7] :
      ( v5_ordinal1(A_7)
      | ~ v3_ordinal1(k1_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31,plain,(
    v5_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_27])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,
    ( ~ v5_ordinal1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,
    ( ~ v5_ordinal1('#skF_1')
    | ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16])).

tff(c_38,plain,(
    ~ v5_relat_1('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_24])).

tff(c_63,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_38])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:18:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.62/1.12  
% 1.62/1.12  %Foreground sorts:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Background operators:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Foreground operators:
% 1.62/1.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.12  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.62/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.12  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.62/1.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.12  
% 1.62/1.13  tff(f_56, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_ordinal1)).
% 1.62/1.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.62/1.13  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.62/1.13  tff(f_41, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_ordinal1)).
% 1.62/1.13  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.62/1.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.13  tff(c_50, plain, (![B_13, A_14]: (v5_relat_1(B_13, A_14) | ~r1_tarski(k2_relat_1(B_13), A_14) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.13  tff(c_60, plain, (![B_15]: (v5_relat_1(B_15, k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(resolution, [status(thm)], [c_6, c_50])).
% 1.62/1.13  tff(c_18, plain, (v3_ordinal1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.62/1.13  tff(c_27, plain, (![A_7]: (v5_ordinal1(A_7) | ~v3_ordinal1(k1_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.13  tff(c_31, plain, (v5_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_27])).
% 1.62/1.13  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.62/1.13  tff(c_16, plain, (~v5_ordinal1('#skF_1') | ~v1_funct_1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.62/1.13  tff(c_24, plain, (~v5_ordinal1('#skF_1') | ~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16])).
% 1.62/1.13  tff(c_38, plain, (~v5_relat_1('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_24])).
% 1.62/1.13  tff(c_63, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_60, c_38])).
% 1.62/1.13  tff(c_67, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_63])).
% 1.62/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  Inference rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Ref     : 0
% 1.62/1.13  #Sup     : 7
% 1.62/1.13  #Fact    : 0
% 1.62/1.13  #Define  : 0
% 1.62/1.13  #Split   : 0
% 1.62/1.13  #Chain   : 0
% 1.62/1.13  #Close   : 0
% 1.62/1.13  
% 1.62/1.13  Ordering : KBO
% 1.62/1.13  
% 1.62/1.13  Simplification rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Subsume      : 0
% 1.62/1.13  #Demod        : 6
% 1.62/1.13  #Tautology    : 4
% 1.62/1.13  #SimpNegUnit  : 0
% 1.62/1.13  #BackRed      : 0
% 1.62/1.13  
% 1.62/1.13  #Partial instantiations: 0
% 1.62/1.13  #Strategies tried      : 1
% 1.62/1.13  
% 1.62/1.13  Timing (in seconds)
% 1.62/1.13  ----------------------
% 1.62/1.14  Preprocessing        : 0.26
% 1.62/1.14  Parsing              : 0.15
% 1.62/1.14  CNF conversion       : 0.02
% 1.62/1.14  Main loop            : 0.09
% 1.62/1.14  Inferencing          : 0.04
% 1.62/1.14  Reduction            : 0.02
% 1.62/1.14  Demodulation         : 0.02
% 1.62/1.14  BG Simplification    : 0.01
% 1.62/1.14  Subsumption          : 0.02
% 1.62/1.14  Abstraction          : 0.00
% 1.62/1.14  MUC search           : 0.00
% 1.62/1.14  Cooper               : 0.00
% 1.62/1.14  Total                : 0.37
% 1.62/1.14  Index Insertion      : 0.00
% 1.62/1.14  Index Deletion       : 0.00
% 1.62/1.14  Index Matching       : 0.00
% 1.62/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
