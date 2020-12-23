%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:08 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 104 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k10_relat_1(B_8,k9_relat_1(B_8,A_7)))
      | ~ r1_tarski(A_7,k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [C_18,A_19,B_20] :
      ( r1_tarski(k10_relat_1(C_18,A_19),k10_relat_1(C_18,B_20))
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_25,C_26,B_27,A_28] :
      ( r1_tarski(A_25,k10_relat_1(C_26,B_27))
      | ~ r1_tarski(A_25,k10_relat_1(C_26,A_28))
      | ~ r1_tarski(A_28,B_27)
      | ~ v1_relat_1(C_26) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_333,plain,(
    ! [A_56,B_57,B_58] :
      ( r1_tarski(A_56,k10_relat_1(B_57,B_58))
      | ~ r1_tarski(k9_relat_1(B_57,A_56),B_58)
      | ~ r1_tarski(A_56,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_352,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')))
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_333])).

tff(c_359,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_352])).

tff(c_58,plain,(
    ! [B_21,A_22] :
      ( r1_tarski(k10_relat_1(B_21,k9_relat_1(B_21,A_22)),A_22)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [A_1,A_22,B_21] :
      ( r1_tarski(A_1,A_22)
      | ~ r1_tarski(A_1,k10_relat_1(B_21,k9_relat_1(B_21,A_22)))
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_364,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_359,c_64])).

tff(c_380,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_12,c_364])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.31  
% 2.47/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.31  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.31  
% 2.47/1.31  %Foreground sorts:
% 2.47/1.31  
% 2.47/1.31  
% 2.47/1.31  %Background operators:
% 2.47/1.31  
% 2.47/1.31  
% 2.47/1.31  %Foreground operators:
% 2.47/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.47/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.47/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.47/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.31  
% 2.47/1.32  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 2.47/1.32  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.47/1.32  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.47/1.32  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.47/1.32  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 2.47/1.32  tff(c_10, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.32  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.32  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.32  tff(c_12, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.32  tff(c_14, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.32  tff(c_16, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.32  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k10_relat_1(B_8, k9_relat_1(B_8, A_7))) | ~r1_tarski(A_7, k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.32  tff(c_51, plain, (![C_18, A_19, B_20]: (r1_tarski(k10_relat_1(C_18, A_19), k10_relat_1(C_18, B_20)) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.32  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.32  tff(c_72, plain, (![A_25, C_26, B_27, A_28]: (r1_tarski(A_25, k10_relat_1(C_26, B_27)) | ~r1_tarski(A_25, k10_relat_1(C_26, A_28)) | ~r1_tarski(A_28, B_27) | ~v1_relat_1(C_26))), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.47/1.32  tff(c_333, plain, (![A_56, B_57, B_58]: (r1_tarski(A_56, k10_relat_1(B_57, B_58)) | ~r1_tarski(k9_relat_1(B_57, A_56), B_58) | ~r1_tarski(A_56, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_6, c_72])).
% 2.47/1.32  tff(c_352, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_333])).
% 2.47/1.32  tff(c_359, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_352])).
% 2.47/1.32  tff(c_58, plain, (![B_21, A_22]: (r1_tarski(k10_relat_1(B_21, k9_relat_1(B_21, A_22)), A_22) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.32  tff(c_64, plain, (![A_1, A_22, B_21]: (r1_tarski(A_1, A_22) | ~r1_tarski(A_1, k10_relat_1(B_21, k9_relat_1(B_21, A_22))) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_58, c_2])).
% 2.47/1.32  tff(c_364, plain, (r1_tarski('#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_359, c_64])).
% 2.47/1.32  tff(c_380, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_12, c_364])).
% 2.47/1.32  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_380])).
% 2.47/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.32  
% 2.47/1.32  Inference rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Ref     : 0
% 2.47/1.32  #Sup     : 93
% 2.47/1.32  #Fact    : 0
% 2.47/1.32  #Define  : 0
% 2.47/1.32  #Split   : 3
% 2.47/1.32  #Chain   : 0
% 2.47/1.32  #Close   : 0
% 2.47/1.32  
% 2.47/1.32  Ordering : KBO
% 2.47/1.32  
% 2.47/1.32  Simplification rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Subsume      : 8
% 2.47/1.32  #Demod        : 24
% 2.47/1.32  #Tautology    : 6
% 2.47/1.32  #SimpNegUnit  : 2
% 2.47/1.32  #BackRed      : 0
% 2.47/1.32  
% 2.47/1.32  #Partial instantiations: 0
% 2.47/1.32  #Strategies tried      : 1
% 2.47/1.32  
% 2.47/1.32  Timing (in seconds)
% 2.47/1.32  ----------------------
% 2.47/1.32  Preprocessing        : 0.26
% 2.47/1.32  Parsing              : 0.15
% 2.47/1.32  CNF conversion       : 0.02
% 2.47/1.32  Main loop            : 0.30
% 2.47/1.32  Inferencing          : 0.11
% 2.47/1.32  Reduction            : 0.08
% 2.47/1.32  Demodulation         : 0.05
% 2.47/1.32  BG Simplification    : 0.01
% 2.47/1.32  Subsumption          : 0.08
% 2.47/1.33  Abstraction          : 0.01
% 2.47/1.33  MUC search           : 0.00
% 2.47/1.33  Cooper               : 0.00
% 2.47/1.33  Total                : 0.59
% 2.47/1.33  Index Insertion      : 0.00
% 2.47/1.33  Index Deletion       : 0.00
% 2.47/1.33  Index Matching       : 0.00
% 2.47/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
