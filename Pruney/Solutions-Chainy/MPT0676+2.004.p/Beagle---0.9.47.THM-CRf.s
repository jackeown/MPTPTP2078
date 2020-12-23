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
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  86 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(k8_relat_1(A,C),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k8_relat_1(A_3,B_4),B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k8_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [C_23,A_24,D_25,B_26] :
      ( r1_tarski(k9_relat_1(C_23,A_24),k9_relat_1(D_25,B_26))
      | ~ r1_tarski(A_24,B_26)
      | ~ r1_tarski(C_23,D_25)
      | ~ v1_relat_1(D_25)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_37,c_16])).

tff(c_45,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_40])).

tff(c_47,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_50,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_50])).

tff(c_55,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_59,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_55])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  
% 1.64/1.12  tff(f_61, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(k8_relat_1(A, C), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_funct_1)).
% 1.64/1.12  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.64/1.12  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 1.64/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.64/1.12  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 1.64/1.12  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.64/1.12  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k8_relat_1(A_3, B_4), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.12  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.64/1.12  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k8_relat_1(A_10, B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.12  tff(c_37, plain, (![C_23, A_24, D_25, B_26]: (r1_tarski(k9_relat_1(C_23, A_24), k9_relat_1(D_25, B_26)) | ~r1_tarski(A_24, B_26) | ~r1_tarski(C_23, D_25) | ~v1_relat_1(D_25) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.12  tff(c_16, plain, (~r1_tarski(k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.64/1.12  tff(c_40, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_37, c_16])).
% 1.64/1.12  tff(c_45, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_40])).
% 1.64/1.12  tff(c_47, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_45])).
% 1.64/1.12  tff(c_50, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_47])).
% 1.64/1.12  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_50])).
% 1.64/1.12  tff(c_55, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_45])).
% 1.64/1.12  tff(c_59, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_55])).
% 1.64/1.12  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 6
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 1
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Subsume      : 0
% 1.64/1.12  #Demod        : 7
% 1.64/1.12  #Tautology    : 2
% 1.64/1.12  #SimpNegUnit  : 0
% 1.64/1.12  #BackRed      : 0
% 1.64/1.12  
% 1.64/1.12  #Partial instantiations: 0
% 1.64/1.12  #Strategies tried      : 1
% 1.64/1.12  
% 1.64/1.12  Timing (in seconds)
% 1.64/1.12  ----------------------
% 1.64/1.12  Preprocessing        : 0.26
% 1.64/1.12  Parsing              : 0.15
% 1.64/1.12  CNF conversion       : 0.02
% 1.64/1.12  Main loop            : 0.10
% 1.64/1.12  Inferencing          : 0.04
% 1.64/1.12  Reduction            : 0.02
% 1.64/1.12  Demodulation         : 0.02
% 1.64/1.12  BG Simplification    : 0.01
% 1.64/1.12  Subsumption          : 0.02
% 1.64/1.12  Abstraction          : 0.00
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.38
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
