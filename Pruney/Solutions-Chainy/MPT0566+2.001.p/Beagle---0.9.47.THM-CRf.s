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
% DateTime   : Thu Dec  3 10:01:14 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  22 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k10_relat_1(B_2,A_1),k1_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2','#skF_1'),k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_2','#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_26,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2','#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_29,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_33,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  %$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.60/1.09  
% 1.60/1.09  %Foreground sorts:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Background operators:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Foreground operators:
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.60/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.09  
% 1.60/1.09  tff(f_38, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 1.60/1.09  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.60/1.09  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.60/1.09  tff(c_8, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.09  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k10_relat_1(B_2, A_1), k1_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.09  tff(c_4, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.09  tff(c_6, plain, (~r1_tarski(k10_relat_1('#skF_2', '#skF_1'), k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.09  tff(c_24, plain, (~r1_tarski(k10_relat_1('#skF_2', '#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_6])).
% 1.60/1.09  tff(c_26, plain, (~r1_tarski(k10_relat_1('#skF_2', '#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 1.60/1.09  tff(c_29, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.60/1.09  tff(c_33, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_29])).
% 1.60/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  Inference rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Ref     : 0
% 1.60/1.09  #Sup     : 5
% 1.60/1.09  #Fact    : 0
% 1.60/1.09  #Define  : 0
% 1.60/1.09  #Split   : 0
% 1.60/1.09  #Chain   : 0
% 1.60/1.09  #Close   : 0
% 1.60/1.09  
% 1.60/1.09  Ordering : KBO
% 1.60/1.09  
% 1.60/1.09  Simplification rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Subsume      : 0
% 1.60/1.09  #Demod        : 2
% 1.60/1.09  #Tautology    : 2
% 1.60/1.09  #SimpNegUnit  : 0
% 1.60/1.09  #BackRed      : 0
% 1.60/1.09  
% 1.60/1.09  #Partial instantiations: 0
% 1.60/1.09  #Strategies tried      : 1
% 1.60/1.09  
% 1.60/1.09  Timing (in seconds)
% 1.60/1.09  ----------------------
% 1.60/1.10  Preprocessing        : 0.25
% 1.60/1.10  Parsing              : 0.14
% 1.60/1.10  CNF conversion       : 0.01
% 1.60/1.10  Main loop            : 0.06
% 1.60/1.10  Inferencing          : 0.03
% 1.60/1.10  Reduction            : 0.02
% 1.60/1.10  Demodulation         : 0.01
% 1.60/1.10  BG Simplification    : 0.01
% 1.60/1.10  Subsumption          : 0.00
% 1.60/1.10  Abstraction          : 0.00
% 1.60/1.10  MUC search           : 0.00
% 1.60/1.10  Cooper               : 0.00
% 1.60/1.10  Total                : 0.34
% 1.60/1.10  Index Insertion      : 0.00
% 1.60/1.10  Index Deletion       : 0.00
% 1.60/1.10  Index Matching       : 0.00
% 1.60/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
