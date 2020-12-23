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
% DateTime   : Thu Dec  3 10:00:33 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.74s
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
%$ r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k9_relat_1(B_2,A_1),k2_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_26,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_29,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_33,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:39:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.21  
% 1.67/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.23  %$ r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.72/1.23  
% 1.72/1.23  %Foreground sorts:
% 1.72/1.23  
% 1.72/1.23  
% 1.72/1.23  %Background operators:
% 1.72/1.23  
% 1.72/1.23  
% 1.72/1.23  %Foreground operators:
% 1.72/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.72/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.23  
% 1.74/1.23  tff(f_38, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 1.74/1.23  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 1.74/1.23  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 1.74/1.23  tff(c_8, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.74/1.23  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k9_relat_1(B_2, A_1), k2_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.23  tff(c_4, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.23  tff(c_6, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.74/1.23  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_6])).
% 1.74/1.23  tff(c_26, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 1.74/1.23  tff(c_29, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.74/1.23  tff(c_33, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_29])).
% 1.74/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.23  
% 1.74/1.23  Inference rules
% 1.74/1.23  ----------------------
% 1.74/1.23  #Ref     : 0
% 1.74/1.23  #Sup     : 5
% 1.74/1.23  #Fact    : 0
% 1.74/1.23  #Define  : 0
% 1.74/1.23  #Split   : 0
% 1.74/1.23  #Chain   : 0
% 1.74/1.23  #Close   : 0
% 1.74/1.23  
% 1.74/1.23  Ordering : KBO
% 1.74/1.23  
% 1.74/1.23  Simplification rules
% 1.74/1.23  ----------------------
% 1.74/1.23  #Subsume      : 0
% 1.74/1.23  #Demod        : 2
% 1.74/1.23  #Tautology    : 2
% 1.74/1.23  #SimpNegUnit  : 0
% 1.74/1.23  #BackRed      : 0
% 1.74/1.23  
% 1.74/1.23  #Partial instantiations: 0
% 1.74/1.23  #Strategies tried      : 1
% 1.74/1.23  
% 1.74/1.23  Timing (in seconds)
% 1.74/1.23  ----------------------
% 1.74/1.24  Preprocessing        : 0.30
% 1.74/1.24  Parsing              : 0.17
% 1.74/1.24  CNF conversion       : 0.02
% 1.74/1.24  Main loop            : 0.07
% 1.74/1.24  Inferencing          : 0.03
% 1.74/1.24  Reduction            : 0.02
% 1.74/1.24  Demodulation         : 0.02
% 1.74/1.24  BG Simplification    : 0.01
% 1.74/1.24  Subsumption          : 0.01
% 1.74/1.24  Abstraction          : 0.00
% 1.74/1.24  MUC search           : 0.00
% 1.74/1.24  Cooper               : 0.00
% 1.74/1.24  Total                : 0.40
% 1.74/1.24  Index Insertion      : 0.00
% 1.74/1.24  Index Deletion       : 0.00
% 1.74/1.24  Index Matching       : 0.00
% 1.74/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
