%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [C_33,A_34,B_35] :
      ( k2_xboole_0(k10_relat_1(C_33,A_34),k10_relat_1(C_33,B_35)) = k10_relat_1(C_33,k2_xboole_0(A_34,B_35))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_276,plain,(
    ! [C_50,A_51,C_52,B_53] :
      ( r1_tarski(k10_relat_1(C_50,A_51),C_52)
      | ~ r1_tarski(k10_relat_1(C_50,k2_xboole_0(A_51,B_53)),C_52)
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_8])).

tff(c_417,plain,(
    ! [C_68,A_69,B_70] :
      ( r1_tarski(k10_relat_1(C_68,A_69),k10_relat_1(C_68,k2_xboole_0(A_69,B_70)))
      | ~ v1_relat_1(C_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_1299,plain,(
    ! [C_135,A_136,B_137] :
      ( r1_tarski(k10_relat_1(C_135,A_136),k10_relat_1(C_135,B_137))
      | ~ v1_relat_1(C_135)
      | ~ r1_tarski(A_136,B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_417])).

tff(c_14,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1322,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1299,c_14])).

tff(c_1334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_1322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.65  
% 2.95/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.65  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.95/1.65  
% 2.95/1.65  %Foreground sorts:
% 2.95/1.65  
% 2.95/1.65  
% 2.95/1.65  %Background operators:
% 2.95/1.65  
% 2.95/1.65  
% 2.95/1.65  %Foreground operators:
% 2.95/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.65  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.65  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.95/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.65  
% 2.95/1.66  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.95/1.66  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.95/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.95/1.66  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.95/1.66  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.95/1.66  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.66  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.66  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.66  tff(c_122, plain, (![C_33, A_34, B_35]: (k2_xboole_0(k10_relat_1(C_33, A_34), k10_relat_1(C_33, B_35))=k10_relat_1(C_33, k2_xboole_0(A_34, B_35)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.66  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.66  tff(c_276, plain, (![C_50, A_51, C_52, B_53]: (r1_tarski(k10_relat_1(C_50, A_51), C_52) | ~r1_tarski(k10_relat_1(C_50, k2_xboole_0(A_51, B_53)), C_52) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_122, c_8])).
% 2.95/1.66  tff(c_417, plain, (![C_68, A_69, B_70]: (r1_tarski(k10_relat_1(C_68, A_69), k10_relat_1(C_68, k2_xboole_0(A_69, B_70))) | ~v1_relat_1(C_68))), inference(resolution, [status(thm)], [c_6, c_276])).
% 2.95/1.66  tff(c_1299, plain, (![C_135, A_136, B_137]: (r1_tarski(k10_relat_1(C_135, A_136), k10_relat_1(C_135, B_137)) | ~v1_relat_1(C_135) | ~r1_tarski(A_136, B_137))), inference(superposition, [status(thm), theory('equality')], [c_10, c_417])).
% 2.95/1.66  tff(c_14, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.66  tff(c_1322, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1299, c_14])).
% 2.95/1.66  tff(c_1334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_1322])).
% 2.95/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.66  
% 2.95/1.66  Inference rules
% 2.95/1.66  ----------------------
% 2.95/1.66  #Ref     : 0
% 2.95/1.66  #Sup     : 324
% 2.95/1.66  #Fact    : 0
% 2.95/1.66  #Define  : 0
% 2.95/1.66  #Split   : 1
% 2.95/1.66  #Chain   : 0
% 2.95/1.66  #Close   : 0
% 2.95/1.66  
% 2.95/1.66  Ordering : KBO
% 2.95/1.66  
% 2.95/1.66  Simplification rules
% 2.95/1.66  ----------------------
% 2.95/1.66  #Subsume      : 53
% 2.95/1.66  #Demod        : 34
% 2.95/1.66  #Tautology    : 34
% 2.95/1.66  #SimpNegUnit  : 0
% 2.95/1.66  #BackRed      : 0
% 2.95/1.66  
% 2.95/1.66  #Partial instantiations: 0
% 2.95/1.66  #Strategies tried      : 1
% 2.95/1.66  
% 2.95/1.66  Timing (in seconds)
% 2.95/1.66  ----------------------
% 2.95/1.67  Preprocessing        : 0.27
% 2.95/1.67  Parsing              : 0.13
% 2.95/1.67  CNF conversion       : 0.02
% 2.95/1.67  Main loop            : 0.46
% 2.95/1.67  Inferencing          : 0.16
% 2.95/1.67  Reduction            : 0.12
% 2.95/1.67  Demodulation         : 0.08
% 2.95/1.67  BG Simplification    : 0.02
% 2.95/1.67  Subsumption          : 0.13
% 2.95/1.67  Abstraction          : 0.02
% 2.95/1.67  MUC search           : 0.00
% 2.95/1.67  Cooper               : 0.00
% 2.95/1.67  Total                : 0.75
% 2.95/1.67  Index Insertion      : 0.00
% 2.95/1.67  Index Deletion       : 0.00
% 2.95/1.67  Index Matching       : 0.00
% 2.95/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
