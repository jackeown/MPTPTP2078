%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:57 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  57 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,k10_relat_1(B_14,A_13)),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [C_12,A_10,B_11] :
      ( r1_tarski(k9_relat_1(C_12,k3_xboole_0(A_10,B_11)),k3_xboole_0(k9_relat_1(C_12,A_10),k9_relat_1(C_12,B_11)))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_23,C_24,B_25,D_26] :
      ( r1_tarski(k3_xboole_0(A_23,C_24),k3_xboole_0(B_25,D_26))
      | ~ r1_tarski(C_24,D_26)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [B_33,A_36,C_34,A_37,D_35] :
      ( r1_tarski(A_36,k3_xboole_0(B_33,D_35))
      | ~ r1_tarski(A_36,k3_xboole_0(A_37,C_34))
      | ~ r1_tarski(C_34,D_35)
      | ~ r1_tarski(A_37,B_33) ) ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_208,plain,(
    ! [D_74,B_73,C_76,B_72,A_75] :
      ( r1_tarski(k9_relat_1(C_76,k3_xboole_0(A_75,B_73)),k3_xboole_0(B_72,D_74))
      | ~ r1_tarski(k9_relat_1(C_76,B_73),D_74)
      | ~ r1_tarski(k9_relat_1(C_76,A_75),B_72)
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_221,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')),'#skF_2')
    | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_16])).

tff(c_233,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_221])).

tff(c_238,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_233])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.23/1.35  
% 2.23/1.35  %Foreground sorts:
% 2.23/1.35  
% 2.23/1.35  
% 2.23/1.35  %Background operators:
% 2.23/1.35  
% 2.23/1.35  
% 2.23/1.35  %Foreground operators:
% 2.23/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.23/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.35  
% 2.23/1.35  tff(f_60, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 2.23/1.35  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 2.23/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.35  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 2.23/1.35  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 2.23/1.35  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.23/1.35  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.35  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.35  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, k10_relat_1(B_14, A_13)), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.35  tff(c_12, plain, (![C_12, A_10, B_11]: (r1_tarski(k9_relat_1(C_12, k3_xboole_0(A_10, B_11)), k3_xboole_0(k9_relat_1(C_12, A_10), k9_relat_1(C_12, B_11))) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.35  tff(c_41, plain, (![A_23, C_24, B_25, D_26]: (r1_tarski(k3_xboole_0(A_23, C_24), k3_xboole_0(B_25, D_26)) | ~r1_tarski(C_24, D_26) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.35  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.35  tff(c_66, plain, (![B_33, A_36, C_34, A_37, D_35]: (r1_tarski(A_36, k3_xboole_0(B_33, D_35)) | ~r1_tarski(A_36, k3_xboole_0(A_37, C_34)) | ~r1_tarski(C_34, D_35) | ~r1_tarski(A_37, B_33))), inference(resolution, [status(thm)], [c_41, c_8])).
% 2.23/1.35  tff(c_208, plain, (![D_74, B_73, C_76, B_72, A_75]: (r1_tarski(k9_relat_1(C_76, k3_xboole_0(A_75, B_73)), k3_xboole_0(B_72, D_74)) | ~r1_tarski(k9_relat_1(C_76, B_73), D_74) | ~r1_tarski(k9_relat_1(C_76, A_75), B_72) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_12, c_66])).
% 2.23/1.35  tff(c_16, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.35  tff(c_221, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')), '#skF_2') | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_208, c_16])).
% 2.23/1.35  tff(c_233, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_221])).
% 2.23/1.35  tff(c_238, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_233])).
% 2.23/1.35  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_238])).
% 2.23/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  Inference rules
% 2.23/1.35  ----------------------
% 2.23/1.35  #Ref     : 0
% 2.23/1.35  #Sup     : 57
% 2.23/1.35  #Fact    : 0
% 2.23/1.36  #Define  : 0
% 2.23/1.36  #Split   : 0
% 2.23/1.36  #Chain   : 0
% 2.23/1.36  #Close   : 0
% 2.23/1.36  
% 2.23/1.36  Ordering : KBO
% 2.23/1.36  
% 2.23/1.36  Simplification rules
% 2.23/1.36  ----------------------
% 2.23/1.36  #Subsume      : 3
% 2.23/1.36  #Demod        : 10
% 2.23/1.36  #Tautology    : 5
% 2.23/1.36  #SimpNegUnit  : 0
% 2.23/1.36  #BackRed      : 0
% 2.23/1.36  
% 2.23/1.36  #Partial instantiations: 0
% 2.23/1.36  #Strategies tried      : 1
% 2.23/1.36  
% 2.23/1.36  Timing (in seconds)
% 2.23/1.36  ----------------------
% 2.23/1.36  Preprocessing        : 0.31
% 2.23/1.36  Parsing              : 0.17
% 2.23/1.36  CNF conversion       : 0.02
% 2.23/1.36  Main loop            : 0.24
% 2.23/1.36  Inferencing          : 0.08
% 2.23/1.36  Reduction            : 0.06
% 2.23/1.36  Demodulation         : 0.04
% 2.23/1.36  BG Simplification    : 0.01
% 2.23/1.36  Subsumption          : 0.07
% 2.23/1.36  Abstraction          : 0.02
% 2.23/1.36  MUC search           : 0.00
% 2.23/1.36  Cooper               : 0.00
% 2.23/1.36  Total                : 0.58
% 2.23/1.36  Index Insertion      : 0.00
% 2.23/1.36  Index Deletion       : 0.00
% 2.23/1.36  Index Matching       : 0.00
% 2.23/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
