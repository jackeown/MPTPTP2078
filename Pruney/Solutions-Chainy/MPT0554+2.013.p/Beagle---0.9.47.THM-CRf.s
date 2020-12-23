%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_21])).

tff(c_161,plain,(
    ! [C_29,A_30,B_31] :
      ( k2_xboole_0(k9_relat_1(C_29,A_30),k9_relat_1(C_29,B_31)) = k9_relat_1(C_29,k2_xboole_0(A_30,B_31))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,C_16)
      | ~ r1_tarski(k2_xboole_0(A_15,B_17),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_15,B_17] : r1_tarski(A_15,k2_xboole_0(A_15,B_17)) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_477,plain,(
    ! [C_51,A_52,B_53] :
      ( r1_tarski(k9_relat_1(C_51,A_52),k9_relat_1(C_51,k2_xboole_0(A_52,B_53)))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_54])).

tff(c_506,plain,(
    ! [C_54] :
      ( r1_tarski(k9_relat_1(C_54,'#skF_1'),k9_relat_1(C_54,'#skF_2'))
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_477])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_511,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_506,c_14])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.64  
% 2.34/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.65  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.34/1.65  
% 2.34/1.65  %Foreground sorts:
% 2.34/1.65  
% 2.34/1.65  
% 2.34/1.65  %Background operators:
% 2.34/1.65  
% 2.34/1.65  
% 2.34/1.65  %Foreground operators:
% 2.34/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.34/1.65  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.65  
% 2.34/1.66  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.34/1.66  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.34/1.66  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 2.34/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.34/1.66  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.34/1.66  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.66  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.66  tff(c_21, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.66  tff(c_29, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_21])).
% 2.34/1.66  tff(c_161, plain, (![C_29, A_30, B_31]: (k2_xboole_0(k9_relat_1(C_29, A_30), k9_relat_1(C_29, B_31))=k9_relat_1(C_29, k2_xboole_0(A_30, B_31)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.66  tff(c_43, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, C_16) | ~r1_tarski(k2_xboole_0(A_15, B_17), C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.66  tff(c_54, plain, (![A_15, B_17]: (r1_tarski(A_15, k2_xboole_0(A_15, B_17)))), inference(resolution, [status(thm)], [c_6, c_43])).
% 2.34/1.66  tff(c_477, plain, (![C_51, A_52, B_53]: (r1_tarski(k9_relat_1(C_51, A_52), k9_relat_1(C_51, k2_xboole_0(A_52, B_53))) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_161, c_54])).
% 2.34/1.66  tff(c_506, plain, (![C_54]: (r1_tarski(k9_relat_1(C_54, '#skF_1'), k9_relat_1(C_54, '#skF_2')) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_29, c_477])).
% 2.34/1.66  tff(c_14, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.66  tff(c_511, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_506, c_14])).
% 2.34/1.66  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_511])).
% 2.34/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.66  
% 2.34/1.66  Inference rules
% 2.34/1.66  ----------------------
% 2.34/1.66  #Ref     : 0
% 2.34/1.66  #Sup     : 115
% 2.34/1.66  #Fact    : 0
% 2.34/1.66  #Define  : 0
% 2.34/1.66  #Split   : 1
% 2.34/1.66  #Chain   : 0
% 2.34/1.66  #Close   : 0
% 2.34/1.66  
% 2.34/1.66  Ordering : KBO
% 2.34/1.66  
% 2.34/1.66  Simplification rules
% 2.34/1.66  ----------------------
% 2.34/1.66  #Subsume      : 10
% 2.34/1.66  #Demod        : 61
% 2.34/1.66  #Tautology    : 59
% 2.34/1.66  #SimpNegUnit  : 0
% 2.34/1.66  #BackRed      : 0
% 2.34/1.66  
% 2.34/1.66  #Partial instantiations: 0
% 2.34/1.66  #Strategies tried      : 1
% 2.34/1.66  
% 2.34/1.66  Timing (in seconds)
% 2.34/1.66  ----------------------
% 2.65/1.67  Preprocessing        : 0.39
% 2.65/1.67  Parsing              : 0.21
% 2.65/1.67  CNF conversion       : 0.03
% 2.65/1.67  Main loop            : 0.38
% 2.65/1.67  Inferencing          : 0.14
% 2.65/1.67  Reduction            : 0.12
% 2.65/1.67  Demodulation         : 0.09
% 2.65/1.67  BG Simplification    : 0.02
% 2.65/1.67  Subsumption          : 0.08
% 2.65/1.67  Abstraction          : 0.02
% 2.65/1.67  MUC search           : 0.00
% 2.65/1.67  Cooper               : 0.00
% 2.65/1.67  Total                : 0.81
% 2.65/1.67  Index Insertion      : 0.00
% 2.65/1.67  Index Deletion       : 0.00
% 2.65/1.67  Index Matching       : 0.00
% 2.65/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
