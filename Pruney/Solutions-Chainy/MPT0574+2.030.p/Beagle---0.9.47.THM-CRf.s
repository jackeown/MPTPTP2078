%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [C_12,A_13,B_14] :
      ( k2_xboole_0(k10_relat_1(C_12,A_13),k10_relat_1(C_12,B_14)) = k10_relat_1(C_12,k2_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [C_15,A_16,B_17] :
      ( r1_tarski(k10_relat_1(C_15,A_16),k10_relat_1(C_15,k2_xboole_0(A_16,B_17)))
      | ~ v1_relat_1(C_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_45,plain,(
    ! [C_18,A_19,B_20] :
      ( r1_tarski(k10_relat_1(C_18,A_19),k10_relat_1(C_18,B_20))
      | ~ v1_relat_1(C_18)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_8,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_8])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.50  
% 1.89/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.52  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.96/1.52  
% 1.96/1.52  %Foreground sorts:
% 1.96/1.52  
% 1.96/1.52  
% 1.96/1.52  %Background operators:
% 1.96/1.52  
% 1.96/1.52  
% 1.96/1.52  %Foreground operators:
% 1.96/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.52  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.52  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.52  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.96/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.52  
% 1.96/1.53  tff(f_42, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 1.96/1.53  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.96/1.53  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 1.96/1.53  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.96/1.53  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.53  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.53  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.53  tff(c_26, plain, (![C_12, A_13, B_14]: (k2_xboole_0(k10_relat_1(C_12, A_13), k10_relat_1(C_12, B_14))=k10_relat_1(C_12, k2_xboole_0(A_13, B_14)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.53  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.53  tff(c_38, plain, (![C_15, A_16, B_17]: (r1_tarski(k10_relat_1(C_15, A_16), k10_relat_1(C_15, k2_xboole_0(A_16, B_17))) | ~v1_relat_1(C_15))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 1.96/1.53  tff(c_45, plain, (![C_18, A_19, B_20]: (r1_tarski(k10_relat_1(C_18, A_19), k10_relat_1(C_18, B_20)) | ~v1_relat_1(C_18) | ~r1_tarski(A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_2, c_38])).
% 1.96/1.53  tff(c_8, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.53  tff(c_48, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_45, c_8])).
% 1.96/1.53  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_48])).
% 1.96/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.53  
% 1.96/1.53  Inference rules
% 1.96/1.53  ----------------------
% 1.96/1.53  #Ref     : 0
% 1.96/1.53  #Sup     : 9
% 1.96/1.53  #Fact    : 0
% 1.96/1.53  #Define  : 0
% 1.96/1.53  #Split   : 0
% 1.96/1.53  #Chain   : 0
% 1.96/1.53  #Close   : 0
% 1.96/1.53  
% 1.96/1.53  Ordering : KBO
% 1.96/1.53  
% 1.96/1.53  Simplification rules
% 1.96/1.53  ----------------------
% 1.96/1.53  #Subsume      : 0
% 1.96/1.53  #Demod        : 2
% 1.96/1.53  #Tautology    : 5
% 1.96/1.53  #SimpNegUnit  : 0
% 1.96/1.53  #BackRed      : 0
% 1.96/1.53  
% 1.96/1.53  #Partial instantiations: 0
% 1.96/1.53  #Strategies tried      : 1
% 1.96/1.53  
% 1.96/1.53  Timing (in seconds)
% 1.96/1.53  ----------------------
% 1.96/1.54  Preprocessing        : 0.43
% 1.96/1.54  Parsing              : 0.25
% 1.96/1.54  CNF conversion       : 0.02
% 1.96/1.54  Main loop            : 0.15
% 1.96/1.54  Inferencing          : 0.07
% 1.96/1.54  Reduction            : 0.04
% 1.96/1.54  Demodulation         : 0.03
% 1.96/1.54  BG Simplification    : 0.01
% 1.96/1.54  Subsumption          : 0.02
% 1.96/1.54  Abstraction          : 0.01
% 1.96/1.54  MUC search           : 0.00
% 1.96/1.54  Cooper               : 0.00
% 1.96/1.54  Total                : 0.63
% 1.96/1.54  Index Insertion      : 0.00
% 1.96/1.54  Index Deletion       : 0.00
% 1.96/1.54  Index Matching       : 0.00
% 1.96/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
