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
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_44,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_679,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden('#skF_2'(A_86,B_87,C_88),B_87)
      | ~ r2_hidden(A_86,k10_relat_1(C_88,B_87))
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [C_42,B_43] : ~ r2_hidden(C_42,k4_xboole_0(B_43,k1_tarski(C_42))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [C_42] : ~ r2_hidden(C_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_690,plain,(
    ! [A_89,C_90] :
      ( ~ r2_hidden(A_89,k10_relat_1(C_90,k1_xboole_0))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_679,c_79])).

tff(c_706,plain,(
    ! [C_91] :
      ( ~ v1_relat_1(C_91)
      | k10_relat_1(C_91,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_690])).

tff(c_709,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_706])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.48  
% 2.42/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.48  %$ r2_hidden > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.42/1.48  
% 2.42/1.48  %Foreground sorts:
% 2.42/1.48  
% 2.42/1.48  
% 2.42/1.48  %Background operators:
% 2.42/1.48  
% 2.42/1.48  
% 2.42/1.48  %Foreground operators:
% 2.42/1.48  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.42/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.42/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.42/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.49  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.42/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.42/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.42/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.42/1.49  
% 2.62/1.49  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.62/1.49  tff(f_36, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.62/1.49  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.62/1.49  tff(f_42, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.62/1.49  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.62/1.49  tff(c_44, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.62/1.49  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.62/1.49  tff(c_6, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.49  tff(c_679, plain, (![A_86, B_87, C_88]: (r2_hidden('#skF_2'(A_86, B_87, C_88), B_87) | ~r2_hidden(A_86, k10_relat_1(C_88, B_87)) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.62/1.49  tff(c_12, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.49  tff(c_76, plain, (![C_42, B_43]: (~r2_hidden(C_42, k4_xboole_0(B_43, k1_tarski(C_42))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.49  tff(c_79, plain, (![C_42]: (~r2_hidden(C_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_76])).
% 2.62/1.49  tff(c_690, plain, (![A_89, C_90]: (~r2_hidden(A_89, k10_relat_1(C_90, k1_xboole_0)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_679, c_79])).
% 2.62/1.49  tff(c_706, plain, (![C_91]: (~v1_relat_1(C_91) | k10_relat_1(C_91, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_690])).
% 2.62/1.49  tff(c_709, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_706])).
% 2.62/1.49  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_709])).
% 2.62/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.49  
% 2.62/1.49  Inference rules
% 2.62/1.49  ----------------------
% 2.62/1.49  #Ref     : 0
% 2.62/1.49  #Sup     : 152
% 2.62/1.49  #Fact    : 0
% 2.62/1.49  #Define  : 0
% 2.62/1.49  #Split   : 0
% 2.62/1.49  #Chain   : 0
% 2.62/1.49  #Close   : 0
% 2.62/1.49  
% 2.62/1.49  Ordering : KBO
% 2.62/1.49  
% 2.62/1.49  Simplification rules
% 2.62/1.49  ----------------------
% 2.62/1.49  #Subsume      : 6
% 2.62/1.49  #Demod        : 93
% 2.62/1.49  #Tautology    : 113
% 2.62/1.49  #SimpNegUnit  : 4
% 2.62/1.49  #BackRed      : 0
% 2.62/1.49  
% 2.62/1.49  #Partial instantiations: 0
% 2.62/1.49  #Strategies tried      : 1
% 2.62/1.49  
% 2.62/1.49  Timing (in seconds)
% 2.62/1.49  ----------------------
% 2.62/1.50  Preprocessing        : 0.38
% 2.62/1.50  Parsing              : 0.21
% 2.62/1.50  CNF conversion       : 0.02
% 2.62/1.50  Main loop            : 0.26
% 2.62/1.50  Inferencing          : 0.10
% 2.62/1.50  Reduction            : 0.09
% 2.62/1.50  Demodulation         : 0.07
% 2.62/1.50  BG Simplification    : 0.02
% 2.62/1.50  Subsumption          : 0.03
% 2.62/1.50  Abstraction          : 0.02
% 2.62/1.50  MUC search           : 0.00
% 2.62/1.50  Cooper               : 0.00
% 2.62/1.50  Total                : 0.66
% 2.62/1.50  Index Insertion      : 0.00
% 2.62/1.50  Index Deletion       : 0.00
% 2.62/1.50  Index Matching       : 0.00
% 2.62/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
