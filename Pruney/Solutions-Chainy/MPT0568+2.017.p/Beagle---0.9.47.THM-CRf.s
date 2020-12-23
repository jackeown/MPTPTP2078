%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_349,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski(A_100,'#skF_2'(A_100,B_101,C_102)),C_102)
      | ~ r2_hidden(A_100,k10_relat_1(C_102,B_101))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [C_50,B_51] : ~ r2_hidden(C_50,k4_xboole_0(B_51,k1_tarski(C_50))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_365,plain,(
    ! [A_100,B_101] :
      ( ~ r2_hidden(A_100,k10_relat_1(k1_xboole_0,B_101))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_349,c_68])).

tff(c_372,plain,(
    ! [A_103,B_104] : ~ r2_hidden(A_103,k10_relat_1(k1_xboole_0,B_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_365])).

tff(c_400,plain,(
    ! [B_104] : k10_relat_1(k1_xboole_0,B_104) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_372])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.15/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.15/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.26  
% 2.15/1.27  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.15/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.27  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.15/1.27  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.15/1.27  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.15/1.27  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.15/1.27  tff(f_79, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.15/1.27  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.27  tff(c_50, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.27  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.15/1.27  tff(c_349, plain, (![A_100, B_101, C_102]: (r2_hidden(k4_tarski(A_100, '#skF_2'(A_100, B_101, C_102)), C_102) | ~r2_hidden(A_100, k10_relat_1(C_102, B_101)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.27  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.27  tff(c_65, plain, (![C_50, B_51]: (~r2_hidden(C_50, k4_xboole_0(B_51, k1_tarski(C_50))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.27  tff(c_68, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 2.15/1.27  tff(c_365, plain, (![A_100, B_101]: (~r2_hidden(A_100, k10_relat_1(k1_xboole_0, B_101)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_349, c_68])).
% 2.15/1.27  tff(c_372, plain, (![A_103, B_104]: (~r2_hidden(A_103, k10_relat_1(k1_xboole_0, B_104)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_365])).
% 2.15/1.27  tff(c_400, plain, (![B_104]: (k10_relat_1(k1_xboole_0, B_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_372])).
% 2.15/1.27  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.27  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_400, c_42])).
% 2.15/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  Inference rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Ref     : 0
% 2.15/1.27  #Sup     : 78
% 2.15/1.27  #Fact    : 0
% 2.15/1.27  #Define  : 0
% 2.15/1.27  #Split   : 0
% 2.15/1.27  #Chain   : 0
% 2.15/1.27  #Close   : 0
% 2.15/1.27  
% 2.15/1.27  Ordering : KBO
% 2.15/1.27  
% 2.15/1.27  Simplification rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Subsume      : 18
% 2.15/1.27  #Demod        : 15
% 2.15/1.27  #Tautology    : 39
% 2.15/1.27  #SimpNegUnit  : 5
% 2.15/1.27  #BackRed      : 2
% 2.15/1.27  
% 2.15/1.27  #Partial instantiations: 0
% 2.15/1.27  #Strategies tried      : 1
% 2.15/1.27  
% 2.15/1.27  Timing (in seconds)
% 2.15/1.27  ----------------------
% 2.15/1.27  Preprocessing        : 0.31
% 2.15/1.27  Parsing              : 0.17
% 2.15/1.27  CNF conversion       : 0.02
% 2.15/1.27  Main loop            : 0.20
% 2.15/1.27  Inferencing          : 0.08
% 2.15/1.27  Reduction            : 0.06
% 2.15/1.27  Demodulation         : 0.04
% 2.15/1.27  BG Simplification    : 0.01
% 2.15/1.27  Subsumption          : 0.04
% 2.15/1.27  Abstraction          : 0.02
% 2.15/1.27  MUC search           : 0.00
% 2.15/1.27  Cooper               : 0.00
% 2.15/1.27  Total                : 0.53
% 2.15/1.27  Index Insertion      : 0.00
% 2.15/1.27  Index Deletion       : 0.00
% 2.15/1.27  Index Matching       : 0.00
% 2.15/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
