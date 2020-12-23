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
% DateTime   : Thu Dec  3 10:01:33 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_74,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_62,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_47])).

tff(c_390,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden(k4_tarski(A_101,'#skF_2'(A_101,B_102,C_103)),C_103)
      | ~ r2_hidden(A_101,k10_relat_1(C_103,B_102))
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [C_49,B_50] : ~ r2_hidden(C_49,k4_xboole_0(B_50,k1_tarski(C_49))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_406,plain,(
    ! [A_101,B_102] :
      ( ~ r2_hidden(A_101,k10_relat_1(k1_xboole_0,B_102))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_390,c_69])).

tff(c_413,plain,(
    ! [A_104,B_105] : ~ r2_hidden(A_104,k10_relat_1(k1_xboole_0,B_105)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_406])).

tff(c_441,plain,(
    ! [B_105] : k10_relat_1(k1_xboole_0,B_105) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_413])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.17/1.27  
% 2.17/1.27  %Foreground sorts:
% 2.17/1.27  
% 2.17/1.27  
% 2.17/1.27  %Background operators:
% 2.17/1.27  
% 2.17/1.27  
% 2.17/1.27  %Foreground operators:
% 2.17/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.17/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.17/1.27  
% 2.17/1.28  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.17/1.28  tff(f_74, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.17/1.28  tff(f_62, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.17/1.28  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.17/1.28  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.17/1.28  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.17/1.28  tff(f_77, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.17/1.28  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.28  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.28  tff(c_47, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.28  tff(c_49, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_47])).
% 2.17/1.28  tff(c_390, plain, (![A_101, B_102, C_103]: (r2_hidden(k4_tarski(A_101, '#skF_2'(A_101, B_102, C_103)), C_103) | ~r2_hidden(A_101, k10_relat_1(C_103, B_102)) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.28  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.28  tff(c_66, plain, (![C_49, B_50]: (~r2_hidden(C_49, k4_xboole_0(B_50, k1_tarski(C_49))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.28  tff(c_69, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.17/1.28  tff(c_406, plain, (![A_101, B_102]: (~r2_hidden(A_101, k10_relat_1(k1_xboole_0, B_102)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_390, c_69])).
% 2.17/1.28  tff(c_413, plain, (![A_104, B_105]: (~r2_hidden(A_104, k10_relat_1(k1_xboole_0, B_105)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_406])).
% 2.17/1.28  tff(c_441, plain, (![B_105]: (k10_relat_1(k1_xboole_0, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_413])).
% 2.17/1.28  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.17/1.28  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_441, c_42])).
% 2.17/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  Inference rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Ref     : 0
% 2.17/1.28  #Sup     : 89
% 2.17/1.28  #Fact    : 0
% 2.17/1.28  #Define  : 0
% 2.17/1.28  #Split   : 0
% 2.17/1.28  #Chain   : 0
% 2.17/1.28  #Close   : 0
% 2.17/1.28  
% 2.17/1.28  Ordering : KBO
% 2.17/1.28  
% 2.17/1.28  Simplification rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Subsume      : 22
% 2.17/1.28  #Demod        : 22
% 2.17/1.28  #Tautology    : 45
% 2.17/1.28  #SimpNegUnit  : 5
% 2.17/1.28  #BackRed      : 2
% 2.17/1.28  
% 2.17/1.28  #Partial instantiations: 0
% 2.17/1.28  #Strategies tried      : 1
% 2.17/1.28  
% 2.17/1.28  Timing (in seconds)
% 2.17/1.28  ----------------------
% 2.17/1.28  Preprocessing        : 0.31
% 2.17/1.28  Parsing              : 0.17
% 2.17/1.28  CNF conversion       : 0.02
% 2.17/1.28  Main loop            : 0.22
% 2.17/1.28  Inferencing          : 0.09
% 2.17/1.28  Reduction            : 0.07
% 2.17/1.28  Demodulation         : 0.05
% 2.17/1.28  BG Simplification    : 0.02
% 2.17/1.28  Subsumption          : 0.04
% 2.17/1.28  Abstraction          : 0.02
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.55
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.29  Index Deletion       : 0.00
% 2.17/1.29  Index Matching       : 0.00
% 2.17/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
