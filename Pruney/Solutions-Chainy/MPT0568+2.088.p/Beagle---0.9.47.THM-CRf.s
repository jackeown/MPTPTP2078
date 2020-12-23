%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:32 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  51 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_49,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_49])).

tff(c_490,plain,(
    ! [A_120,B_121,C_122] :
      ( r2_hidden(k4_tarski(A_120,'#skF_2'(A_120,B_121,C_122)),C_122)
      | ~ r2_hidden(A_120,k10_relat_1(C_122,B_121))
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_123,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_26,plain,(
    ! [C_38,B_37] : ~ r2_hidden(C_38,k4_xboole_0(B_37,k1_tarski(C_38))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_26])).

tff(c_514,plain,(
    ! [A_120,B_121] :
      ( ~ r2_hidden(A_120,k10_relat_1(k1_xboole_0,B_121))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_490,c_128])).

tff(c_532,plain,(
    ! [A_130,B_131] : ~ r2_hidden(A_130,k10_relat_1(k1_xboole_0,B_131)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_514])).

tff(c_560,plain,(
    ! [B_131] : k10_relat_1(k1_xboole_0,B_131) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_532])).

tff(c_44,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:07:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.16/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.30  
% 2.16/1.31  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.16/1.31  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.16/1.31  tff(f_64, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.16/1.31  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.16/1.31  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.16/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.16/1.31  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.31  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.16/1.31  tff(f_79, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.16/1.31  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.31  tff(c_42, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.31  tff(c_49, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.31  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_49])).
% 2.16/1.31  tff(c_490, plain, (![A_120, B_121, C_122]: (r2_hidden(k4_tarski(A_120, '#skF_2'(A_120, B_121, C_122)), C_122) | ~r2_hidden(A_120, k10_relat_1(C_122, B_121)) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.16/1.31  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.31  tff(c_110, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.31  tff(c_119, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 2.16/1.31  tff(c_123, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_119])).
% 2.16/1.31  tff(c_26, plain, (![C_38, B_37]: (~r2_hidden(C_38, k4_xboole_0(B_37, k1_tarski(C_38))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.31  tff(c_128, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_123, c_26])).
% 2.16/1.31  tff(c_514, plain, (![A_120, B_121]: (~r2_hidden(A_120, k10_relat_1(k1_xboole_0, B_121)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_490, c_128])).
% 2.16/1.31  tff(c_532, plain, (![A_130, B_131]: (~r2_hidden(A_130, k10_relat_1(k1_xboole_0, B_131)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_514])).
% 2.16/1.31  tff(c_560, plain, (![B_131]: (k10_relat_1(k1_xboole_0, B_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_532])).
% 2.16/1.31  tff(c_44, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.31  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_44])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 115
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 0
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 24
% 2.16/1.31  #Demod        : 24
% 2.16/1.31  #Tautology    : 56
% 2.16/1.31  #SimpNegUnit  : 6
% 2.16/1.31  #BackRed      : 2
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.31  Preprocessing        : 0.31
% 2.16/1.31  Parsing              : 0.16
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.25
% 2.16/1.31  Inferencing          : 0.10
% 2.16/1.31  Reduction            : 0.07
% 2.16/1.31  Demodulation         : 0.05
% 2.16/1.31  BG Simplification    : 0.02
% 2.16/1.32  Subsumption          : 0.04
% 2.16/1.32  Abstraction          : 0.02
% 2.16/1.32  MUC search           : 0.00
% 2.16/1.32  Cooper               : 0.00
% 2.16/1.32  Total                : 0.59
% 2.16/1.32  Index Insertion      : 0.00
% 2.16/1.32  Index Deletion       : 0.00
% 2.16/1.32  Index Matching       : 0.00
% 2.16/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
