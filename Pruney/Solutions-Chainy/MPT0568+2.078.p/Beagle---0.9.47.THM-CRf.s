%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:30 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  82 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_42,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_31])).

tff(c_145,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k4_tarski(A_34,'#skF_3'(A_34,B_35,C_36)),C_36)
      | ~ r2_hidden(A_34,k10_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden('#skF_3'(A_20,B_21,C_22),B_21)
      | ~ r2_hidden(A_20,k10_relat_1(C_22,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [B_23,A_24,C_25] :
      ( ~ v1_xboole_0(B_23)
      | ~ r2_hidden(A_24,k10_relat_1(C_25,B_23))
      | ~ v1_relat_1(C_25) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_80,plain,(
    ! [B_26,C_27] :
      ( ~ v1_xboole_0(B_26)
      | ~ v1_relat_1(C_27)
      | k10_relat_1(C_27,B_26) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_84,plain,(
    ! [C_28] :
      ( ~ v1_relat_1(C_28)
      | k10_relat_1(C_28,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_91,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_84])).

tff(c_63,plain,(
    ! [B_21,A_20,C_22] :
      ( ~ v1_xboole_0(B_21)
      | ~ r2_hidden(A_20,k10_relat_1(C_22,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_106,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_20,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_63])).

tff(c_110,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_6,c_106])).

tff(c_149,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden(A_34,k10_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_145,c_110])).

tff(c_162,plain,(
    ! [A_37,B_38] : ~ r2_hidden(A_37,k10_relat_1(k1_xboole_0,B_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_149])).

tff(c_183,plain,(
    ! [B_38] : k10_relat_1(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_26,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.83/1.19  
% 1.83/1.19  %Foreground sorts:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Background operators:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Foreground operators:
% 1.83/1.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.83/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.83/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.83/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.19  
% 1.83/1.20  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.83/1.20  tff(f_57, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.83/1.20  tff(f_42, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.83/1.20  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.83/1.20  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.83/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.83/1.20  tff(f_60, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.83/1.20  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.20  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.83/1.20  tff(c_31, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.83/1.20  tff(c_33, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_31])).
% 1.83/1.20  tff(c_145, plain, (![A_34, B_35, C_36]: (r2_hidden(k4_tarski(A_34, '#skF_3'(A_34, B_35, C_36)), C_36) | ~r2_hidden(A_34, k10_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.20  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.20  tff(c_59, plain, (![A_20, B_21, C_22]: (r2_hidden('#skF_3'(A_20, B_21, C_22), B_21) | ~r2_hidden(A_20, k10_relat_1(C_22, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.20  tff(c_64, plain, (![B_23, A_24, C_25]: (~v1_xboole_0(B_23) | ~r2_hidden(A_24, k10_relat_1(C_25, B_23)) | ~v1_relat_1(C_25))), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.83/1.20  tff(c_80, plain, (![B_26, C_27]: (~v1_xboole_0(B_26) | ~v1_relat_1(C_27) | k10_relat_1(C_27, B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_64])).
% 1.83/1.20  tff(c_84, plain, (![C_28]: (~v1_relat_1(C_28) | k10_relat_1(C_28, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_80])).
% 1.83/1.20  tff(c_91, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_84])).
% 1.83/1.20  tff(c_63, plain, (![B_21, A_20, C_22]: (~v1_xboole_0(B_21) | ~r2_hidden(A_20, k10_relat_1(C_22, B_21)) | ~v1_relat_1(C_22))), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.83/1.20  tff(c_106, plain, (![A_20]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_20, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_91, c_63])).
% 1.83/1.20  tff(c_110, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_6, c_106])).
% 1.83/1.20  tff(c_149, plain, (![A_34, B_35]: (~r2_hidden(A_34, k10_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_145, c_110])).
% 1.83/1.20  tff(c_162, plain, (![A_37, B_38]: (~r2_hidden(A_37, k10_relat_1(k1_xboole_0, B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_149])).
% 1.83/1.20  tff(c_183, plain, (![B_38]: (k10_relat_1(k1_xboole_0, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_162])).
% 1.83/1.20  tff(c_26, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.83/1.20  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_26])).
% 1.83/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  Inference rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Ref     : 0
% 1.83/1.20  #Sup     : 37
% 1.83/1.20  #Fact    : 0
% 1.83/1.20  #Define  : 0
% 1.83/1.20  #Split   : 0
% 1.83/1.20  #Chain   : 0
% 1.83/1.20  #Close   : 0
% 1.83/1.20  
% 1.83/1.20  Ordering : KBO
% 1.83/1.20  
% 1.83/1.20  Simplification rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Subsume      : 3
% 1.83/1.20  #Demod        : 11
% 1.83/1.20  #Tautology    : 16
% 1.83/1.20  #SimpNegUnit  : 0
% 1.83/1.20  #BackRed      : 2
% 1.83/1.20  
% 1.83/1.20  #Partial instantiations: 0
% 1.83/1.20  #Strategies tried      : 1
% 1.83/1.20  
% 1.83/1.20  Timing (in seconds)
% 1.83/1.20  ----------------------
% 1.83/1.20  Preprocessing        : 0.26
% 1.83/1.20  Parsing              : 0.14
% 1.83/1.20  CNF conversion       : 0.02
% 1.83/1.20  Main loop            : 0.15
% 1.83/1.20  Inferencing          : 0.07
% 1.83/1.20  Reduction            : 0.04
% 1.83/1.20  Demodulation         : 0.03
% 1.83/1.21  BG Simplification    : 0.01
% 1.83/1.21  Subsumption          : 0.03
% 1.83/1.21  Abstraction          : 0.01
% 1.83/1.21  MUC search           : 0.00
% 1.83/1.21  Cooper               : 0.00
% 1.83/1.21  Total                : 0.43
% 1.83/1.21  Index Insertion      : 0.00
% 1.83/1.21  Index Deletion       : 0.00
% 1.83/1.21  Index Matching       : 0.00
% 1.83/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
