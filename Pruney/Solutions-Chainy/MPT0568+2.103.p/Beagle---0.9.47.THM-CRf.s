%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,(
    ! [A_41] : v1_relat_1(k6_relat_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_37])).

tff(c_163,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden(k4_tarski(A_75,'#skF_2'(A_75,B_76,C_77)),C_77)
      | ~ r2_hidden(A_75,k10_relat_1(C_77,B_76))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r2_hidden(A_46,C_47)
      | ~ r1_xboole_0(k2_tarski(A_46,B_48),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_51])).

tff(c_175,plain,(
    ! [A_75,B_76] :
      ( ~ r2_hidden(A_75,k10_relat_1(k1_xboole_0,B_76))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_163,c_56])).

tff(c_181,plain,(
    ! [A_78,B_79] : ~ r2_hidden(A_78,k10_relat_1(k1_xboole_0,B_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_175])).

tff(c_198,plain,(
    ! [B_79] : k10_relat_1(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_181])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.98/1.20  
% 1.98/1.20  %Foreground sorts:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Background operators:
% 1.98/1.20  
% 1.98/1.20  
% 1.98/1.20  %Foreground operators:
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.98/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.98/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.20  
% 1.98/1.21  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.98/1.21  tff(f_66, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.98/1.21  tff(f_54, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.98/1.21  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.98/1.21  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.98/1.21  tff(f_52, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.98/1.21  tff(f_69, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.98/1.21  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.21  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.98/1.21  tff(c_37, plain, (![A_41]: (v1_relat_1(k6_relat_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.21  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_37])).
% 1.98/1.21  tff(c_163, plain, (![A_75, B_76, C_77]: (r2_hidden(k4_tarski(A_75, '#skF_2'(A_75, B_76, C_77)), C_77) | ~r2_hidden(A_75, k10_relat_1(C_77, B_76)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.21  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.21  tff(c_51, plain, (![A_46, C_47, B_48]: (~r2_hidden(A_46, C_47) | ~r1_xboole_0(k2_tarski(A_46, B_48), C_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.98/1.21  tff(c_56, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_51])).
% 1.98/1.21  tff(c_175, plain, (![A_75, B_76]: (~r2_hidden(A_75, k10_relat_1(k1_xboole_0, B_76)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_163, c_56])).
% 1.98/1.21  tff(c_181, plain, (![A_78, B_79]: (~r2_hidden(A_78, k10_relat_1(k1_xboole_0, B_79)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_175])).
% 1.98/1.21  tff(c_198, plain, (![B_79]: (k10_relat_1(k1_xboole_0, B_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_181])).
% 1.98/1.21  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.98/1.21  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_32])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 36
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 0
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 6
% 1.98/1.21  #Demod        : 9
% 1.98/1.21  #Tautology    : 17
% 1.98/1.21  #SimpNegUnit  : 0
% 1.98/1.21  #BackRed      : 2
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.21  Preprocessing        : 0.30
% 1.98/1.21  Parsing              : 0.16
% 1.98/1.21  CNF conversion       : 0.02
% 1.98/1.21  Main loop            : 0.14
% 1.98/1.21  Inferencing          : 0.06
% 1.98/1.21  Reduction            : 0.04
% 1.98/1.22  Demodulation         : 0.03
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.02
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.46
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
