%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(f_62,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_33])).

tff(c_181,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden(k4_tarski(A_64,'#skF_2'(A_64,B_65,C_66)),C_66)
      | ~ r2_hidden(A_64,k10_relat_1(C_66,B_65))
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_33,C_34,B_35] :
      ( ~ r2_hidden(A_33,C_34)
      | ~ r1_xboole_0(k2_tarski(A_33,B_35),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_47])).

tff(c_193,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden(A_64,k10_relat_1(k1_xboole_0,B_65))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_181,c_52])).

tff(c_199,plain,(
    ! [A_67,B_68] : ~ r2_hidden(A_67,k10_relat_1(k1_xboole_0,B_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_193])).

tff(c_222,plain,(
    ! [B_68] : k10_relat_1(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_199])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.03/1.23  
% 2.03/1.23  %Foreground sorts:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Background operators:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Foreground operators:
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.03/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.23  
% 2.05/1.24  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.05/1.24  tff(f_62, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.05/1.24  tff(f_50, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.05/1.24  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.05/1.24  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.05/1.24  tff(f_48, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.05/1.24  tff(f_65, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.05/1.24  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.24  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.24  tff(c_33, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.05/1.24  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_33])).
% 2.05/1.24  tff(c_181, plain, (![A_64, B_65, C_66]: (r2_hidden(k4_tarski(A_64, '#skF_2'(A_64, B_65, C_66)), C_66) | ~r2_hidden(A_64, k10_relat_1(C_66, B_65)) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.24  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.24  tff(c_47, plain, (![A_33, C_34, B_35]: (~r2_hidden(A_33, C_34) | ~r1_xboole_0(k2_tarski(A_33, B_35), C_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.05/1.24  tff(c_52, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_47])).
% 2.05/1.24  tff(c_193, plain, (![A_64, B_65]: (~r2_hidden(A_64, k10_relat_1(k1_xboole_0, B_65)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_181, c_52])).
% 2.05/1.24  tff(c_199, plain, (![A_67, B_68]: (~r2_hidden(A_67, k10_relat_1(k1_xboole_0, B_68)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_193])).
% 2.05/1.24  tff(c_222, plain, (![B_68]: (k10_relat_1(k1_xboole_0, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_199])).
% 2.05/1.24  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.05/1.24  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_28])).
% 2.05/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  Inference rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Ref     : 0
% 2.05/1.24  #Sup     : 42
% 2.05/1.24  #Fact    : 0
% 2.05/1.24  #Define  : 0
% 2.05/1.24  #Split   : 0
% 2.05/1.24  #Chain   : 0
% 2.05/1.24  #Close   : 0
% 2.05/1.24  
% 2.05/1.24  Ordering : KBO
% 2.05/1.24  
% 2.05/1.24  Simplification rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Subsume      : 10
% 2.05/1.24  #Demod        : 12
% 2.05/1.24  #Tautology    : 19
% 2.05/1.24  #SimpNegUnit  : 0
% 2.05/1.24  #BackRed      : 2
% 2.05/1.24  
% 2.05/1.24  #Partial instantiations: 0
% 2.05/1.24  #Strategies tried      : 1
% 2.05/1.24  
% 2.05/1.24  Timing (in seconds)
% 2.05/1.24  ----------------------
% 2.05/1.25  Preprocessing        : 0.33
% 2.05/1.25  Parsing              : 0.17
% 2.05/1.25  CNF conversion       : 0.02
% 2.05/1.25  Main loop            : 0.15
% 2.05/1.25  Inferencing          : 0.06
% 2.05/1.25  Reduction            : 0.04
% 2.05/1.25  Demodulation         : 0.03
% 2.05/1.25  BG Simplification    : 0.01
% 2.05/1.25  Subsumption          : 0.02
% 2.05/1.25  Abstraction          : 0.02
% 2.05/1.25  MUC search           : 0.00
% 2.05/1.25  Cooper               : 0.00
% 2.05/1.25  Total                : 0.51
% 2.05/1.25  Index Insertion      : 0.00
% 2.05/1.25  Index Deletion       : 0.00
% 2.05/1.25  Index Matching       : 0.00
% 2.05/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
