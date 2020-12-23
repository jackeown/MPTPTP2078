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
% DateTime   : Thu Dec  3 10:00:43 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   37 (  37 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_46,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_159,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski('#skF_2'(A_40,B_41,C_42),A_40),C_42)
      | ~ r2_hidden(A_40,k9_relat_1(C_42,B_41))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | ~ r1_xboole_0(k1_tarski(A_22),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_171,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,k9_relat_1(k1_xboole_0,B_41))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_159,c_57])).

tff(c_190,plain,(
    ! [A_47,B_48] : ~ r2_hidden(A_47,k9_relat_1(k1_xboole_0,B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_171])).

tff(c_213,plain,(
    ! [B_48] : k9_relat_1(k1_xboole_0,B_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_190])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.18  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.69/1.18  
% 1.69/1.18  %Foreground sorts:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Background operators:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Foreground operators:
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.69/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.69/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.18  
% 1.92/1.18  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.92/1.18  tff(f_58, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.92/1.18  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.92/1.18  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.92/1.18  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.92/1.18  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.92/1.18  tff(f_61, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.94/1.18  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.18  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.18  tff(c_30, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.18  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_30])).
% 1.94/1.18  tff(c_159, plain, (![A_40, B_41, C_42]: (r2_hidden(k4_tarski('#skF_2'(A_40, B_41, C_42), A_40), C_42) | ~r2_hidden(A_40, k9_relat_1(C_42, B_41)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.18  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.18  tff(c_52, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | ~r1_xboole_0(k1_tarski(A_22), B_23))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.18  tff(c_57, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_52])).
% 1.94/1.18  tff(c_171, plain, (![A_40, B_41]: (~r2_hidden(A_40, k9_relat_1(k1_xboole_0, B_41)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_159, c_57])).
% 1.94/1.18  tff(c_190, plain, (![A_47, B_48]: (~r2_hidden(A_47, k9_relat_1(k1_xboole_0, B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_171])).
% 1.94/1.18  tff(c_213, plain, (![B_48]: (k9_relat_1(k1_xboole_0, B_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_190])).
% 1.94/1.18  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.18  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_24])).
% 1.94/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  Inference rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Ref     : 0
% 1.94/1.18  #Sup     : 42
% 1.94/1.18  #Fact    : 0
% 1.94/1.18  #Define  : 0
% 1.94/1.18  #Split   : 0
% 1.94/1.18  #Chain   : 0
% 1.94/1.18  #Close   : 0
% 1.94/1.18  
% 1.94/1.18  Ordering : KBO
% 1.94/1.18  
% 1.94/1.18  Simplification rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Subsume      : 10
% 1.94/1.18  #Demod        : 12
% 1.94/1.18  #Tautology    : 15
% 1.94/1.18  #SimpNegUnit  : 0
% 1.94/1.18  #BackRed      : 2
% 1.94/1.18  
% 1.94/1.18  #Partial instantiations: 0
% 1.94/1.18  #Strategies tried      : 1
% 1.94/1.18  
% 1.94/1.18  Timing (in seconds)
% 1.94/1.18  ----------------------
% 1.94/1.19  Preprocessing        : 0.28
% 1.94/1.19  Parsing              : 0.15
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.15
% 1.94/1.19  Inferencing          : 0.06
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.03
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.03
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.45
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.19  Index Deletion       : 0.00
% 1.94/1.19  Index Matching       : 0.00
% 1.94/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
