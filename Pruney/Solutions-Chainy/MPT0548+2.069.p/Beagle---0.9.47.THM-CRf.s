%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:44 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_33])).

tff(c_179,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k4_tarski('#skF_2'(A_46,B_47,C_48),A_46),C_48)
      | ~ r2_hidden(A_46,k9_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | k4_xboole_0(A_28,k1_tarski(B_27)) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [B_27] : ~ r2_hidden(B_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_81])).

tff(c_191,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,k9_relat_1(k1_xboole_0,B_47))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_179,c_90])).

tff(c_197,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k9_relat_1(k1_xboole_0,B_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_191])).

tff(c_214,plain,(
    ! [B_50] : k9_relat_1(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_197])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.22  
% 1.84/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.22  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.84/1.22  
% 1.84/1.22  %Foreground sorts:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Background operators:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Foreground operators:
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.84/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.84/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.84/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.84/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.22  
% 1.87/1.23  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.87/1.23  tff(f_60, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.87/1.23  tff(f_48, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.87/1.23  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.87/1.23  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.87/1.23  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.87/1.23  tff(f_63, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.87/1.23  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.23  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.23  tff(c_33, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.87/1.23  tff(c_35, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_33])).
% 1.87/1.23  tff(c_179, plain, (![A_46, B_47, C_48]: (r2_hidden(k4_tarski('#skF_2'(A_46, B_47, C_48), A_46), C_48) | ~r2_hidden(A_46, k9_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.23  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.23  tff(c_81, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | k4_xboole_0(A_28, k1_tarski(B_27))!=A_28)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.23  tff(c_90, plain, (![B_27]: (~r2_hidden(B_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_81])).
% 1.87/1.23  tff(c_191, plain, (![A_46, B_47]: (~r2_hidden(A_46, k9_relat_1(k1_xboole_0, B_47)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_179, c_90])).
% 1.87/1.23  tff(c_197, plain, (![A_49, B_50]: (~r2_hidden(A_49, k9_relat_1(k1_xboole_0, B_50)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_191])).
% 1.87/1.23  tff(c_214, plain, (![B_50]: (k9_relat_1(k1_xboole_0, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_197])).
% 1.87/1.23  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.87/1.23  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_28])).
% 1.87/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.23  
% 1.87/1.23  Inference rules
% 1.87/1.23  ----------------------
% 1.87/1.23  #Ref     : 0
% 1.87/1.23  #Sup     : 41
% 1.87/1.23  #Fact    : 0
% 1.87/1.23  #Define  : 0
% 1.87/1.23  #Split   : 0
% 1.87/1.23  #Chain   : 0
% 1.87/1.23  #Close   : 0
% 1.87/1.23  
% 1.87/1.23  Ordering : KBO
% 1.87/1.23  
% 1.87/1.23  Simplification rules
% 1.87/1.23  ----------------------
% 1.87/1.23  #Subsume      : 6
% 1.87/1.23  #Demod        : 9
% 1.87/1.23  #Tautology    : 22
% 1.87/1.23  #SimpNegUnit  : 0
% 1.87/1.23  #BackRed      : 2
% 1.87/1.23  
% 1.87/1.23  #Partial instantiations: 0
% 1.87/1.23  #Strategies tried      : 1
% 1.87/1.23  
% 1.87/1.23  Timing (in seconds)
% 1.87/1.23  ----------------------
% 1.87/1.24  Preprocessing        : 0.27
% 1.87/1.24  Parsing              : 0.14
% 1.87/1.24  CNF conversion       : 0.02
% 1.87/1.24  Main loop            : 0.14
% 1.87/1.24  Inferencing          : 0.06
% 1.87/1.24  Reduction            : 0.04
% 1.87/1.24  Demodulation         : 0.03
% 1.87/1.24  BG Simplification    : 0.01
% 1.87/1.24  Subsumption          : 0.02
% 1.87/1.24  Abstraction          : 0.01
% 1.87/1.24  MUC search           : 0.00
% 1.87/1.24  Cooper               : 0.00
% 1.87/1.24  Total                : 0.43
% 1.87/1.24  Index Insertion      : 0.00
% 1.87/1.24  Index Deletion       : 0.00
% 1.87/1.24  Index Matching       : 0.00
% 1.87/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
