%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:37 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_170,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden(k4_tarski('#skF_2'(A_47,B_48,C_49),A_47),C_49)
      | ~ r2_hidden(A_47,k9_relat_1(C_49,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | k4_xboole_0(A_28,k1_tarski(B_27)) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [B_27] : ~ r2_hidden(B_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_79])).

tff(c_182,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,k9_relat_1(k1_xboole_0,B_48))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_170,c_88])).

tff(c_188,plain,(
    ! [A_50,B_51] : ~ r2_hidden(A_50,k9_relat_1(k1_xboole_0,B_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_182])).

tff(c_211,plain,(
    ! [B_51] : k9_relat_1(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.18  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.82/1.18  
% 1.82/1.18  %Foreground sorts:
% 1.82/1.18  
% 1.82/1.18  
% 1.82/1.18  %Background operators:
% 1.82/1.18  
% 1.82/1.18  
% 1.82/1.18  %Foreground operators:
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.82/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.82/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.82/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.18  
% 1.91/1.19  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.91/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.19  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.91/1.19  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.91/1.19  tff(f_36, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.91/1.19  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.91/1.19  tff(f_65, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.91/1.19  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.91/1.19  tff(c_36, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.19  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 1.91/1.19  tff(c_170, plain, (![A_47, B_48, C_49]: (r2_hidden(k4_tarski('#skF_2'(A_47, B_48, C_49), A_47), C_49) | ~r2_hidden(A_47, k9_relat_1(C_49, B_48)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.19  tff(c_79, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | k4_xboole_0(A_28, k1_tarski(B_27))!=A_28)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.19  tff(c_88, plain, (![B_27]: (~r2_hidden(B_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_79])).
% 1.91/1.19  tff(c_182, plain, (![A_47, B_48]: (~r2_hidden(A_47, k9_relat_1(k1_xboole_0, B_48)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_170, c_88])).
% 1.91/1.19  tff(c_188, plain, (![A_50, B_51]: (~r2_hidden(A_50, k9_relat_1(k1_xboole_0, B_51)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_182])).
% 1.91/1.19  tff(c_211, plain, (![B_51]: (k9_relat_1(k1_xboole_0, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_188])).
% 1.91/1.19  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.19  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_28])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 38
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 0
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 7
% 1.91/1.19  #Demod        : 8
% 1.91/1.19  #Tautology    : 19
% 1.91/1.19  #SimpNegUnit  : 0
% 1.91/1.19  #BackRed      : 2
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.19  Preprocessing        : 0.29
% 1.91/1.20  Parsing              : 0.15
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.14
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.02
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.46
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
