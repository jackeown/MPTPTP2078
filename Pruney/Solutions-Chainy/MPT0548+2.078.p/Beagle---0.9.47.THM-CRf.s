%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:45 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  38 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_30])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    ! [B_11,A_12] :
      ( k7_relat_1(B_11,A_12) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_12)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_12] :
      ( k7_relat_1(k1_xboole_0,A_12) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_48,plain,(
    ! [A_13] : k7_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_45])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_13] :
      ( k9_relat_1(k1_xboole_0,A_13) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_58,plain,(
    ! [A_13] : k9_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8,c_53])).

tff(c_16,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.07  
% 1.48/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.07  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.48/1.07  
% 1.48/1.07  %Foreground sorts:
% 1.48/1.07  
% 1.48/1.07  
% 1.48/1.07  %Background operators:
% 1.48/1.07  
% 1.48/1.07  
% 1.48/1.07  %Foreground operators:
% 1.48/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.48/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.48/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.48/1.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.48/1.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.48/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.48/1.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.48/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.48/1.07  
% 1.61/1.08  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.61/1.08  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.61/1.08  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.61/1.08  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.61/1.08  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.61/1.08  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.61/1.08  tff(f_46, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.61/1.08  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.08  tff(c_30, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.08  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_30])).
% 1.61/1.08  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.08  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.08  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.08  tff(c_42, plain, (![B_11, A_12]: (k7_relat_1(B_11, A_12)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_12) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.61/1.08  tff(c_45, plain, (![A_12]: (k7_relat_1(k1_xboole_0, A_12)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_12) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_42])).
% 1.61/1.08  tff(c_48, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_45])).
% 1.61/1.08  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.08  tff(c_53, plain, (![A_13]: (k9_relat_1(k1_xboole_0, A_13)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6])).
% 1.61/1.08  tff(c_58, plain, (![A_13]: (k9_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8, c_53])).
% 1.61/1.08  tff(c_16, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.08  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_16])).
% 1.61/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.08  
% 1.61/1.08  Inference rules
% 1.61/1.08  ----------------------
% 1.61/1.08  #Ref     : 0
% 1.61/1.08  #Sup     : 13
% 1.61/1.08  #Fact    : 0
% 1.61/1.08  #Define  : 0
% 1.61/1.08  #Split   : 0
% 1.61/1.08  #Chain   : 0
% 1.61/1.08  #Close   : 0
% 1.61/1.08  
% 1.61/1.08  Ordering : KBO
% 1.61/1.08  
% 1.61/1.08  Simplification rules
% 1.61/1.08  ----------------------
% 1.61/1.08  #Subsume      : 0
% 1.61/1.08  #Demod        : 5
% 1.61/1.08  #Tautology    : 10
% 1.61/1.08  #SimpNegUnit  : 0
% 1.61/1.08  #BackRed      : 1
% 1.61/1.08  
% 1.61/1.08  #Partial instantiations: 0
% 1.61/1.08  #Strategies tried      : 1
% 1.61/1.08  
% 1.61/1.08  Timing (in seconds)
% 1.61/1.08  ----------------------
% 1.61/1.08  Preprocessing        : 0.25
% 1.61/1.08  Parsing              : 0.14
% 1.61/1.08  CNF conversion       : 0.01
% 1.61/1.08  Main loop            : 0.09
% 1.61/1.08  Inferencing          : 0.04
% 1.61/1.08  Reduction            : 0.02
% 1.61/1.08  Demodulation         : 0.02
% 1.61/1.08  BG Simplification    : 0.01
% 1.61/1.08  Subsumption          : 0.01
% 1.61/1.08  Abstraction          : 0.00
% 1.61/1.08  MUC search           : 0.00
% 1.61/1.08  Cooper               : 0.00
% 1.61/1.08  Total                : 0.36
% 1.61/1.08  Index Insertion      : 0.00
% 1.61/1.08  Index Deletion       : 0.00
% 1.61/1.08  Index Matching       : 0.00
% 1.61/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
