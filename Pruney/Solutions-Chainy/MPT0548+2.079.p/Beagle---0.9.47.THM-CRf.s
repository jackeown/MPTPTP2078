%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:45 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  34 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
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

tff(f_39,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [B_9,A_10] :
      ( r1_tarski(k7_relat_1(B_9,A_10),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_10] :
      ( k7_relat_1(k1_xboole_0,A_10) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_40,plain,(
    ! [A_10] : k7_relat_1(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_37])).

tff(c_53,plain,(
    ! [B_12,A_13] :
      ( k2_relat_1(k7_relat_1(B_12,A_13)) = k9_relat_1(B_12,A_13)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_10] :
      ( k9_relat_1(k1_xboole_0,A_10) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_53])).

tff(c_66,plain,(
    ! [A_10] : k9_relat_1(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_8,c_62])).

tff(c_16,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  
% 1.68/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.68/1.10  
% 1.68/1.10  %Foreground sorts:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Background operators:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Foreground operators:
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.10  
% 1.68/1.11  tff(f_39, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.68/1.11  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.68/1.11  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.68/1.11  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.68/1.11  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.68/1.11  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.68/1.11  tff(f_46, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.68/1.11  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.11  tff(c_29, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.11  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_29])).
% 1.68/1.11  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.11  tff(c_33, plain, (![B_9, A_10]: (r1_tarski(k7_relat_1(B_9, A_10), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.11  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.11  tff(c_37, plain, (![A_10]: (k7_relat_1(k1_xboole_0, A_10)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_33, c_2])).
% 1.68/1.11  tff(c_40, plain, (![A_10]: (k7_relat_1(k1_xboole_0, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31, c_37])).
% 1.68/1.11  tff(c_53, plain, (![B_12, A_13]: (k2_relat_1(k7_relat_1(B_12, A_13))=k9_relat_1(B_12, A_13) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.11  tff(c_62, plain, (![A_10]: (k9_relat_1(k1_xboole_0, A_10)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_53])).
% 1.68/1.11  tff(c_66, plain, (![A_10]: (k9_relat_1(k1_xboole_0, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31, c_8, c_62])).
% 1.68/1.11  tff(c_16, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.68/1.11  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_16])).
% 1.68/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  Inference rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Ref     : 0
% 1.68/1.11  #Sup     : 15
% 1.68/1.11  #Fact    : 0
% 1.68/1.11  #Define  : 0
% 1.68/1.11  #Split   : 0
% 1.68/1.11  #Chain   : 0
% 1.68/1.11  #Close   : 0
% 1.68/1.11  
% 1.68/1.11  Ordering : KBO
% 1.68/1.11  
% 1.68/1.11  Simplification rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Subsume      : 0
% 1.68/1.11  #Demod        : 5
% 1.68/1.11  #Tautology    : 11
% 1.68/1.11  #SimpNegUnit  : 0
% 1.68/1.11  #BackRed      : 1
% 1.68/1.11  
% 1.68/1.11  #Partial instantiations: 0
% 1.68/1.11  #Strategies tried      : 1
% 1.68/1.11  
% 1.68/1.11  Timing (in seconds)
% 1.68/1.11  ----------------------
% 1.68/1.12  Preprocessing        : 0.26
% 1.68/1.12  Parsing              : 0.15
% 1.68/1.12  CNF conversion       : 0.01
% 1.68/1.12  Main loop            : 0.09
% 1.68/1.12  Inferencing          : 0.04
% 1.68/1.12  Reduction            : 0.03
% 1.68/1.12  Demodulation         : 0.02
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.01
% 1.68/1.12  Abstraction          : 0.00
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.38
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
