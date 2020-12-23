%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:47 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [B_19,A_20] :
      ( k7_relat_1(B_19,A_20) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    ! [A_20] :
      ( k7_relat_1(k1_xboole_0,A_20) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_20)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_84,plain,(
    ! [A_21] : k7_relat_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_81])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_21] :
      ( k9_relat_1(k1_xboole_0,A_21) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_12])).

tff(c_94,plain,(
    ! [A_21] : k9_relat_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14,c_89])).

tff(c_20,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.12  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.70/1.12  
% 1.70/1.12  %Foreground sorts:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Background operators:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Foreground operators:
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.70/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.70/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.12  
% 1.70/1.13  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.70/1.13  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.70/1.13  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.70/1.13  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.70/1.13  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.70/1.13  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.70/1.13  tff(f_51, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.70/1.13  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.13  tff(c_52, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.13  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 1.70/1.13  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.13  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.13  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.13  tff(c_78, plain, (![B_19, A_20]: (k7_relat_1(B_19, A_20)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.13  tff(c_81, plain, (![A_20]: (k7_relat_1(k1_xboole_0, A_20)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_20) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_78])).
% 1.70/1.13  tff(c_84, plain, (![A_21]: (k7_relat_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_81])).
% 1.70/1.13  tff(c_12, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.70/1.13  tff(c_89, plain, (![A_21]: (k9_relat_1(k1_xboole_0, A_21)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_84, c_12])).
% 1.70/1.13  tff(c_94, plain, (![A_21]: (k9_relat_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14, c_89])).
% 1.70/1.13  tff(c_20, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.13  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_20])).
% 1.70/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.13  
% 1.70/1.13  Inference rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Ref     : 0
% 1.70/1.13  #Sup     : 20
% 1.70/1.13  #Fact    : 0
% 1.70/1.13  #Define  : 0
% 1.70/1.13  #Split   : 0
% 1.70/1.13  #Chain   : 0
% 1.70/1.13  #Close   : 0
% 1.70/1.13  
% 1.70/1.13  Ordering : KBO
% 1.70/1.13  
% 1.70/1.13  Simplification rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Subsume      : 0
% 1.70/1.13  #Demod        : 6
% 1.70/1.13  #Tautology    : 17
% 1.70/1.13  #SimpNegUnit  : 0
% 1.70/1.13  #BackRed      : 1
% 1.70/1.13  
% 1.70/1.13  #Partial instantiations: 0
% 1.70/1.13  #Strategies tried      : 1
% 1.70/1.13  
% 1.70/1.13  Timing (in seconds)
% 1.70/1.13  ----------------------
% 1.70/1.13  Preprocessing        : 0.26
% 1.70/1.13  Parsing              : 0.15
% 1.70/1.13  CNF conversion       : 0.02
% 1.70/1.13  Main loop            : 0.10
% 1.70/1.13  Inferencing          : 0.04
% 1.70/1.13  Reduction            : 0.03
% 1.70/1.13  Demodulation         : 0.02
% 1.70/1.13  BG Simplification    : 0.01
% 1.70/1.13  Subsumption          : 0.01
% 1.70/1.13  Abstraction          : 0.00
% 1.70/1.13  MUC search           : 0.00
% 1.70/1.13  Cooper               : 0.00
% 1.70/1.13  Total                : 0.38
% 1.70/1.13  Index Insertion      : 0.00
% 1.70/1.13  Index Deletion       : 0.00
% 1.70/1.13  Index Matching       : 0.00
% 1.70/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
