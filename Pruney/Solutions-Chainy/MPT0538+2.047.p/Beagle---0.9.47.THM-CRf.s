%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k8_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_20,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23),A_23)
      | v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_51,C_52,B_53] :
      ( ~ r2_hidden(A_51,C_52)
      | ~ r1_xboole_0(k2_tarski(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_67,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ! [A_54,B_55] :
      ( k8_relat_1(A_54,B_55) = B_55
      | ~ r1_tarski(k2_relat_1(B_55),A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    ! [A_54] :
      ( k8_relat_1(A_54,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_54)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_56])).

tff(c_61,plain,(
    ! [A_54] :
      ( k8_relat_1(A_54,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_69,plain,(
    ! [A_54] : k8_relat_1(A_54,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_61])).

tff(c_28,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k8_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.79/1.18  
% 1.79/1.18  %Foreground sorts:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Background operators:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Foreground operators:
% 1.79/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.79/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.79/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.79/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.18  
% 1.79/1.19  tff(f_52, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.79/1.19  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.79/1.19  tff(f_42, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.79/1.19  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.79/1.19  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.79/1.19  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.79/1.19  tff(f_64, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.79/1.19  tff(c_20, plain, (![A_23]: (r2_hidden('#skF_1'(A_23), A_23) | v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.19  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.19  tff(c_50, plain, (![A_51, C_52, B_53]: (~r2_hidden(A_51, C_52) | ~r1_xboole_0(k2_tarski(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.19  tff(c_62, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_50])).
% 1.79/1.19  tff(c_67, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_62])).
% 1.79/1.19  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.19  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.79/1.19  tff(c_56, plain, (![A_54, B_55]: (k8_relat_1(A_54, B_55)=B_55 | ~r1_tarski(k2_relat_1(B_55), A_54) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.19  tff(c_59, plain, (![A_54]: (k8_relat_1(A_54, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_54) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_56])).
% 1.79/1.19  tff(c_61, plain, (![A_54]: (k8_relat_1(A_54, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_59])).
% 1.79/1.19  tff(c_69, plain, (![A_54]: (k8_relat_1(A_54, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_61])).
% 1.79/1.19  tff(c_28, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.79/1.19  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_28])).
% 1.79/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  Inference rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Ref     : 0
% 1.79/1.19  #Sup     : 9
% 1.79/1.19  #Fact    : 0
% 1.79/1.19  #Define  : 0
% 1.79/1.19  #Split   : 0
% 1.79/1.19  #Chain   : 0
% 1.79/1.19  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 0
% 1.79/1.19  #Demod        : 3
% 1.79/1.19  #Tautology    : 6
% 1.79/1.19  #SimpNegUnit  : 0
% 1.79/1.19  #BackRed      : 1
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.19  Timing (in seconds)
% 1.79/1.19  ----------------------
% 1.79/1.19  Preprocessing        : 0.29
% 1.79/1.19  Parsing              : 0.15
% 1.79/1.19  CNF conversion       : 0.02
% 1.79/1.19  Main loop            : 0.08
% 1.79/1.19  Inferencing          : 0.03
% 1.79/1.19  Reduction            : 0.03
% 1.79/1.19  Demodulation         : 0.02
% 1.79/1.19  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.01
% 1.79/1.20  Abstraction          : 0.01
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.40
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
