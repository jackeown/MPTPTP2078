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
% DateTime   : Thu Dec  3 10:00:30 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  31 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_4,plain,(
    ! [A_2,B_3] : v1_relat_1(k2_zfmisc_1(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13,plain,(
    ! [A_11] :
      ( k8_relat_1(k1_xboole_0,A_11) = k1_xboole_0
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17,plain,(
    ! [A_2,B_3] : k8_relat_1(k1_xboole_0,k2_zfmisc_1(A_2,B_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_13])).

tff(c_25,plain,(
    ! [B_14,A_15,C_16] :
      ( k8_relat_1(B_14,k8_relat_1(A_15,C_16)) = k8_relat_1(A_15,C_16)
      | ~ r1_tarski(A_15,B_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_2,B_3,B_14] :
      ( k8_relat_1(k1_xboole_0,k2_zfmisc_1(A_2,B_3)) = k8_relat_1(B_14,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_14)
      | ~ v1_relat_1(k2_zfmisc_1(A_2,B_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_25])).

tff(c_44,plain,(
    ! [B_14] : k8_relat_1(B_14,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_17,c_40])).

tff(c_10,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.61/1.10  
% 1.61/1.10  %Foreground sorts:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Background operators:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Foreground operators:
% 1.61/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.10  
% 1.61/1.11  tff(f_29, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.61/1.11  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.61/1.11  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.61/1.11  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.61/1.11  tff(f_42, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.61/1.11  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k2_zfmisc_1(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.11  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.11  tff(c_13, plain, (![A_11]: (k8_relat_1(k1_xboole_0, A_11)=k1_xboole_0 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.11  tff(c_17, plain, (![A_2, B_3]: (k8_relat_1(k1_xboole_0, k2_zfmisc_1(A_2, B_3))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_13])).
% 1.61/1.11  tff(c_25, plain, (![B_14, A_15, C_16]: (k8_relat_1(B_14, k8_relat_1(A_15, C_16))=k8_relat_1(A_15, C_16) | ~r1_tarski(A_15, B_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.11  tff(c_40, plain, (![A_2, B_3, B_14]: (k8_relat_1(k1_xboole_0, k2_zfmisc_1(A_2, B_3))=k8_relat_1(B_14, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_14) | ~v1_relat_1(k2_zfmisc_1(A_2, B_3)))), inference(superposition, [status(thm), theory('equality')], [c_17, c_25])).
% 1.61/1.11  tff(c_44, plain, (![B_14]: (k8_relat_1(B_14, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_17, c_40])).
% 1.61/1.11  tff(c_10, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.11  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 1.61/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  Inference rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Ref     : 0
% 1.61/1.11  #Sup     : 8
% 1.61/1.11  #Fact    : 0
% 1.61/1.11  #Define  : 0
% 1.61/1.11  #Split   : 0
% 1.61/1.11  #Chain   : 0
% 1.61/1.11  #Close   : 0
% 1.61/1.11  
% 1.61/1.11  Ordering : KBO
% 1.61/1.11  
% 1.61/1.11  Simplification rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Subsume      : 0
% 1.61/1.11  #Demod        : 4
% 1.61/1.11  #Tautology    : 4
% 1.61/1.11  #SimpNegUnit  : 0
% 1.61/1.11  #BackRed      : 1
% 1.61/1.11  
% 1.61/1.11  #Partial instantiations: 0
% 1.61/1.11  #Strategies tried      : 1
% 1.61/1.11  
% 1.61/1.11  Timing (in seconds)
% 1.61/1.11  ----------------------
% 1.61/1.11  Preprocessing        : 0.25
% 1.61/1.11  Parsing              : 0.14
% 1.61/1.11  CNF conversion       : 0.01
% 1.61/1.11  Main loop            : 0.09
% 1.61/1.11  Inferencing          : 0.05
% 1.61/1.11  Reduction            : 0.02
% 1.61/1.11  Demodulation         : 0.02
% 1.61/1.11  BG Simplification    : 0.01
% 1.61/1.11  Subsumption          : 0.01
% 1.61/1.11  Abstraction          : 0.00
% 1.61/1.11  MUC search           : 0.00
% 1.61/1.11  Cooper               : 0.00
% 1.61/1.11  Total                : 0.36
% 1.61/1.11  Index Insertion      : 0.00
% 1.61/1.11  Index Deletion       : 0.00
% 1.61/1.11  Index Matching       : 0.00
% 1.61/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
