%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:30 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [A_15,B_16] :
      ( k8_relat_1(A_15,B_16) = B_16
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_15] :
      ( k8_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_72,plain,(
    ! [A_15] : k8_relat_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_2,c_70])).

tff(c_18,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:47:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.12  
% 1.57/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.12  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.57/1.12  
% 1.57/1.12  %Foreground sorts:
% 1.57/1.12  
% 1.57/1.12  
% 1.57/1.12  %Background operators:
% 1.57/1.12  
% 1.57/1.12  
% 1.57/1.12  %Foreground operators:
% 1.57/1.12  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.57/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.57/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.57/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.12  
% 1.57/1.13  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.57/1.13  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.57/1.13  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.57/1.13  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.57/1.13  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.57/1.13  tff(f_47, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.57/1.13  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.13  tff(c_35, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.57/1.13  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 1.57/1.13  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.57/1.13  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.13  tff(c_67, plain, (![A_15, B_16]: (k8_relat_1(A_15, B_16)=B_16 | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.57/1.13  tff(c_70, plain, (![A_15]: (k8_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_15) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 1.57/1.13  tff(c_72, plain, (![A_15]: (k8_relat_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_2, c_70])).
% 1.57/1.13  tff(c_18, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.57/1.13  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_18])).
% 1.57/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.13  
% 1.57/1.13  Inference rules
% 1.57/1.13  ----------------------
% 1.57/1.13  #Ref     : 0
% 1.57/1.13  #Sup     : 15
% 1.57/1.13  #Fact    : 0
% 1.57/1.13  #Define  : 0
% 1.57/1.13  #Split   : 0
% 1.57/1.13  #Chain   : 0
% 1.57/1.13  #Close   : 0
% 1.57/1.13  
% 1.57/1.13  Ordering : KBO
% 1.57/1.13  
% 1.57/1.13  Simplification rules
% 1.57/1.13  ----------------------
% 1.57/1.13  #Subsume      : 0
% 1.57/1.13  #Demod        : 4
% 1.57/1.13  #Tautology    : 13
% 1.57/1.13  #SimpNegUnit  : 0
% 1.57/1.13  #BackRed      : 1
% 1.57/1.13  
% 1.57/1.13  #Partial instantiations: 0
% 1.57/1.13  #Strategies tried      : 1
% 1.57/1.13  
% 1.57/1.13  Timing (in seconds)
% 1.57/1.13  ----------------------
% 1.57/1.13  Preprocessing        : 0.25
% 1.57/1.13  Parsing              : 0.14
% 1.57/1.13  CNF conversion       : 0.01
% 1.57/1.13  Main loop            : 0.09
% 1.57/1.13  Inferencing          : 0.03
% 1.57/1.13  Reduction            : 0.02
% 1.57/1.13  Demodulation         : 0.02
% 1.57/1.13  BG Simplification    : 0.01
% 1.57/1.13  Subsumption          : 0.01
% 1.57/1.13  Abstraction          : 0.00
% 1.57/1.13  MUC search           : 0.00
% 1.57/1.13  Cooper               : 0.00
% 1.57/1.13  Total                : 0.36
% 1.57/1.13  Index Insertion      : 0.00
% 1.57/1.13  Index Deletion       : 0.00
% 1.57/1.13  Index Matching       : 0.00
% 1.57/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
