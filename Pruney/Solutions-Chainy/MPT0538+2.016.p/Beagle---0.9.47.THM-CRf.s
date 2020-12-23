%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:24 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_14])).

tff(c_31,plain,(
    ! [B_12,A_13] :
      ( k3_xboole_0(B_12,k2_zfmisc_1(k1_relat_1(B_12),A_13)) = k8_relat_1(A_13,B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_19,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_19])).

tff(c_38,plain,(
    ! [A_13] :
      ( k8_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_23])).

tff(c_48,plain,(
    ! [A_13] : k8_relat_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.06  
% 1.57/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.06  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.57/1.06  
% 1.57/1.06  %Foreground sorts:
% 1.57/1.06  
% 1.57/1.06  
% 1.57/1.06  %Background operators:
% 1.57/1.06  
% 1.57/1.06  
% 1.57/1.06  %Foreground operators:
% 1.57/1.06  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.57/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.57/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.57/1.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.57/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.06  
% 1.57/1.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.57/1.07  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.57/1.07  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 1.57/1.07  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.57/1.07  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.57/1.07  tff(f_43, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.57/1.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.57/1.07  tff(c_14, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.57/1.07  tff(c_18, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_14])).
% 1.57/1.07  tff(c_31, plain, (![B_12, A_13]: (k3_xboole_0(B_12, k2_zfmisc_1(k1_relat_1(B_12), A_13))=k8_relat_1(A_13, B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.57/1.07  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.57/1.07  tff(c_19, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.57/1.07  tff(c_23, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_19])).
% 1.57/1.07  tff(c_38, plain, (![A_13]: (k8_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_31, c_23])).
% 1.57/1.07  tff(c_48, plain, (![A_13]: (k8_relat_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38])).
% 1.57/1.07  tff(c_12, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.57/1.07  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 1.57/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.07  
% 1.57/1.07  Inference rules
% 1.57/1.07  ----------------------
% 1.57/1.07  #Ref     : 0
% 1.57/1.07  #Sup     : 8
% 1.57/1.07  #Fact    : 0
% 1.57/1.07  #Define  : 0
% 1.57/1.07  #Split   : 0
% 1.57/1.07  #Chain   : 0
% 1.57/1.07  #Close   : 0
% 1.57/1.07  
% 1.57/1.07  Ordering : KBO
% 1.57/1.07  
% 1.57/1.07  Simplification rules
% 1.57/1.07  ----------------------
% 1.57/1.07  #Subsume      : 0
% 1.57/1.07  #Demod        : 3
% 1.57/1.07  #Tautology    : 4
% 1.57/1.07  #SimpNegUnit  : 0
% 1.57/1.07  #BackRed      : 1
% 1.57/1.07  
% 1.57/1.07  #Partial instantiations: 0
% 1.57/1.07  #Strategies tried      : 1
% 1.57/1.07  
% 1.57/1.07  Timing (in seconds)
% 1.57/1.07  ----------------------
% 1.57/1.07  Preprocessing        : 0.23
% 1.57/1.07  Parsing              : 0.13
% 1.57/1.07  CNF conversion       : 0.01
% 1.57/1.08  Main loop            : 0.08
% 1.57/1.08  Inferencing          : 0.04
% 1.57/1.08  Reduction            : 0.02
% 1.57/1.08  Demodulation         : 0.02
% 1.57/1.08  BG Simplification    : 0.01
% 1.57/1.08  Subsumption          : 0.01
% 1.57/1.08  Abstraction          : 0.00
% 1.57/1.08  MUC search           : 0.00
% 1.57/1.08  Cooper               : 0.00
% 1.57/1.08  Total                : 0.33
% 1.57/1.08  Index Insertion      : 0.00
% 1.57/1.08  Index Deletion       : 0.00
% 1.57/1.08  Index Matching       : 0.00
% 1.57/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
