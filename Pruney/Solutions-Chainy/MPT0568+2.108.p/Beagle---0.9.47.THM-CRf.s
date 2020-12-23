%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_28])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_47])).

tff(c_60,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14,c_56])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_65,plain,(
    ! [B_14,A_15] :
      ( k10_relat_1(B_14,k3_xboole_0(k2_relat_1(B_14),A_15)) = k10_relat_1(B_14,A_15)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_15] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_15)) = k10_relat_1(k1_xboole_0,A_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_65])).

tff(c_78,plain,(
    ! [A_15] : k10_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_60,c_39,c_74])).

tff(c_18,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.71/1.11  
% 1.71/1.11  %Foreground sorts:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Background operators:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Foreground operators:
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.71/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.11  
% 1.71/1.12  tff(f_45, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.71/1.12  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.71/1.12  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.12  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.71/1.12  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.71/1.12  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.71/1.12  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 1.71/1.12  tff(f_48, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.71/1.12  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.71/1.12  tff(c_28, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.12  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_28])).
% 1.71/1.12  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.12  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.12  tff(c_47, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.71/1.12  tff(c_56, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_47])).
% 1.71/1.12  tff(c_60, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14, c_56])).
% 1.71/1.12  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.12  tff(c_35, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.12  tff(c_39, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_35])).
% 1.71/1.12  tff(c_65, plain, (![B_14, A_15]: (k10_relat_1(B_14, k3_xboole_0(k2_relat_1(B_14), A_15))=k10_relat_1(B_14, A_15) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.12  tff(c_74, plain, (![A_15]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_15))=k10_relat_1(k1_xboole_0, A_15) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_65])).
% 1.71/1.12  tff(c_78, plain, (![A_15]: (k10_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_60, c_39, c_74])).
% 1.71/1.12  tff(c_18, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.71/1.12  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_18])).
% 1.71/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  Inference rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Ref     : 0
% 1.71/1.12  #Sup     : 18
% 1.71/1.12  #Fact    : 0
% 1.71/1.12  #Define  : 0
% 1.71/1.12  #Split   : 0
% 1.71/1.12  #Chain   : 0
% 1.71/1.12  #Close   : 0
% 1.71/1.12  
% 1.71/1.12  Ordering : KBO
% 1.71/1.12  
% 1.71/1.12  Simplification rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Subsume      : 0
% 1.71/1.12  #Demod        : 7
% 1.71/1.12  #Tautology    : 15
% 1.71/1.12  #SimpNegUnit  : 0
% 1.71/1.12  #BackRed      : 1
% 1.71/1.12  
% 1.71/1.12  #Partial instantiations: 0
% 1.71/1.12  #Strategies tried      : 1
% 1.71/1.12  
% 1.71/1.12  Timing (in seconds)
% 1.71/1.12  ----------------------
% 1.71/1.13  Preprocessing        : 0.26
% 1.71/1.13  Parsing              : 0.15
% 1.71/1.13  CNF conversion       : 0.01
% 1.71/1.13  Main loop            : 0.10
% 1.71/1.13  Inferencing          : 0.05
% 1.71/1.13  Reduction            : 0.03
% 1.71/1.13  Demodulation         : 0.02
% 1.71/1.13  BG Simplification    : 0.01
% 1.71/1.13  Subsumption          : 0.01
% 1.71/1.13  Abstraction          : 0.00
% 1.71/1.13  MUC search           : 0.00
% 1.71/1.13  Cooper               : 0.00
% 1.71/1.13  Total                : 0.39
% 1.71/1.13  Index Insertion      : 0.00
% 1.71/1.13  Index Deletion       : 0.00
% 1.71/1.13  Index Matching       : 0.00
% 1.71/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
