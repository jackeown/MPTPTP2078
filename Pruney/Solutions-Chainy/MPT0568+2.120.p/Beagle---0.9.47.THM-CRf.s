%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:36 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_72])).

tff(c_85,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20,c_81])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_101,plain,(
    ! [B_22,A_23] :
      ( k10_relat_1(B_22,k3_xboole_0(k2_relat_1(B_22),A_23)) = k10_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_110,plain,(
    ! [A_23] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_23)) = k10_relat_1(k1_xboole_0,A_23)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_114,plain,(
    ! [A_23] : k10_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_85,c_64,c_110])).

tff(c_22,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:02:08 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.12  
% 1.73/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.12  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.73/1.12  
% 1.73/1.12  %Foreground sorts:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Background operators:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Foreground operators:
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.73/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.12  
% 1.73/1.13  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.73/1.13  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.73/1.13  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.73/1.13  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.73/1.13  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.73/1.13  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.73/1.13  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 1.73/1.13  tff(f_53, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.73/1.13  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.13  tff(c_54, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.13  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_54])).
% 1.73/1.13  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.13  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.13  tff(c_72, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.73/1.13  tff(c_81, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_72])).
% 1.73/1.13  tff(c_85, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20, c_81])).
% 1.73/1.13  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.13  tff(c_60, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.13  tff(c_64, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_60])).
% 1.73/1.13  tff(c_101, plain, (![B_22, A_23]: (k10_relat_1(B_22, k3_xboole_0(k2_relat_1(B_22), A_23))=k10_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.73/1.13  tff(c_110, plain, (![A_23]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_23))=k10_relat_1(k1_xboole_0, A_23) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_101])).
% 1.73/1.13  tff(c_114, plain, (![A_23]: (k10_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_85, c_64, c_110])).
% 1.73/1.13  tff(c_22, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.73/1.13  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_22])).
% 1.73/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.13  
% 1.73/1.13  Inference rules
% 1.73/1.13  ----------------------
% 1.73/1.13  #Ref     : 0
% 1.73/1.13  #Sup     : 25
% 1.73/1.13  #Fact    : 0
% 1.73/1.13  #Define  : 0
% 1.73/1.13  #Split   : 0
% 1.73/1.13  #Chain   : 0
% 1.73/1.13  #Close   : 0
% 1.73/1.13  
% 1.73/1.13  Ordering : KBO
% 1.73/1.13  
% 1.73/1.13  Simplification rules
% 1.73/1.13  ----------------------
% 1.73/1.13  #Subsume      : 0
% 1.73/1.13  #Demod        : 8
% 1.73/1.13  #Tautology    : 22
% 1.73/1.13  #SimpNegUnit  : 0
% 1.73/1.13  #BackRed      : 1
% 1.73/1.13  
% 1.73/1.13  #Partial instantiations: 0
% 1.73/1.13  #Strategies tried      : 1
% 1.73/1.13  
% 1.73/1.13  Timing (in seconds)
% 1.73/1.13  ----------------------
% 1.73/1.14  Preprocessing        : 0.27
% 1.73/1.14  Parsing              : 0.16
% 1.73/1.14  CNF conversion       : 0.02
% 1.73/1.14  Main loop            : 0.11
% 1.73/1.14  Inferencing          : 0.05
% 1.73/1.14  Reduction            : 0.03
% 1.73/1.14  Demodulation         : 0.02
% 1.73/1.14  BG Simplification    : 0.01
% 1.73/1.14  Subsumption          : 0.01
% 1.73/1.14  Abstraction          : 0.00
% 1.73/1.14  MUC search           : 0.00
% 1.73/1.14  Cooper               : 0.00
% 1.73/1.14  Total                : 0.40
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
