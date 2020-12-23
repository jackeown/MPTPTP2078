%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  62 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_6,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [B_32,A_33] :
      ( k7_relat_1(B_32,k3_xboole_0(k1_relat_1(B_32),A_33)) = k7_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = k8_relat_1(A_6,B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_6,A_24] :
      ( k8_relat_1(A_6,k6_relat_1(A_24)) = k7_relat_1(k6_relat_1(A_6),A_24)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_92,plain,(
    ! [A_6,A_24] : k8_relat_1(A_6,k6_relat_1(A_24)) = k7_relat_1(k6_relat_1(A_6),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_80])).

tff(c_16,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_107,plain,(
    ! [A_28,B_29] :
      ( k8_relat_1(A_28,B_29) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [A_28,A_12] :
      ( k8_relat_1(A_28,k6_relat_1(A_12)) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_28)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_107])).

tff(c_112,plain,(
    ! [A_28,A_12] :
      ( k7_relat_1(k6_relat_1(A_28),A_12) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92,c_110])).

tff(c_133,plain,(
    ! [A_28,A_33] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_28)),A_33)) = k7_relat_1(k6_relat_1(A_28),A_33)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_28)),A_33),A_28)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_112])).

tff(c_146,plain,(
    ! [A_28,A_33] : k7_relat_1(k6_relat_1(A_28),A_33) = k6_relat_1(k3_xboole_0(A_28,A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2,c_14,c_14,c_133])).

tff(c_20,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_20])).

tff(c_90,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:05:27 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.66/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.15  
% 1.66/1.16  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.66/1.16  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.66/1.16  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.66/1.16  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 1.66/1.16  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.66/1.16  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.66/1.16  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.66/1.16  tff(f_56, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.66/1.16  tff(c_6, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.16  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.16  tff(c_14, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.66/1.16  tff(c_126, plain, (![B_32, A_33]: (k7_relat_1(B_32, k3_xboole_0(k1_relat_1(B_32), A_33))=k7_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.16  tff(c_70, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.16  tff(c_8, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=k8_relat_1(A_6, B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.16  tff(c_80, plain, (![A_6, A_24]: (k8_relat_1(A_6, k6_relat_1(A_24))=k7_relat_1(k6_relat_1(A_6), A_24) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 1.66/1.16  tff(c_92, plain, (![A_6, A_24]: (k8_relat_1(A_6, k6_relat_1(A_24))=k7_relat_1(k6_relat_1(A_6), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_80])).
% 1.66/1.16  tff(c_16, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.66/1.16  tff(c_107, plain, (![A_28, B_29]: (k8_relat_1(A_28, B_29)=B_29 | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.66/1.16  tff(c_110, plain, (![A_28, A_12]: (k8_relat_1(A_28, k6_relat_1(A_12))=k6_relat_1(A_12) | ~r1_tarski(A_12, A_28) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_107])).
% 1.66/1.16  tff(c_112, plain, (![A_28, A_12]: (k7_relat_1(k6_relat_1(A_28), A_12)=k6_relat_1(A_12) | ~r1_tarski(A_12, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92, c_110])).
% 1.66/1.16  tff(c_133, plain, (![A_28, A_33]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_28)), A_33))=k7_relat_1(k6_relat_1(A_28), A_33) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_28)), A_33), A_28) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_112])).
% 1.66/1.16  tff(c_146, plain, (![A_28, A_33]: (k7_relat_1(k6_relat_1(A_28), A_33)=k6_relat_1(k3_xboole_0(A_28, A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2, c_14, c_14, c_133])).
% 1.66/1.16  tff(c_20, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.66/1.16  tff(c_76, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_20])).
% 1.66/1.16  tff(c_90, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_76])).
% 1.66/1.16  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_90])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 27
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 1
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 1
% 1.66/1.16  #Demod        : 22
% 1.66/1.16  #Tautology    : 17
% 1.66/1.16  #SimpNegUnit  : 0
% 1.66/1.16  #BackRed      : 4
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.16  Preprocessing        : 0.27
% 1.66/1.16  Parsing              : 0.15
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.13
% 1.66/1.16  Inferencing          : 0.06
% 1.66/1.16  Reduction            : 0.04
% 1.66/1.16  Demodulation         : 0.03
% 1.66/1.16  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.02
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.43
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.66/1.17  Index Matching       : 0.00
% 1.66/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
