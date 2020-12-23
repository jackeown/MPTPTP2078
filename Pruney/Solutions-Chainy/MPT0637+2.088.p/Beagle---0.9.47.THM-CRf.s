%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  57 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_8,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [B_32,A_33] :
      ( k7_relat_1(B_32,k3_xboole_0(k1_relat_1(B_32),A_33)) = k7_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [B_26,A_27] :
      ( k5_relat_1(B_26,k6_relat_1(A_27)) = B_26
      | ~ r1_tarski(k2_relat_1(B_26),A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_10,A_27] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_27)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_27)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_73])).

tff(c_79,plain,(
    ! [A_28,A_29] :
      ( k5_relat_1(k6_relat_1(A_28),k6_relat_1(A_29)) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_95,plain,(
    ! [A_29,A_13] :
      ( k7_relat_1(k6_relat_1(A_29),A_13) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_29)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_79])).

tff(c_101,plain,(
    ! [A_29,A_13] :
      ( k7_relat_1(k6_relat_1(A_29),A_13) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_122,plain,(
    ! [A_29,A_33] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)),A_33)) = k7_relat_1(k6_relat_1(A_29),A_33)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)),A_33),A_29)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_101])).

tff(c_135,plain,(
    ! [A_29,A_33] : k7_relat_1(k6_relat_1(A_29),A_33) = k6_relat_1(k3_xboole_0(A_29,A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_12,c_12,c_122])).

tff(c_20,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_72,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.89/1.20  
% 1.89/1.20  %Foreground sorts:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Background operators:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Foreground operators:
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.89/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.89/1.20  
% 1.89/1.21  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.89/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.89/1.21  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.89/1.21  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 1.89/1.21  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.89/1.21  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.89/1.21  tff(f_54, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.89/1.21  tff(c_8, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.21  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.21  tff(c_115, plain, (![B_32, A_33]: (k7_relat_1(B_32, k3_xboole_0(k1_relat_1(B_32), A_33))=k7_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.21  tff(c_18, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.21  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.21  tff(c_73, plain, (![B_26, A_27]: (k5_relat_1(B_26, k6_relat_1(A_27))=B_26 | ~r1_tarski(k2_relat_1(B_26), A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.21  tff(c_76, plain, (![A_10, A_27]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_27))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_27) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_73])).
% 1.89/1.21  tff(c_79, plain, (![A_28, A_29]: (k5_relat_1(k6_relat_1(A_28), k6_relat_1(A_29))=k6_relat_1(A_28) | ~r1_tarski(A_28, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_76])).
% 1.89/1.21  tff(c_95, plain, (![A_29, A_13]: (k7_relat_1(k6_relat_1(A_29), A_13)=k6_relat_1(A_13) | ~r1_tarski(A_13, A_29) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_79])).
% 1.89/1.21  tff(c_101, plain, (![A_29, A_13]: (k7_relat_1(k6_relat_1(A_29), A_13)=k6_relat_1(A_13) | ~r1_tarski(A_13, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 1.89/1.21  tff(c_122, plain, (![A_29, A_33]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)), A_33))=k7_relat_1(k6_relat_1(A_29), A_33) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_29)), A_33), A_29) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_101])).
% 1.89/1.21  tff(c_135, plain, (![A_29, A_33]: (k7_relat_1(k6_relat_1(A_29), A_33)=k6_relat_1(k3_xboole_0(A_29, A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_12, c_12, c_122])).
% 1.89/1.21  tff(c_20, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.89/1.21  tff(c_70, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_20])).
% 1.89/1.21  tff(c_72, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_70])).
% 1.89/1.21  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_72])).
% 1.89/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  Inference rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Ref     : 0
% 1.89/1.21  #Sup     : 25
% 1.89/1.21  #Fact    : 0
% 1.89/1.21  #Define  : 0
% 1.89/1.21  #Split   : 1
% 1.89/1.21  #Chain   : 0
% 1.89/1.21  #Close   : 0
% 1.89/1.21  
% 1.89/1.21  Ordering : KBO
% 1.89/1.21  
% 1.89/1.21  Simplification rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Subsume      : 2
% 1.89/1.21  #Demod        : 15
% 1.89/1.21  #Tautology    : 16
% 1.89/1.21  #SimpNegUnit  : 0
% 1.89/1.21  #BackRed      : 2
% 1.89/1.21  
% 1.89/1.21  #Partial instantiations: 0
% 1.89/1.21  #Strategies tried      : 1
% 1.89/1.21  
% 1.89/1.21  Timing (in seconds)
% 1.89/1.21  ----------------------
% 1.89/1.21  Preprocessing        : 0.28
% 1.89/1.21  Parsing              : 0.15
% 1.89/1.21  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.12
% 1.89/1.21  Inferencing          : 0.05
% 1.89/1.21  Reduction            : 0.04
% 1.89/1.21  Demodulation         : 0.03
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.01
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.42
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
