%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  57 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [B_28,A_29] :
      ( k5_relat_1(B_28,k6_relat_1(A_29)) = B_28
      | ~ r1_tarski(k2_relat_1(B_28),A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [A_10,A_29] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_29)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_29)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_119,plain,(
    ! [A_30,A_31] :
      ( k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_31)) = k6_relat_1(A_30)
      | ~ r1_tarski(A_30,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_116])).

tff(c_135,plain,(
    ! [A_31,A_13] :
      ( k7_relat_1(k6_relat_1(A_31),A_13) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_31)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_119])).

tff(c_165,plain,(
    ! [A_34,A_35] :
      ( k7_relat_1(k6_relat_1(A_34),A_35) = k6_relat_1(A_35)
      | ~ r1_tarski(A_35,A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_135])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,k3_xboole_0(k1_relat_1(B_9),A_8)) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    ! [A_34,A_8] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_34)),A_8)) = k7_relat_1(k6_relat_1(A_34),A_8)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_34)),A_8),A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_10])).

tff(c_185,plain,(
    ! [A_34,A_8] : k7_relat_1(k6_relat_1(A_34),A_8) = k6_relat_1(k3_xboole_0(A_34,A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12,c_8,c_12,c_172])).

tff(c_20,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_112,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.67/1.16  
% 1.67/1.16  %Foreground sorts:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Background operators:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Foreground operators:
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.67/1.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.67/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.67/1.16  
% 1.87/1.17  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.87/1.17  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.87/1.17  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.87/1.17  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.87/1.17  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.87/1.17  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.87/1.17  tff(f_54, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.87/1.17  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.17  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.17  tff(c_8, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.17  tff(c_18, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.17  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.17  tff(c_113, plain, (![B_28, A_29]: (k5_relat_1(B_28, k6_relat_1(A_29))=B_28 | ~r1_tarski(k2_relat_1(B_28), A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.17  tff(c_116, plain, (![A_10, A_29]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_29))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_29) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_113])).
% 1.87/1.17  tff(c_119, plain, (![A_30, A_31]: (k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_31))=k6_relat_1(A_30) | ~r1_tarski(A_30, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_116])).
% 1.87/1.17  tff(c_135, plain, (![A_31, A_13]: (k7_relat_1(k6_relat_1(A_31), A_13)=k6_relat_1(A_13) | ~r1_tarski(A_13, A_31) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_119])).
% 1.87/1.17  tff(c_165, plain, (![A_34, A_35]: (k7_relat_1(k6_relat_1(A_34), A_35)=k6_relat_1(A_35) | ~r1_tarski(A_35, A_34))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_135])).
% 1.87/1.17  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, k3_xboole_0(k1_relat_1(B_9), A_8))=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.17  tff(c_172, plain, (![A_34, A_8]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_34)), A_8))=k7_relat_1(k6_relat_1(A_34), A_8) | ~v1_relat_1(k6_relat_1(A_34)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_34)), A_8), A_34))), inference(superposition, [status(thm), theory('equality')], [c_165, c_10])).
% 1.87/1.17  tff(c_185, plain, (![A_34, A_8]: (k7_relat_1(k6_relat_1(A_34), A_8)=k6_relat_1(k3_xboole_0(A_34, A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12, c_8, c_12, c_172])).
% 1.87/1.17  tff(c_20, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.87/1.17  tff(c_110, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_20])).
% 1.87/1.17  tff(c_112, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_110])).
% 1.87/1.17  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_112])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 37
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 1
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 1
% 1.87/1.17  #Demod        : 18
% 1.87/1.17  #Tautology    : 25
% 1.87/1.17  #SimpNegUnit  : 0
% 1.87/1.17  #BackRed      : 2
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.18  Preprocessing        : 0.27
% 1.87/1.18  Parsing              : 0.16
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.15
% 1.87/1.18  Inferencing          : 0.05
% 1.87/1.18  Reduction            : 0.06
% 1.87/1.18  Demodulation         : 0.05
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
