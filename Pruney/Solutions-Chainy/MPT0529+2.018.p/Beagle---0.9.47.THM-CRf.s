%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  61 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k8_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = k8_relat_1(A_7,B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_34,B_35)),k2_relat_1(B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_132,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_7,B_8)),k2_relat_1(k6_relat_1(A_7)))
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_143,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_36,B_37)),A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_132])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_43,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_2')
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( k8_relat_1(A_28,B_29) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [B_29] :
      ( k8_relat_1('#skF_2',B_29) = B_29
      | ~ v1_relat_1(B_29)
      | ~ r1_tarski(k2_relat_1(B_29),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_714,plain,(
    ! [B_79] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_79)) = k8_relat_1('#skF_1',B_79)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_143,c_76])).

tff(c_786,plain,(
    ! [B_82] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_82)) = k8_relat_1('#skF_1',B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_714])).

tff(c_18,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_813,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_18])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.48  
% 2.95/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.48  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.95/1.48  
% 2.95/1.48  %Foreground sorts:
% 2.95/1.48  
% 2.95/1.48  
% 2.95/1.48  %Background operators:
% 2.95/1.48  
% 2.95/1.48  
% 2.95/1.48  %Foreground operators:
% 2.95/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.95/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.48  
% 2.95/1.49  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.95/1.49  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.95/1.49  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.95/1.49  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.95/1.49  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.95/1.49  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.95/1.49  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.95/1.49  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.95/1.49  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.49  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k8_relat_1(A_5, B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.49  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.49  tff(c_16, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.95/1.49  tff(c_8, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=k8_relat_1(A_7, B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.49  tff(c_122, plain, (![A_34, B_35]: (r1_tarski(k2_relat_1(k5_relat_1(A_34, B_35)), k2_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.95/1.49  tff(c_132, plain, (![A_7, B_8]: (r1_tarski(k2_relat_1(k8_relat_1(A_7, B_8)), k2_relat_1(k6_relat_1(A_7))) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(B_8) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_122])).
% 2.95/1.49  tff(c_143, plain, (![A_36, B_37]: (r1_tarski(k2_relat_1(k8_relat_1(A_36, B_37)), A_36) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_132])).
% 2.95/1.49  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.49  tff(c_43, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.49  tff(c_46, plain, (![A_20]: (r1_tarski(A_20, '#skF_2') | ~r1_tarski(A_20, '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.95/1.49  tff(c_68, plain, (![A_28, B_29]: (k8_relat_1(A_28, B_29)=B_29 | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.95/1.49  tff(c_76, plain, (![B_29]: (k8_relat_1('#skF_2', B_29)=B_29 | ~v1_relat_1(B_29) | ~r1_tarski(k2_relat_1(B_29), '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_68])).
% 2.95/1.49  tff(c_714, plain, (![B_79]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_79))=k8_relat_1('#skF_1', B_79) | ~v1_relat_1(k8_relat_1('#skF_1', B_79)) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_143, c_76])).
% 2.95/1.49  tff(c_786, plain, (![B_82]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_82))=k8_relat_1('#skF_1', B_82) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_6, c_714])).
% 2.95/1.49  tff(c_18, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.49  tff(c_813, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_786, c_18])).
% 2.95/1.49  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_813])).
% 2.95/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.49  
% 2.95/1.49  Inference rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Ref     : 0
% 2.95/1.49  #Sup     : 192
% 2.95/1.49  #Fact    : 0
% 2.95/1.49  #Define  : 0
% 2.95/1.49  #Split   : 0
% 2.95/1.49  #Chain   : 0
% 2.95/1.49  #Close   : 0
% 2.95/1.49  
% 2.95/1.49  Ordering : KBO
% 2.95/1.49  
% 2.95/1.49  Simplification rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Subsume      : 37
% 2.95/1.49  #Demod        : 58
% 2.95/1.49  #Tautology    : 46
% 2.95/1.49  #SimpNegUnit  : 0
% 2.95/1.49  #BackRed      : 0
% 2.95/1.49  
% 2.95/1.49  #Partial instantiations: 0
% 2.95/1.49  #Strategies tried      : 1
% 2.95/1.49  
% 2.95/1.49  Timing (in seconds)
% 2.95/1.49  ----------------------
% 3.10/1.50  Preprocessing        : 0.28
% 3.10/1.50  Parsing              : 0.16
% 3.10/1.50  CNF conversion       : 0.02
% 3.10/1.50  Main loop            : 0.42
% 3.10/1.50  Inferencing          : 0.17
% 3.10/1.50  Reduction            : 0.11
% 3.10/1.50  Demodulation         : 0.08
% 3.10/1.50  BG Simplification    : 0.02
% 3.10/1.50  Subsumption          : 0.09
% 3.10/1.50  Abstraction          : 0.02
% 3.10/1.50  MUC search           : 0.00
% 3.10/1.50  Cooper               : 0.00
% 3.10/1.50  Total                : 0.73
% 3.10/1.50  Index Insertion      : 0.00
% 3.10/1.50  Index Deletion       : 0.00
% 3.10/1.50  Index Matching       : 0.00
% 3.10/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
