%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  66 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(k2_xboole_0(A_42,C_43),B_44)
      | ~ r1_tarski(C_43,B_44)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(A_16,C_17)
      | ~ r1_tarski(k2_xboole_0(A_16,B_18),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(k2_xboole_0(A_21,B_22),A_21) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_122,plain,(
    ! [B_44,C_43] :
      ( k2_xboole_0(B_44,C_43) = B_44
      | ~ r1_tarski(C_43,B_44)
      | ~ r1_tarski(B_44,B_44) ) ),
    inference(resolution,[status(thm)],[c_116,c_46])).

tff(c_134,plain,(
    ! [B_45,C_46] :
      ( k2_xboole_0(B_45,C_46) = B_45
      | ~ r1_tarski(C_46,B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_122])).

tff(c_166,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_446,plain,(
    ! [C_58,A_59,B_60] :
      ( k2_xboole_0(k10_relat_1(C_58,A_59),k10_relat_1(C_58,B_60)) = k10_relat_1(C_58,k2_xboole_0(A_59,B_60))
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1366,plain,(
    ! [A_97,C_98,A_99,B_100] :
      ( r1_tarski(A_97,k10_relat_1(C_98,k2_xboole_0(A_99,B_100)))
      | ~ r1_tarski(A_97,k10_relat_1(C_98,B_100))
      | ~ v1_relat_1(C_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_8])).

tff(c_1624,plain,(
    ! [A_106,C_107] :
      ( r1_tarski(A_106,k10_relat_1(C_107,'#skF_2'))
      | ~ r1_tarski(A_106,k10_relat_1(C_107,'#skF_1'))
      | ~ v1_relat_1(C_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_1366])).

tff(c_16,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1650,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1624,c_16])).

tff(c_1661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_1650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.55  
% 3.21/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.55  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.21/1.55  
% 3.21/1.55  %Foreground sorts:
% 3.21/1.55  
% 3.21/1.55  
% 3.21/1.55  %Background operators:
% 3.21/1.55  
% 3.21/1.55  
% 3.21/1.55  %Foreground operators:
% 3.21/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.21/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.55  
% 3.21/1.56  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 3.21/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.56  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.21/1.56  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.21/1.56  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 3.21/1.56  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.21/1.56  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.56  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.56  tff(c_116, plain, (![A_42, C_43, B_44]: (r1_tarski(k2_xboole_0(A_42, C_43), B_44) | ~r1_tarski(C_43, B_44) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.56  tff(c_23, plain, (![A_16, C_17, B_18]: (r1_tarski(A_16, C_17) | ~r1_tarski(k2_xboole_0(A_16, B_18), C_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.56  tff(c_39, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_6, c_23])).
% 3.21/1.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.56  tff(c_46, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(k2_xboole_0(A_21, B_22), A_21))), inference(resolution, [status(thm)], [c_39, c_2])).
% 3.21/1.56  tff(c_122, plain, (![B_44, C_43]: (k2_xboole_0(B_44, C_43)=B_44 | ~r1_tarski(C_43, B_44) | ~r1_tarski(B_44, B_44))), inference(resolution, [status(thm)], [c_116, c_46])).
% 3.21/1.56  tff(c_134, plain, (![B_45, C_46]: (k2_xboole_0(B_45, C_46)=B_45 | ~r1_tarski(C_46, B_45))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_122])).
% 3.21/1.56  tff(c_166, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_134])).
% 3.21/1.56  tff(c_446, plain, (![C_58, A_59, B_60]: (k2_xboole_0(k10_relat_1(C_58, A_59), k10_relat_1(C_58, B_60))=k10_relat_1(C_58, k2_xboole_0(A_59, B_60)) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.56  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.56  tff(c_1366, plain, (![A_97, C_98, A_99, B_100]: (r1_tarski(A_97, k10_relat_1(C_98, k2_xboole_0(A_99, B_100))) | ~r1_tarski(A_97, k10_relat_1(C_98, B_100)) | ~v1_relat_1(C_98))), inference(superposition, [status(thm), theory('equality')], [c_446, c_8])).
% 3.21/1.56  tff(c_1624, plain, (![A_106, C_107]: (r1_tarski(A_106, k10_relat_1(C_107, '#skF_2')) | ~r1_tarski(A_106, k10_relat_1(C_107, '#skF_1')) | ~v1_relat_1(C_107))), inference(superposition, [status(thm), theory('equality')], [c_166, c_1366])).
% 3.21/1.56  tff(c_16, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.56  tff(c_1650, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1624, c_16])).
% 3.21/1.56  tff(c_1661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_1650])).
% 3.21/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.56  
% 3.21/1.56  Inference rules
% 3.21/1.56  ----------------------
% 3.21/1.56  #Ref     : 0
% 3.21/1.56  #Sup     : 394
% 3.21/1.56  #Fact    : 0
% 3.21/1.56  #Define  : 0
% 3.21/1.56  #Split   : 1
% 3.21/1.56  #Chain   : 0
% 3.21/1.56  #Close   : 0
% 3.21/1.56  
% 3.21/1.56  Ordering : KBO
% 3.21/1.56  
% 3.21/1.56  Simplification rules
% 3.21/1.56  ----------------------
% 3.21/1.56  #Subsume      : 27
% 3.21/1.56  #Demod        : 209
% 3.21/1.56  #Tautology    : 202
% 3.21/1.56  #SimpNegUnit  : 0
% 3.21/1.56  #BackRed      : 0
% 3.21/1.56  
% 3.21/1.56  #Partial instantiations: 0
% 3.21/1.56  #Strategies tried      : 1
% 3.21/1.56  
% 3.21/1.56  Timing (in seconds)
% 3.21/1.56  ----------------------
% 3.21/1.56  Preprocessing        : 0.29
% 3.21/1.56  Parsing              : 0.16
% 3.21/1.56  CNF conversion       : 0.02
% 3.21/1.56  Main loop            : 0.46
% 3.21/1.56  Inferencing          : 0.17
% 3.21/1.56  Reduction            : 0.14
% 3.21/1.56  Demodulation         : 0.11
% 3.21/1.56  BG Simplification    : 0.02
% 3.21/1.56  Subsumption          : 0.10
% 3.21/1.56  Abstraction          : 0.03
% 3.21/1.56  MUC search           : 0.00
% 3.21/1.57  Cooper               : 0.00
% 3.21/1.57  Total                : 0.77
% 3.21/1.57  Index Insertion      : 0.00
% 3.21/1.57  Index Deletion       : 0.00
% 3.21/1.57  Index Matching       : 0.00
% 3.21/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
