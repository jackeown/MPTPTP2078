%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:52 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  52 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_30])).

tff(c_93,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_93])).

tff(c_169,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_169])).

tff(c_206,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_196])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_199,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_169])).

tff(c_207,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_199])).

tff(c_449,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_207])).

tff(c_403,plain,(
    ! [C_38,A_39,B_40] :
      ( k2_xboole_0(k10_relat_1(C_38,A_39),k10_relat_1(C_38,B_40)) = k10_relat_1(C_38,k2_xboole_0(A_39,B_40))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_544,plain,(
    ! [C_43,A_44,B_45] :
      ( r1_tarski(k10_relat_1(C_43,A_44),k10_relat_1(C_43,k2_xboole_0(A_44,B_45)))
      | ~ v1_relat_1(C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_12])).

tff(c_670,plain,(
    ! [C_48] :
      ( r1_tarski(k10_relat_1(C_48,'#skF_1'),k10_relat_1(C_48,'#skF_2'))
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_544])).

tff(c_16,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_676,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_670,c_16])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.28  
% 2.29/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.28  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.28  
% 2.29/1.28  %Foreground sorts:
% 2.29/1.28  
% 2.29/1.28  
% 2.29/1.28  %Background operators:
% 2.29/1.28  
% 2.29/1.28  
% 2.29/1.28  %Foreground operators:
% 2.29/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.29/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.28  
% 2.29/1.29  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.29/1.29  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.29/1.29  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.29/1.29  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.29/1.29  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.29/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.29/1.29  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.29/1.29  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.29  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.29  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.29  tff(c_33, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_30])).
% 2.29/1.29  tff(c_93, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.29  tff(c_111, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_93])).
% 2.29/1.29  tff(c_169, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.29  tff(c_196, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_111, c_169])).
% 2.29/1.29  tff(c_206, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_196])).
% 2.29/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.29  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.29  tff(c_113, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_93])).
% 2.29/1.29  tff(c_199, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113, c_169])).
% 2.29/1.29  tff(c_207, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_199])).
% 2.29/1.29  tff(c_449, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_207])).
% 2.29/1.29  tff(c_403, plain, (![C_38, A_39, B_40]: (k2_xboole_0(k10_relat_1(C_38, A_39), k10_relat_1(C_38, B_40))=k10_relat_1(C_38, k2_xboole_0(A_39, B_40)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.29  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.29  tff(c_544, plain, (![C_43, A_44, B_45]: (r1_tarski(k10_relat_1(C_43, A_44), k10_relat_1(C_43, k2_xboole_0(A_44, B_45))) | ~v1_relat_1(C_43))), inference(superposition, [status(thm), theory('equality')], [c_403, c_12])).
% 2.29/1.29  tff(c_670, plain, (![C_48]: (r1_tarski(k10_relat_1(C_48, '#skF_1'), k10_relat_1(C_48, '#skF_2')) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_449, c_544])).
% 2.29/1.29  tff(c_16, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.29  tff(c_676, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_670, c_16])).
% 2.29/1.29  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_676])).
% 2.29/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  Inference rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Ref     : 0
% 2.29/1.29  #Sup     : 167
% 2.29/1.29  #Fact    : 0
% 2.29/1.29  #Define  : 0
% 2.29/1.29  #Split   : 0
% 2.29/1.29  #Chain   : 0
% 2.29/1.29  #Close   : 0
% 2.29/1.29  
% 2.29/1.29  Ordering : KBO
% 2.29/1.29  
% 2.29/1.29  Simplification rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Subsume      : 1
% 2.29/1.29  #Demod        : 92
% 2.29/1.29  #Tautology    : 122
% 2.29/1.29  #SimpNegUnit  : 0
% 2.29/1.29  #BackRed      : 0
% 2.29/1.29  
% 2.29/1.29  #Partial instantiations: 0
% 2.29/1.29  #Strategies tried      : 1
% 2.29/1.29  
% 2.29/1.29  Timing (in seconds)
% 2.29/1.29  ----------------------
% 2.29/1.29  Preprocessing        : 0.26
% 2.29/1.29  Parsing              : 0.15
% 2.29/1.29  CNF conversion       : 0.02
% 2.29/1.29  Main loop            : 0.26
% 2.29/1.29  Inferencing          : 0.10
% 2.29/1.29  Reduction            : 0.10
% 2.29/1.29  Demodulation         : 0.08
% 2.29/1.29  BG Simplification    : 0.01
% 2.29/1.29  Subsumption          : 0.04
% 2.29/1.29  Abstraction          : 0.01
% 2.29/1.29  MUC search           : 0.00
% 2.29/1.29  Cooper               : 0.00
% 2.29/1.29  Total                : 0.55
% 2.29/1.29  Index Insertion      : 0.00
% 2.29/1.29  Index Deletion       : 0.00
% 2.29/1.29  Index Matching       : 0.00
% 2.29/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
