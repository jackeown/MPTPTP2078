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
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   13 (  13 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_150,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_150])).

tff(c_276,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_313,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_276])).

tff(c_327,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_313])).

tff(c_329,plain,(
    ! [C_35,A_36,B_37] :
      ( k2_xboole_0(k10_relat_1(C_35,A_36),k10_relat_1(C_35,B_37)) = k10_relat_1(C_35,k2_xboole_0(A_36,B_37))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_633,plain,(
    ! [C_44,A_45,B_46] :
      ( r1_tarski(k10_relat_1(C_44,A_45),k10_relat_1(C_44,k2_xboole_0(A_45,B_46)))
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_12])).

tff(c_775,plain,(
    ! [C_49] :
      ( r1_tarski(k10_relat_1(C_49,'#skF_1'),k10_relat_1(C_49,'#skF_2'))
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_633])).

tff(c_16,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_781,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_775,c_16])).

tff(c_786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.73  
% 2.85/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.74  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.85/1.74  
% 2.85/1.74  %Foreground sorts:
% 2.85/1.74  
% 2.85/1.74  
% 2.85/1.74  %Background operators:
% 2.85/1.74  
% 2.85/1.74  
% 2.85/1.74  %Foreground operators:
% 2.85/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.85/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.74  
% 2.85/1.75  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.85/1.75  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.85/1.75  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.85/1.75  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.85/1.75  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.85/1.75  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.85/1.75  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.85/1.75  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.85/1.75  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.75  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.75  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.85/1.75  tff(c_150, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.75  tff(c_170, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_150])).
% 2.85/1.75  tff(c_276, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.75  tff(c_313, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_170, c_276])).
% 2.85/1.75  tff(c_327, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_313])).
% 2.85/1.75  tff(c_329, plain, (![C_35, A_36, B_37]: (k2_xboole_0(k10_relat_1(C_35, A_36), k10_relat_1(C_35, B_37))=k10_relat_1(C_35, k2_xboole_0(A_36, B_37)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.75  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.75  tff(c_633, plain, (![C_44, A_45, B_46]: (r1_tarski(k10_relat_1(C_44, A_45), k10_relat_1(C_44, k2_xboole_0(A_45, B_46))) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_329, c_12])).
% 2.85/1.75  tff(c_775, plain, (![C_49]: (r1_tarski(k10_relat_1(C_49, '#skF_1'), k10_relat_1(C_49, '#skF_2')) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_327, c_633])).
% 2.85/1.75  tff(c_16, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.85/1.75  tff(c_781, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_775, c_16])).
% 2.85/1.75  tff(c_786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_781])).
% 2.85/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.75  
% 2.85/1.75  Inference rules
% 2.85/1.75  ----------------------
% 2.85/1.75  #Ref     : 0
% 2.85/1.75  #Sup     : 194
% 2.85/1.75  #Fact    : 0
% 2.85/1.75  #Define  : 0
% 2.85/1.75  #Split   : 0
% 2.85/1.75  #Chain   : 0
% 2.85/1.75  #Close   : 0
% 2.85/1.75  
% 2.85/1.75  Ordering : KBO
% 2.85/1.75  
% 2.85/1.75  Simplification rules
% 2.85/1.75  ----------------------
% 2.85/1.75  #Subsume      : 1
% 2.85/1.75  #Demod        : 120
% 2.85/1.75  #Tautology    : 137
% 2.85/1.75  #SimpNegUnit  : 0
% 2.85/1.75  #BackRed      : 0
% 2.85/1.75  
% 2.85/1.75  #Partial instantiations: 0
% 2.85/1.75  #Strategies tried      : 1
% 2.85/1.75  
% 2.85/1.75  Timing (in seconds)
% 2.85/1.75  ----------------------
% 2.85/1.76  Preprocessing        : 0.40
% 2.85/1.76  Parsing              : 0.22
% 2.85/1.76  CNF conversion       : 0.03
% 2.85/1.76  Main loop            : 0.47
% 2.85/1.76  Inferencing          : 0.18
% 2.85/1.76  Reduction            : 0.17
% 2.85/1.76  Demodulation         : 0.14
% 2.85/1.76  BG Simplification    : 0.02
% 2.85/1.76  Subsumption          : 0.07
% 2.85/1.76  Abstraction          : 0.02
% 2.85/1.76  MUC search           : 0.00
% 2.85/1.76  Cooper               : 0.00
% 2.85/1.76  Total                : 0.91
% 2.85/1.76  Index Insertion      : 0.00
% 2.85/1.76  Index Deletion       : 0.00
% 2.85/1.76  Index Matching       : 0.00
% 2.85/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
