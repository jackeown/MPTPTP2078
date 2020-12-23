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
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  49 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_279,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_300,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_279])).

tff(c_304,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_300])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_182,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_297,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_279])).

tff(c_303,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_297])).

tff(c_347,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_303])).

tff(c_305,plain,(
    ! [C_36,A_37,B_38] :
      ( k2_xboole_0(k10_relat_1(C_36,A_37),k10_relat_1(C_36,B_38)) = k10_relat_1(C_36,k2_xboole_0(A_37,B_38))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_776,plain,(
    ! [C_49,A_50,B_51] :
      ( r1_tarski(k10_relat_1(C_49,A_50),k10_relat_1(C_49,k2_xboole_0(A_50,B_51)))
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_12])).

tff(c_817,plain,(
    ! [C_52] :
      ( r1_tarski(k10_relat_1(C_52,'#skF_1'),k10_relat_1(C_52,'#skF_2'))
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_776])).

tff(c_18,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_823,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_817,c_18])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.34  %$ r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.34  
% 2.45/1.34  %Foreground sorts:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Background operators:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Foreground operators:
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.45/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.34  
% 2.45/1.35  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.45/1.35  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.45/1.35  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.45/1.35  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.45/1.35  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.45/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.45/1.35  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.45/1.35  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.45/1.35  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.35  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.35  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.35  tff(c_158, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.35  tff(c_181, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_158])).
% 2.45/1.35  tff(c_279, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.35  tff(c_300, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_181, c_279])).
% 2.45/1.35  tff(c_304, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_300])).
% 2.45/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.35  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.35  tff(c_182, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_158])).
% 2.45/1.35  tff(c_297, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_182, c_279])).
% 2.45/1.35  tff(c_303, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_297])).
% 2.45/1.35  tff(c_347, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_303])).
% 2.45/1.35  tff(c_305, plain, (![C_36, A_37, B_38]: (k2_xboole_0(k10_relat_1(C_36, A_37), k10_relat_1(C_36, B_38))=k10_relat_1(C_36, k2_xboole_0(A_37, B_38)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.35  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.35  tff(c_776, plain, (![C_49, A_50, B_51]: (r1_tarski(k10_relat_1(C_49, A_50), k10_relat_1(C_49, k2_xboole_0(A_50, B_51))) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_305, c_12])).
% 2.45/1.35  tff(c_817, plain, (![C_52]: (r1_tarski(k10_relat_1(C_52, '#skF_1'), k10_relat_1(C_52, '#skF_2')) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_347, c_776])).
% 2.45/1.35  tff(c_18, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.35  tff(c_823, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_817, c_18])).
% 2.45/1.35  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_823])).
% 2.45/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  Inference rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Ref     : 0
% 2.45/1.35  #Sup     : 201
% 2.45/1.35  #Fact    : 0
% 2.45/1.35  #Define  : 0
% 2.45/1.35  #Split   : 0
% 2.45/1.35  #Chain   : 0
% 2.45/1.35  #Close   : 0
% 2.45/1.35  
% 2.45/1.35  Ordering : KBO
% 2.45/1.35  
% 2.45/1.35  Simplification rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Subsume      : 1
% 2.45/1.35  #Demod        : 145
% 2.45/1.35  #Tautology    : 146
% 2.45/1.35  #SimpNegUnit  : 0
% 2.45/1.35  #BackRed      : 0
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.45/1.35  Preprocessing        : 0.26
% 2.45/1.35  Parsing              : 0.15
% 2.45/1.35  CNF conversion       : 0.02
% 2.45/1.35  Main loop            : 0.32
% 2.45/1.35  Inferencing          : 0.12
% 2.45/1.35  Reduction            : 0.13
% 2.45/1.35  Demodulation         : 0.10
% 2.45/1.35  BG Simplification    : 0.01
% 2.45/1.35  Subsumption          : 0.05
% 2.45/1.35  Abstraction          : 0.02
% 2.45/1.35  MUC search           : 0.00
% 2.45/1.35  Cooper               : 0.00
% 2.45/1.35  Total                : 0.61
% 2.45/1.35  Index Insertion      : 0.00
% 2.45/1.35  Index Deletion       : 0.00
% 2.45/1.35  Index Matching       : 0.00
% 2.45/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
