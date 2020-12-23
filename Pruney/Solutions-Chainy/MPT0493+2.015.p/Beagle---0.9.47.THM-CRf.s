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
% DateTime   : Thu Dec  3 09:59:37 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  54 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_14,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k3_xboole_0(B_18,C_19))
      | ~ r1_tarski(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_22,B_23,A_24] :
      ( r1_tarski(A_22,k1_relat_1(k7_relat_1(B_23,A_24)))
      | ~ r1_tarski(A_22,A_24)
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [B_13,A_14] :
      ( B_13 = A_14
      | ~ r1_tarski(B_13,A_14)
      | ~ r1_tarski(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [B_7,A_6] :
      ( k1_relat_1(k7_relat_1(B_7,A_6)) = A_6
      | ~ r1_tarski(A_6,k1_relat_1(k7_relat_1(B_7,A_6)))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_57,plain,(
    ! [B_23,A_24] :
      ( k1_relat_1(k7_relat_1(B_23,A_24)) = A_24
      | ~ r1_tarski(A_24,A_24)
      | ~ r1_tarski(A_24,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_53,c_29])).

tff(c_64,plain,(
    ! [B_25,A_26] :
      ( k1_relat_1(k7_relat_1(B_25,A_26)) = A_26
      | ~ r1_tarski(A_26,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_74,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_83,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.14  
% 1.64/1.15  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 1.64/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.64/1.15  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.64/1.15  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.64/1.15  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 1.64/1.15  tff(c_14, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.15  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.15  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.15  tff(c_12, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.15  tff(c_45, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k3_xboole_0(B_18, C_19)) | ~r1_tarski(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.15  tff(c_53, plain, (![A_22, B_23, A_24]: (r1_tarski(A_22, k1_relat_1(k7_relat_1(B_23, A_24))) | ~r1_tarski(A_22, A_24) | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_12, c_45])).
% 1.64/1.15  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.15  tff(c_22, plain, (![B_13, A_14]: (B_13=A_14 | ~r1_tarski(B_13, A_14) | ~r1_tarski(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.15  tff(c_29, plain, (![B_7, A_6]: (k1_relat_1(k7_relat_1(B_7, A_6))=A_6 | ~r1_tarski(A_6, k1_relat_1(k7_relat_1(B_7, A_6))) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_22])).
% 1.64/1.15  tff(c_57, plain, (![B_23, A_24]: (k1_relat_1(k7_relat_1(B_23, A_24))=A_24 | ~r1_tarski(A_24, A_24) | ~r1_tarski(A_24, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_53, c_29])).
% 1.64/1.15  tff(c_64, plain, (![B_25, A_26]: (k1_relat_1(k7_relat_1(B_25, A_26))=A_26 | ~r1_tarski(A_26, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 1.64/1.15  tff(c_74, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_64])).
% 1.64/1.15  tff(c_83, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_74])).
% 1.64/1.15  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_83])).
% 1.64/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  Inference rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Ref     : 0
% 1.64/1.15  #Sup     : 13
% 1.64/1.15  #Fact    : 0
% 1.64/1.15  #Define  : 0
% 1.64/1.15  #Split   : 1
% 1.64/1.15  #Chain   : 0
% 1.64/1.15  #Close   : 0
% 1.64/1.15  
% 1.64/1.15  Ordering : KBO
% 1.64/1.15  
% 1.64/1.15  Simplification rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Subsume      : 0
% 1.64/1.15  #Demod        : 4
% 1.64/1.15  #Tautology    : 4
% 1.64/1.15  #SimpNegUnit  : 1
% 1.64/1.15  #BackRed      : 0
% 1.64/1.15  
% 1.64/1.15  #Partial instantiations: 0
% 1.64/1.15  #Strategies tried      : 1
% 1.64/1.15  
% 1.64/1.15  Timing (in seconds)
% 1.64/1.15  ----------------------
% 1.64/1.15  Preprocessing        : 0.28
% 1.64/1.15  Parsing              : 0.15
% 1.64/1.15  CNF conversion       : 0.02
% 1.64/1.15  Main loop            : 0.11
% 1.64/1.15  Inferencing          : 0.04
% 1.64/1.15  Reduction            : 0.03
% 1.64/1.15  Demodulation         : 0.02
% 1.64/1.15  BG Simplification    : 0.01
% 1.64/1.15  Subsumption          : 0.02
% 1.64/1.16  Abstraction          : 0.01
% 1.64/1.16  MUC search           : 0.00
% 1.64/1.16  Cooper               : 0.00
% 1.64/1.16  Total                : 0.41
% 1.64/1.16  Index Insertion      : 0.00
% 1.64/1.16  Index Deletion       : 0.00
% 1.64/1.16  Index Matching       : 0.00
% 1.64/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
