%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
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
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(c_14,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k2_relat_1(B_9),A_8) = k2_relat_1(k8_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k3_xboole_0(B_18,C_19))
      | ~ r1_tarski(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_22,A_23,B_24] :
      ( r1_tarski(A_22,k2_relat_1(k8_relat_1(A_23,B_24)))
      | ~ r1_tarski(A_22,A_23)
      | ~ r1_tarski(A_22,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [B_13,A_14] :
      ( B_13 = A_14
      | ~ r1_tarski(B_13,A_14)
      | ~ r1_tarski(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_6,B_7] :
      ( k2_relat_1(k8_relat_1(A_6,B_7)) = A_6
      | ~ r1_tarski(A_6,k2_relat_1(k8_relat_1(A_6,B_7)))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_57,plain,(
    ! [A_23,B_24] :
      ( k2_relat_1(k8_relat_1(A_23,B_24)) = A_23
      | ~ r1_tarski(A_23,A_23)
      | ~ r1_tarski(A_23,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_53,c_29])).

tff(c_64,plain,(
    ! [A_25,B_26] :
      ( k2_relat_1(k8_relat_1(A_25,B_26)) = A_25
      | ~ r1_tarski(A_25,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_74,plain,
    ( k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_83,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_1
% 1.69/1.10  
% 1.69/1.10  %Foreground sorts:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Background operators:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Foreground operators:
% 1.69/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.10  
% 1.69/1.11  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 1.69/1.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.69/1.11  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 1.69/1.11  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.69/1.11  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 1.69/1.11  tff(c_14, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.69/1.11  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.69/1.11  tff(c_16, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.69/1.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.11  tff(c_12, plain, (![B_9, A_8]: (k3_xboole_0(k2_relat_1(B_9), A_8)=k2_relat_1(k8_relat_1(A_8, B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.11  tff(c_45, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k3_xboole_0(B_18, C_19)) | ~r1_tarski(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.11  tff(c_53, plain, (![A_22, A_23, B_24]: (r1_tarski(A_22, k2_relat_1(k8_relat_1(A_23, B_24))) | ~r1_tarski(A_22, A_23) | ~r1_tarski(A_22, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_45])).
% 1.69/1.11  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.11  tff(c_22, plain, (![B_13, A_14]: (B_13=A_14 | ~r1_tarski(B_13, A_14) | ~r1_tarski(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.11  tff(c_29, plain, (![A_6, B_7]: (k2_relat_1(k8_relat_1(A_6, B_7))=A_6 | ~r1_tarski(A_6, k2_relat_1(k8_relat_1(A_6, B_7))) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_22])).
% 1.69/1.11  tff(c_57, plain, (![A_23, B_24]: (k2_relat_1(k8_relat_1(A_23, B_24))=A_23 | ~r1_tarski(A_23, A_23) | ~r1_tarski(A_23, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_53, c_29])).
% 1.69/1.11  tff(c_64, plain, (![A_25, B_26]: (k2_relat_1(k8_relat_1(A_25, B_26))=A_25 | ~r1_tarski(A_25, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 1.69/1.11  tff(c_74, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_64])).
% 1.69/1.11  tff(c_83, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_74])).
% 1.69/1.11  tff(c_85, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_83])).
% 1.69/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.11  
% 1.69/1.11  Inference rules
% 1.69/1.11  ----------------------
% 1.69/1.11  #Ref     : 0
% 1.69/1.11  #Sup     : 13
% 1.69/1.11  #Fact    : 0
% 1.69/1.11  #Define  : 0
% 1.69/1.11  #Split   : 1
% 1.69/1.11  #Chain   : 0
% 1.69/1.11  #Close   : 0
% 1.69/1.11  
% 1.69/1.11  Ordering : KBO
% 1.69/1.11  
% 1.69/1.11  Simplification rules
% 1.69/1.11  ----------------------
% 1.69/1.11  #Subsume      : 0
% 1.69/1.11  #Demod        : 4
% 1.69/1.11  #Tautology    : 4
% 1.69/1.11  #SimpNegUnit  : 1
% 1.69/1.11  #BackRed      : 0
% 1.69/1.11  
% 1.69/1.11  #Partial instantiations: 0
% 1.69/1.11  #Strategies tried      : 1
% 1.69/1.11  
% 1.69/1.11  Timing (in seconds)
% 1.69/1.11  ----------------------
% 1.69/1.11  Preprocessing        : 0.26
% 1.69/1.11  Parsing              : 0.14
% 1.69/1.11  CNF conversion       : 0.02
% 1.69/1.11  Main loop            : 0.10
% 1.69/1.11  Inferencing          : 0.04
% 1.69/1.11  Reduction            : 0.03
% 1.69/1.12  Demodulation         : 0.02
% 1.69/1.12  BG Simplification    : 0.01
% 1.69/1.12  Subsumption          : 0.02
% 1.69/1.12  Abstraction          : 0.01
% 1.69/1.12  MUC search           : 0.00
% 1.69/1.12  Cooper               : 0.00
% 1.69/1.12  Total                : 0.39
% 1.69/1.12  Index Insertion      : 0.00
% 1.69/1.12  Index Deletion       : 0.00
% 1.69/1.12  Index Matching       : 0.00
% 1.69/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
