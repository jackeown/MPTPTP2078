%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:37 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_14,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_182,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(k1_relat_1(B_22),A_23) = k1_relat_1(k7_relat_1(B_22,A_23))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,k1_relat_1(B_25)) = k1_relat_1(k7_relat_1(B_25,A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_62])).

tff(c_75,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_75])).

tff(c_96,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_224,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_96])).

tff(c_251,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_224])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.21  
% 1.89/1.22  tff(f_46, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 1.89/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.89/1.22  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.89/1.22  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.89/1.22  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.89/1.22  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.89/1.22  tff(c_14, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.89/1.22  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.89/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.22  tff(c_182, plain, (![B_22, A_23]: (k3_xboole_0(k1_relat_1(B_22), A_23)=k1_relat_1(k7_relat_1(B_22, A_23)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.22  tff(c_210, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k1_relat_1(B_25))=k1_relat_1(k7_relat_1(B_25, A_24)) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 1.89/1.22  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.22  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.89/1.22  tff(c_62, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.22  tff(c_70, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_62])).
% 1.89/1.22  tff(c_75, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.22  tff(c_90, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_75])).
% 1.89/1.22  tff(c_96, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_90])).
% 1.89/1.22  tff(c_224, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_210, c_96])).
% 1.89/1.22  tff(c_251, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_224])).
% 1.89/1.22  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_251])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 61
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 0
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 4
% 1.89/1.22  #Demod        : 14
% 1.89/1.22  #Tautology    : 32
% 1.89/1.22  #SimpNegUnit  : 1
% 1.89/1.22  #BackRed      : 0
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.22  Preprocessing        : 0.29
% 1.89/1.22  Parsing              : 0.16
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.22  Main loop            : 0.17
% 1.89/1.23  Inferencing          : 0.07
% 1.89/1.23  Reduction            : 0.06
% 1.89/1.23  Demodulation         : 0.04
% 1.89/1.23  BG Simplification    : 0.01
% 1.89/1.23  Subsumption          : 0.02
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.47
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
