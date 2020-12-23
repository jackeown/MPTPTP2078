%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_8,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [B_11,A_12] :
      ( k3_xboole_0(k2_relat_1(B_11),A_12) = k2_relat_1(k8_relat_1(A_12,B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,k2_relat_1(B_14)) = k2_relat_1(k8_relat_1(A_13,B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_10,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_46])).

tff(c_84,plain,
    ( k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_50])).

tff(c_115,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.21  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_1
% 1.79/1.21  
% 1.79/1.21  %Foreground sorts:
% 1.79/1.21  
% 1.79/1.21  
% 1.79/1.21  %Background operators:
% 1.79/1.21  
% 1.79/1.21  
% 1.79/1.21  %Foreground operators:
% 1.79/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.79/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.21  
% 1.79/1.21  tff(f_42, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 1.79/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.79/1.21  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 1.79/1.21  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.79/1.21  tff(c_8, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.21  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.21  tff(c_51, plain, (![B_11, A_12]: (k3_xboole_0(k2_relat_1(B_11), A_12)=k2_relat_1(k8_relat_1(A_12, B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.21  tff(c_78, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_relat_1(B_14))=k2_relat_1(k8_relat_1(A_13, B_14)) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_2, c_51])).
% 1.79/1.21  tff(c_10, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.21  tff(c_46, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.21  tff(c_50, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_10, c_46])).
% 1.79/1.21  tff(c_84, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_78, c_50])).
% 1.79/1.21  tff(c_115, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_84])).
% 1.79/1.21  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_115])).
% 1.79/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.21  
% 1.79/1.21  Inference rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Ref     : 0
% 1.79/1.21  #Sup     : 27
% 1.79/1.21  #Fact    : 0
% 1.79/1.21  #Define  : 0
% 1.79/1.21  #Split   : 0
% 1.79/1.21  #Chain   : 0
% 1.79/1.21  #Close   : 0
% 1.79/1.21  
% 1.79/1.21  Ordering : KBO
% 1.79/1.21  
% 1.79/1.21  Simplification rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Subsume      : 0
% 1.79/1.21  #Demod        : 1
% 1.79/1.21  #Tautology    : 13
% 1.79/1.21  #SimpNegUnit  : 1
% 1.79/1.21  #BackRed      : 0
% 1.79/1.21  
% 1.79/1.21  #Partial instantiations: 0
% 1.79/1.21  #Strategies tried      : 1
% 1.79/1.21  
% 1.79/1.21  Timing (in seconds)
% 1.79/1.21  ----------------------
% 1.79/1.22  Preprocessing        : 0.29
% 1.79/1.22  Parsing              : 0.15
% 1.79/1.22  CNF conversion       : 0.02
% 1.79/1.22  Main loop            : 0.10
% 1.79/1.22  Inferencing          : 0.04
% 1.79/1.22  Reduction            : 0.03
% 1.79/1.22  Demodulation         : 0.02
% 1.79/1.22  BG Simplification    : 0.01
% 1.79/1.22  Subsumption          : 0.01
% 1.79/1.22  Abstraction          : 0.01
% 1.79/1.22  MUC search           : 0.00
% 1.79/1.22  Cooper               : 0.00
% 1.79/1.22  Total                : 0.41
% 1.79/1.22  Index Insertion      : 0.00
% 1.79/1.22  Index Deletion       : 0.00
% 1.79/1.22  Index Matching       : 0.00
% 1.79/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
