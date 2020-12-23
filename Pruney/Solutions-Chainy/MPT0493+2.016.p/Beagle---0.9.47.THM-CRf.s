%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:37 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  54 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_16,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,(
    ! [B_28,A_29] :
      ( k3_xboole_0(k1_relat_1(B_28),A_29) = k1_relat_1(k7_relat_1(B_28,A_29))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_64,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(k3_xboole_0(A_20,C_21),k3_xboole_0(B_22,C_21))
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [B_2,B_22] :
      ( r1_tarski(B_2,k3_xboole_0(B_22,B_2))
      | ~ r1_tarski(B_2,B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_64])).

tff(c_509,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k1_relat_1(k7_relat_1(B_48,A_47)))
      | ~ r1_tarski(A_47,k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_78])).

tff(c_56,plain,(
    ! [B_18,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_18,A_19)),A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_18,A_19] :
      ( k1_relat_1(k7_relat_1(B_18,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(k7_relat_1(B_18,A_19)))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_529,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(k7_relat_1(B_49,A_50)) = A_50
      | ~ r1_tarski(A_50,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_509,c_62])).

tff(c_546,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_529])).

tff(c_556,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_546])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.27  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.26/1.27  
% 2.26/1.27  %Foreground sorts:
% 2.26/1.27  
% 2.26/1.27  
% 2.26/1.27  %Background operators:
% 2.26/1.27  
% 2.26/1.27  
% 2.26/1.27  %Foreground operators:
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.26/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.27  
% 2.26/1.28  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.26/1.28  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.26/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.28  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.26/1.28  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.26/1.28  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.26/1.28  tff(c_16, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.28  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.28  tff(c_18, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.28  tff(c_138, plain, (![B_28, A_29]: (k3_xboole_0(k1_relat_1(B_28), A_29)=k1_relat_1(k7_relat_1(B_28, A_29)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.28  tff(c_23, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.26/1.28  tff(c_31, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_23])).
% 2.26/1.28  tff(c_64, plain, (![A_20, C_21, B_22]: (r1_tarski(k3_xboole_0(A_20, C_21), k3_xboole_0(B_22, C_21)) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.28  tff(c_78, plain, (![B_2, B_22]: (r1_tarski(B_2, k3_xboole_0(B_22, B_2)) | ~r1_tarski(B_2, B_22))), inference(superposition, [status(thm), theory('equality')], [c_31, c_64])).
% 2.26/1.28  tff(c_509, plain, (![A_47, B_48]: (r1_tarski(A_47, k1_relat_1(k7_relat_1(B_48, A_47))) | ~r1_tarski(A_47, k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_138, c_78])).
% 2.26/1.28  tff(c_56, plain, (![B_18, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_18, A_19)), A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.28  tff(c_62, plain, (![B_18, A_19]: (k1_relat_1(k7_relat_1(B_18, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(k7_relat_1(B_18, A_19))) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.26/1.28  tff(c_529, plain, (![B_49, A_50]: (k1_relat_1(k7_relat_1(B_49, A_50))=A_50 | ~r1_tarski(A_50, k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_509, c_62])).
% 2.26/1.28  tff(c_546, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_529])).
% 2.26/1.28  tff(c_556, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_546])).
% 2.26/1.28  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_556])).
% 2.26/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.28  
% 2.26/1.28  Inference rules
% 2.26/1.28  ----------------------
% 2.26/1.28  #Ref     : 0
% 2.26/1.28  #Sup     : 138
% 2.26/1.28  #Fact    : 0
% 2.26/1.28  #Define  : 0
% 2.26/1.28  #Split   : 1
% 2.26/1.28  #Chain   : 0
% 2.26/1.28  #Close   : 0
% 2.26/1.28  
% 2.26/1.28  Ordering : KBO
% 2.26/1.28  
% 2.26/1.28  Simplification rules
% 2.26/1.28  ----------------------
% 2.26/1.28  #Subsume      : 26
% 2.26/1.28  #Demod        : 44
% 2.26/1.28  #Tautology    : 47
% 2.26/1.28  #SimpNegUnit  : 3
% 2.26/1.28  #BackRed      : 0
% 2.26/1.28  
% 2.26/1.28  #Partial instantiations: 0
% 2.26/1.28  #Strategies tried      : 1
% 2.26/1.28  
% 2.26/1.28  Timing (in seconds)
% 2.26/1.28  ----------------------
% 2.26/1.28  Preprocessing        : 0.27
% 2.26/1.28  Parsing              : 0.14
% 2.26/1.28  CNF conversion       : 0.02
% 2.26/1.28  Main loop            : 0.26
% 2.26/1.28  Inferencing          : 0.10
% 2.26/1.28  Reduction            : 0.07
% 2.26/1.28  Demodulation         : 0.05
% 2.26/1.28  BG Simplification    : 0.01
% 2.26/1.28  Subsumption          : 0.06
% 2.26/1.28  Abstraction          : 0.02
% 2.26/1.28  MUC search           : 0.00
% 2.26/1.28  Cooper               : 0.00
% 2.26/1.28  Total                : 0.55
% 2.26/1.28  Index Insertion      : 0.00
% 2.26/1.28  Index Deletion       : 0.00
% 2.26/1.28  Index Matching       : 0.00
% 2.26/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
