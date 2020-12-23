%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  60 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k1_relat_1(B_24),A_25)
      | ~ v4_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [B_29,A_30] :
      ( k3_xboole_0(k1_relat_1(B_29),A_30) = k1_relat_1(B_29)
      | ~ v4_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_91,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(k3_xboole_0(A_15,C_16),B_17)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [B_2,A_1,B_17] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_17)
      | ~ r1_tarski(A_1,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_639,plain,(
    ! [B_56,B_57,A_58] :
      ( r1_tarski(k1_relat_1(B_56),B_57)
      | ~ r1_tarski(A_58,B_57)
      | ~ v4_relat_1(B_56,A_58)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_70])).

tff(c_658,plain,(
    ! [B_59] :
      ( r1_tarski(k1_relat_1(B_59),'#skF_2')
      | ~ v4_relat_1(B_59,'#skF_1')
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_18,c_639])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( v4_relat_1(B_9,A_8)
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_674,plain,(
    ! [B_60] :
      ( v4_relat_1(B_60,'#skF_2')
      | ~ v4_relat_1(B_60,'#skF_1')
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_658,c_8])).

tff(c_12,plain,(
    ~ v4_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_677,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_674,c_12])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  
% 2.51/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.42  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.42  
% 2.51/1.42  %Foreground sorts:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Background operators:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Foreground operators:
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.51/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.42  
% 2.51/1.43  tff(f_51, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.51/1.43  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.51/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.51/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.51/1.43  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.51/1.43  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.43  tff(c_14, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.43  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.43  tff(c_91, plain, (![B_24, A_25]: (r1_tarski(k1_relat_1(B_24), A_25) | ~v4_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.43  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.43  tff(c_145, plain, (![B_29, A_30]: (k3_xboole_0(k1_relat_1(B_29), A_30)=k1_relat_1(B_29) | ~v4_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_91, c_6])).
% 2.51/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.43  tff(c_61, plain, (![A_15, C_16, B_17]: (r1_tarski(k3_xboole_0(A_15, C_16), B_17) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.43  tff(c_70, plain, (![B_2, A_1, B_17]: (r1_tarski(k3_xboole_0(B_2, A_1), B_17) | ~r1_tarski(A_1, B_17))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 2.51/1.43  tff(c_639, plain, (![B_56, B_57, A_58]: (r1_tarski(k1_relat_1(B_56), B_57) | ~r1_tarski(A_58, B_57) | ~v4_relat_1(B_56, A_58) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_145, c_70])).
% 2.51/1.43  tff(c_658, plain, (![B_59]: (r1_tarski(k1_relat_1(B_59), '#skF_2') | ~v4_relat_1(B_59, '#skF_1') | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_18, c_639])).
% 2.51/1.43  tff(c_8, plain, (![B_9, A_8]: (v4_relat_1(B_9, A_8) | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.43  tff(c_674, plain, (![B_60]: (v4_relat_1(B_60, '#skF_2') | ~v4_relat_1(B_60, '#skF_1') | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_658, c_8])).
% 2.51/1.43  tff(c_12, plain, (~v4_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.43  tff(c_677, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_674, c_12])).
% 2.51/1.43  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_677])).
% 2.51/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.43  
% 2.51/1.43  Inference rules
% 2.51/1.43  ----------------------
% 2.51/1.43  #Ref     : 0
% 2.51/1.43  #Sup     : 186
% 2.51/1.43  #Fact    : 0
% 2.51/1.43  #Define  : 0
% 2.51/1.43  #Split   : 0
% 2.51/1.43  #Chain   : 0
% 2.51/1.43  #Close   : 0
% 2.51/1.43  
% 2.51/1.43  Ordering : KBO
% 2.51/1.43  
% 2.51/1.43  Simplification rules
% 2.51/1.43  ----------------------
% 2.51/1.43  #Subsume      : 33
% 2.51/1.43  #Demod        : 25
% 2.51/1.43  #Tautology    : 42
% 2.51/1.43  #SimpNegUnit  : 0
% 2.51/1.43  #BackRed      : 0
% 2.51/1.43  
% 2.51/1.43  #Partial instantiations: 0
% 2.51/1.43  #Strategies tried      : 1
% 2.51/1.43  
% 2.51/1.43  Timing (in seconds)
% 2.51/1.43  ----------------------
% 2.51/1.43  Preprocessing        : 0.28
% 2.51/1.43  Parsing              : 0.15
% 2.51/1.43  CNF conversion       : 0.02
% 2.51/1.43  Main loop            : 0.34
% 2.51/1.43  Inferencing          : 0.13
% 2.51/1.43  Reduction            : 0.10
% 2.51/1.43  Demodulation         : 0.08
% 2.51/1.43  BG Simplification    : 0.02
% 2.51/1.43  Subsumption          : 0.07
% 2.51/1.43  Abstraction          : 0.02
% 2.51/1.43  MUC search           : 0.00
% 2.51/1.43  Cooper               : 0.00
% 2.51/1.43  Total                : 0.65
% 2.51/1.43  Index Insertion      : 0.00
% 2.51/1.43  Index Deletion       : 0.00
% 2.51/1.43  Index Matching       : 0.00
% 2.51/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
