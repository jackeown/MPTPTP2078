%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  56 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [B_15,A_16] :
      ( r1_tarski(k1_relat_1(B_15),A_16)
      | ~ v4_relat_1(B_15,A_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [B_19,A_20] :
      ( k2_xboole_0(k1_relat_1(B_19),A_20) = A_20
      | ~ v4_relat_1(B_19,A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_31,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [B_21,C_22,A_23] :
      ( r1_tarski(k1_relat_1(B_21),C_22)
      | ~ r1_tarski(A_23,C_22)
      | ~ v4_relat_1(B_21,A_23)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_60,plain,(
    ! [B_24] :
      ( r1_tarski(k1_relat_1(B_24),'#skF_2')
      | ~ v4_relat_1(B_24,'#skF_1')
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [B_25] :
      ( v4_relat_1(B_25,'#skF_2')
      | ~ v4_relat_1(B_25,'#skF_1')
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_60,c_6])).

tff(c_10,plain,(
    ~ v4_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_10])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.13  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.13  
% 1.78/1.13  %Foreground sorts:
% 1.78/1.13  
% 1.78/1.13  
% 1.78/1.13  %Background operators:
% 1.78/1.13  
% 1.78/1.13  
% 1.78/1.13  %Foreground operators:
% 1.78/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.78/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.13  
% 1.78/1.14  tff(f_49, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 1.78/1.14  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.78/1.14  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.78/1.14  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.78/1.14  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.78/1.14  tff(c_12, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.78/1.14  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.78/1.14  tff(c_31, plain, (![B_15, A_16]: (r1_tarski(k1_relat_1(B_15), A_16) | ~v4_relat_1(B_15, A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.14  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.14  tff(c_41, plain, (![B_19, A_20]: (k2_xboole_0(k1_relat_1(B_19), A_20)=A_20 | ~v4_relat_1(B_19, A_20) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_31, c_4])).
% 1.78/1.14  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.14  tff(c_53, plain, (![B_21, C_22, A_23]: (r1_tarski(k1_relat_1(B_21), C_22) | ~r1_tarski(A_23, C_22) | ~v4_relat_1(B_21, A_23) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 1.78/1.14  tff(c_60, plain, (![B_24]: (r1_tarski(k1_relat_1(B_24), '#skF_2') | ~v4_relat_1(B_24, '#skF_1') | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_16, c_53])).
% 1.78/1.14  tff(c_6, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.14  tff(c_72, plain, (![B_25]: (v4_relat_1(B_25, '#skF_2') | ~v4_relat_1(B_25, '#skF_1') | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_60, c_6])).
% 1.78/1.14  tff(c_10, plain, (~v4_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.78/1.14  tff(c_75, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_10])).
% 1.78/1.14  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_75])).
% 1.78/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  
% 1.78/1.14  Inference rules
% 1.78/1.14  ----------------------
% 1.78/1.14  #Ref     : 0
% 1.78/1.14  #Sup     : 15
% 1.78/1.14  #Fact    : 0
% 1.78/1.14  #Define  : 0
% 1.78/1.14  #Split   : 0
% 1.78/1.14  #Chain   : 0
% 1.78/1.14  #Close   : 0
% 1.78/1.14  
% 1.78/1.14  Ordering : KBO
% 1.78/1.14  
% 1.78/1.14  Simplification rules
% 1.78/1.14  ----------------------
% 1.78/1.14  #Subsume      : 0
% 1.78/1.14  #Demod        : 2
% 1.78/1.14  #Tautology    : 5
% 1.78/1.14  #SimpNegUnit  : 0
% 1.78/1.14  #BackRed      : 0
% 1.78/1.14  
% 1.78/1.14  #Partial instantiations: 0
% 1.78/1.14  #Strategies tried      : 1
% 1.78/1.14  
% 1.78/1.14  Timing (in seconds)
% 1.78/1.14  ----------------------
% 1.78/1.15  Preprocessing        : 0.26
% 1.78/1.15  Parsing              : 0.14
% 1.78/1.15  CNF conversion       : 0.02
% 1.78/1.15  Main loop            : 0.12
% 1.78/1.15  Inferencing          : 0.06
% 1.78/1.15  Reduction            : 0.03
% 1.78/1.15  Demodulation         : 0.02
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.15  Subsumption          : 0.02
% 1.78/1.15  Abstraction          : 0.01
% 1.78/1.15  MUC search           : 0.00
% 1.78/1.15  Cooper               : 0.00
% 1.78/1.15  Total                : 0.41
% 1.78/1.15  Index Insertion      : 0.00
% 1.78/1.15  Index Deletion       : 0.00
% 1.78/1.15  Index Matching       : 0.00
% 1.78/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
