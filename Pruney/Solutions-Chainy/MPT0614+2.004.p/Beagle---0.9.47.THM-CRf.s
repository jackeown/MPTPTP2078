%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:48 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
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
%$ v5_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A) )
           => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [B_15,A_16] :
      ( r1_tarski(k2_relat_1(B_15),A_16)
      | ~ v5_relat_1(B_15,A_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [B_19,A_20] :
      ( k2_xboole_0(k2_relat_1(B_19),A_20) = A_20
      | ~ v5_relat_1(B_19,A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_31,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [B_21,C_22,A_23] :
      ( r1_tarski(k2_relat_1(B_21),C_22)
      | ~ r1_tarski(A_23,C_22)
      | ~ v5_relat_1(B_21,A_23)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_60,plain,(
    ! [B_24] :
      ( r1_tarski(k2_relat_1(B_24),'#skF_2')
      | ~ v5_relat_1(B_24,'#skF_1')
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v5_relat_1(B_7,A_6)
      | ~ r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [B_25] :
      ( v5_relat_1(B_25,'#skF_2')
      | ~ v5_relat_1(B_25,'#skF_1')
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_60,c_6])).

tff(c_10,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_10])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:53 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.10  
% 1.68/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  %$ v5_relat_1 > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.11  
% 1.68/1.11  %Foreground sorts:
% 1.68/1.11  
% 1.68/1.11  
% 1.68/1.11  %Background operators:
% 1.68/1.11  
% 1.68/1.11  
% 1.68/1.11  %Foreground operators:
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.11  
% 1.68/1.11  tff(f_49, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 1.68/1.11  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.68/1.11  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.68/1.11  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.68/1.11  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.11  tff(c_12, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.11  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.11  tff(c_31, plain, (![B_15, A_16]: (r1_tarski(k2_relat_1(B_15), A_16) | ~v5_relat_1(B_15, A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.11  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.11  tff(c_41, plain, (![B_19, A_20]: (k2_xboole_0(k2_relat_1(B_19), A_20)=A_20 | ~v5_relat_1(B_19, A_20) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_31, c_4])).
% 1.68/1.11  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.11  tff(c_53, plain, (![B_21, C_22, A_23]: (r1_tarski(k2_relat_1(B_21), C_22) | ~r1_tarski(A_23, C_22) | ~v5_relat_1(B_21, A_23) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 1.68/1.11  tff(c_60, plain, (![B_24]: (r1_tarski(k2_relat_1(B_24), '#skF_2') | ~v5_relat_1(B_24, '#skF_1') | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_16, c_53])).
% 1.68/1.11  tff(c_6, plain, (![B_7, A_6]: (v5_relat_1(B_7, A_6) | ~r1_tarski(k2_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.11  tff(c_72, plain, (![B_25]: (v5_relat_1(B_25, '#skF_2') | ~v5_relat_1(B_25, '#skF_1') | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_60, c_6])).
% 1.68/1.11  tff(c_10, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.11  tff(c_75, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_10])).
% 1.68/1.11  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_75])).
% 1.68/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  Inference rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Ref     : 0
% 1.68/1.12  #Sup     : 15
% 1.68/1.12  #Fact    : 0
% 1.68/1.12  #Define  : 0
% 1.68/1.12  #Split   : 0
% 1.68/1.12  #Chain   : 0
% 1.68/1.12  #Close   : 0
% 1.68/1.12  
% 1.68/1.12  Ordering : KBO
% 1.68/1.12  
% 1.68/1.12  Simplification rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Subsume      : 0
% 1.68/1.12  #Demod        : 2
% 1.68/1.12  #Tautology    : 5
% 1.68/1.12  #SimpNegUnit  : 0
% 1.68/1.12  #BackRed      : 0
% 1.68/1.12  
% 1.68/1.12  #Partial instantiations: 0
% 1.68/1.12  #Strategies tried      : 1
% 1.68/1.12  
% 1.68/1.12  Timing (in seconds)
% 1.68/1.12  ----------------------
% 1.68/1.12  Preprocessing        : 0.25
% 1.68/1.12  Parsing              : 0.14
% 1.68/1.12  CNF conversion       : 0.02
% 1.68/1.12  Main loop            : 0.11
% 1.68/1.12  Inferencing          : 0.05
% 1.68/1.12  Reduction            : 0.03
% 1.68/1.12  Demodulation         : 0.02
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.02
% 1.68/1.12  Abstraction          : 0.00
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.39
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
