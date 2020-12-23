%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15,plain,(
    ! [A_7,C_8,B_9] :
      ( r1_tarski(A_7,C_8)
      | ~ r1_tarski(B_9,C_8)
      | ~ r1_tarski(A_7,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,'#skF_2')
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

tff(c_27,plain,(
    ! [B_13,A_14] :
      ( v4_relat_1(B_13,A_14)
      | ~ r1_tarski(k1_relat_1(B_13),A_14)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [B_17] :
      ( v4_relat_1(B_17,'#skF_2')
      | ~ v1_relat_1(B_17)
      | ~ r1_tarski(k1_relat_1(B_17),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_27])).

tff(c_54,plain,(
    ! [B_18] :
      ( v4_relat_1(B_18,'#skF_2')
      | ~ v4_relat_1(B_18,'#skF_1')
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_8,plain,(
    ~ v4_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  %$ v4_relat_1 > r1_tarski > v1_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.09  
% 1.64/1.09  %Foreground sorts:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Background operators:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Foreground operators:
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.64/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.09  
% 1.64/1.10  tff(f_47, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 1.64/1.10  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.64/1.10  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.64/1.10  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.10  tff(c_10, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.10  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.10  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.10  tff(c_15, plain, (![A_7, C_8, B_9]: (r1_tarski(A_7, C_8) | ~r1_tarski(B_9, C_8) | ~r1_tarski(A_7, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.10  tff(c_18, plain, (![A_7]: (r1_tarski(A_7, '#skF_2') | ~r1_tarski(A_7, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_15])).
% 1.64/1.10  tff(c_27, plain, (![B_13, A_14]: (v4_relat_1(B_13, A_14) | ~r1_tarski(k1_relat_1(B_13), A_14) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.10  tff(c_48, plain, (![B_17]: (v4_relat_1(B_17, '#skF_2') | ~v1_relat_1(B_17) | ~r1_tarski(k1_relat_1(B_17), '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_27])).
% 1.64/1.10  tff(c_54, plain, (![B_18]: (v4_relat_1(B_18, '#skF_2') | ~v4_relat_1(B_18, '#skF_1') | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_6, c_48])).
% 1.64/1.10  tff(c_8, plain, (~v4_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.10  tff(c_57, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_8])).
% 1.64/1.10  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_57])).
% 1.64/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  Inference rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Ref     : 0
% 1.64/1.10  #Sup     : 10
% 1.64/1.10  #Fact    : 0
% 1.64/1.10  #Define  : 0
% 1.64/1.10  #Split   : 0
% 1.64/1.10  #Chain   : 0
% 1.64/1.10  #Close   : 0
% 1.64/1.10  
% 1.64/1.10  Ordering : KBO
% 1.64/1.10  
% 1.64/1.10  Simplification rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Subsume      : 1
% 1.64/1.10  #Demod        : 3
% 1.64/1.10  #Tautology    : 2
% 1.64/1.10  #SimpNegUnit  : 0
% 1.64/1.10  #BackRed      : 0
% 1.64/1.10  
% 1.64/1.10  #Partial instantiations: 0
% 1.64/1.10  #Strategies tried      : 1
% 1.64/1.10  
% 1.64/1.10  Timing (in seconds)
% 1.64/1.10  ----------------------
% 1.64/1.10  Preprocessing        : 0.24
% 1.64/1.10  Parsing              : 0.14
% 1.64/1.10  CNF conversion       : 0.01
% 1.64/1.10  Main loop            : 0.10
% 1.64/1.10  Inferencing          : 0.05
% 1.64/1.10  Reduction            : 0.02
% 1.64/1.10  Demodulation         : 0.02
% 1.64/1.10  BG Simplification    : 0.01
% 1.64/1.10  Subsumption          : 0.02
% 1.64/1.10  Abstraction          : 0.00
% 1.64/1.10  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.37
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
