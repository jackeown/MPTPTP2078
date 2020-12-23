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
% DateTime   : Thu Dec  3 10:06:48 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k3_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => r4_wellord1(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_wellord1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r3_wellord1(A,A,k6_relat_1(k3_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_1] : v1_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12] :
      ( r3_wellord1(A_12,A_12,k6_relat_1(k3_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25,plain,(
    ! [A_22,B_23,C_24] :
      ( r4_wellord1(A_22,B_23)
      | ~ r3_wellord1(A_22,B_23,C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,(
    ! [A_12] :
      ( r4_wellord1(A_12,A_12)
      | ~ v1_funct_1(k6_relat_1(k3_relat_1(A_12)))
      | ~ v1_relat_1(k6_relat_1(k3_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_36,plain,(
    ! [A_25] :
      ( r4_wellord1(A_25,A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_31])).

tff(c_16,plain,(
    ~ r4_wellord1('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_16])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  %$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k3_relat_1 > #skF_2 > #skF_1
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.15  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 1.66/1.15  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.15  
% 1.66/1.16  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => r4_wellord1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_wellord1)).
% 1.66/1.16  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.66/1.16  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r3_wellord1(A, A, k6_relat_1(k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_wellord1)).
% 1.66/1.16  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) <=> (?[C]: ((v1_relat_1(C) & v1_funct_1(C)) & r3_wellord1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_wellord1)).
% 1.66/1.16  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.16  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.16  tff(c_4, plain, (![A_1]: (v1_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.16  tff(c_14, plain, (![A_12]: (r3_wellord1(A_12, A_12, k6_relat_1(k3_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.16  tff(c_25, plain, (![A_22, B_23, C_24]: (r4_wellord1(A_22, B_23) | ~r3_wellord1(A_22, B_23, C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.16  tff(c_31, plain, (![A_12]: (r4_wellord1(A_12, A_12) | ~v1_funct_1(k6_relat_1(k3_relat_1(A_12))) | ~v1_relat_1(k6_relat_1(k3_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_14, c_25])).
% 1.66/1.16  tff(c_36, plain, (![A_25]: (r4_wellord1(A_25, A_25) | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_31])).
% 1.66/1.16  tff(c_16, plain, (~r4_wellord1('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.16  tff(c_39, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_16])).
% 1.66/1.16  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_39])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 3
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 0
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 0
% 1.66/1.16  #Demod        : 3
% 1.66/1.16  #Tautology    : 1
% 1.66/1.16  #SimpNegUnit  : 0
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.16  Preprocessing        : 0.24
% 1.66/1.16  Parsing              : 0.14
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.09
% 1.66/1.16  Inferencing          : 0.05
% 1.66/1.16  Reduction            : 0.02
% 1.66/1.16  Demodulation         : 0.02
% 1.66/1.16  BG Simplification    : 0.01
% 1.66/1.16  Subsumption          : 0.01
% 1.66/1.16  Abstraction          : 0.00
% 1.66/1.16  MUC search           : 0.00
% 1.66/1.16  Cooper               : 0.00
% 1.66/1.16  Total                : 0.36
% 1.66/1.16  Index Insertion      : 0.00
% 1.66/1.16  Index Deletion       : 0.00
% 1.66/1.16  Index Matching       : 0.00
% 1.66/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
