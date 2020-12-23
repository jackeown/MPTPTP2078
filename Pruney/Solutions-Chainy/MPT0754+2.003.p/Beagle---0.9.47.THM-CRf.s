%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 110 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A)
              & v1_funct_1(C)
              & v5_ordinal1(C) )
           => ( v1_relat_1(C)
              & v5_relat_1(C,B)
              & v1_funct_1(C)
              & v5_ordinal1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
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

tff(c_47,plain,(
    ! [B_19,A_20] :
      ( k2_xboole_0(k2_relat_1(B_19),A_20) = A_20
      | ~ v5_relat_1(B_19,A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_37,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [B_21,C_22,A_23] :
      ( r1_tarski(k2_relat_1(B_21),C_22)
      | ~ r1_tarski(A_23,C_22)
      | ~ v5_relat_1(B_21,A_23)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_2])).

tff(c_66,plain,(
    ! [B_24] :
      ( r1_tarski(k2_relat_1(B_24),'#skF_2')
      | ~ v5_relat_1(B_24,'#skF_1')
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v5_relat_1(B_7,A_6)
      | ~ r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [B_28] :
      ( v5_relat_1(B_28,'#skF_2')
      | ~ v5_relat_1(B_28,'#skF_1')
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_14,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    v5_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,
    ( ~ v5_ordinal1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_12,c_10])).

tff(c_82,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_22])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.15  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.15  
% 1.86/1.15  %Foreground sorts:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Background operators:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Foreground operators:
% 1.86/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.15  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.86/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.15  
% 1.86/1.16  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) & v5_ordinal1(C)) => (((v1_relat_1(C) & v5_relat_1(C, B)) & v1_funct_1(C)) & v5_ordinal1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_ordinal1)).
% 1.86/1.16  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.86/1.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.86/1.16  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.86/1.16  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.16  tff(c_16, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.16  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.16  tff(c_37, plain, (![B_15, A_16]: (r1_tarski(k2_relat_1(B_15), A_16) | ~v5_relat_1(B_15, A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.16  tff(c_47, plain, (![B_19, A_20]: (k2_xboole_0(k2_relat_1(B_19), A_20)=A_20 | ~v5_relat_1(B_19, A_20) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_37, c_4])).
% 1.86/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.16  tff(c_59, plain, (![B_21, C_22, A_23]: (r1_tarski(k2_relat_1(B_21), C_22) | ~r1_tarski(A_23, C_22) | ~v5_relat_1(B_21, A_23) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_47, c_2])).
% 1.86/1.16  tff(c_66, plain, (![B_24]: (r1_tarski(k2_relat_1(B_24), '#skF_2') | ~v5_relat_1(B_24, '#skF_1') | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_20, c_59])).
% 1.86/1.16  tff(c_6, plain, (![B_7, A_6]: (v5_relat_1(B_7, A_6) | ~r1_tarski(k2_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_79, plain, (![B_28]: (v5_relat_1(B_28, '#skF_2') | ~v5_relat_1(B_28, '#skF_1') | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_66, c_6])).
% 1.86/1.16  tff(c_14, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.16  tff(c_12, plain, (v5_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.16  tff(c_10, plain, (~v5_ordinal1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.86/1.16  tff(c_22, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_12, c_10])).
% 1.86/1.16  tff(c_82, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_22])).
% 1.86/1.16  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_82])).
% 1.86/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  Inference rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Ref     : 0
% 1.86/1.16  #Sup     : 15
% 1.86/1.16  #Fact    : 0
% 1.86/1.16  #Define  : 0
% 1.86/1.16  #Split   : 0
% 1.86/1.16  #Chain   : 0
% 1.86/1.16  #Close   : 0
% 1.86/1.16  
% 1.86/1.16  Ordering : KBO
% 1.86/1.16  
% 1.86/1.16  Simplification rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Subsume      : 0
% 1.86/1.16  #Demod        : 5
% 1.86/1.16  #Tautology    : 5
% 1.86/1.16  #SimpNegUnit  : 0
% 1.86/1.16  #BackRed      : 0
% 1.86/1.16  
% 1.86/1.16  #Partial instantiations: 0
% 1.86/1.16  #Strategies tried      : 1
% 1.86/1.16  
% 1.86/1.16  Timing (in seconds)
% 1.86/1.16  ----------------------
% 1.86/1.16  Preprocessing        : 0.25
% 1.86/1.16  Parsing              : 0.14
% 1.86/1.16  CNF conversion       : 0.02
% 1.86/1.16  Main loop            : 0.12
% 1.86/1.17  Inferencing          : 0.06
% 1.86/1.17  Reduction            : 0.03
% 1.86/1.17  Demodulation         : 0.02
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.00
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.40
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
