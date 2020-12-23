%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  54 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(c_8,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_relat_1(A_3),B_4) = k7_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(k1_relat_1(B_2),A_1) = k1_relat_1(k7_relat_1(B_2,A_1))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [B_12,C_13,A_14] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(B_12),C_13),A_14) = k1_funct_1(C_13,A_14)
      | ~ r2_hidden(A_14,k3_xboole_0(k1_relat_1(C_13),B_12))
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_37,plain,(
    ! [A_15,B_16,A_17] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_15),B_16),A_17) = k1_funct_1(B_16,A_17)
      | ~ r2_hidden(A_17,k1_relat_1(k7_relat_1(B_16,A_15)))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33])).

tff(c_40,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_37])).

tff(c_43,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_40])).

tff(c_48,plain,
    ( k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_52,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.41  
% 1.96/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.41  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.41  
% 1.96/1.41  %Foreground sorts:
% 1.96/1.41  
% 1.96/1.41  
% 1.96/1.41  %Background operators:
% 1.96/1.41  
% 1.96/1.41  
% 1.96/1.41  %Foreground operators:
% 1.96/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.41  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.41  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.41  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.96/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.41  
% 2.08/1.42  tff(f_50, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 2.08/1.42  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.08/1.42  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.08/1.42  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 2.08/1.42  tff(c_8, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.42  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.42  tff(c_4, plain, (![A_3, B_4]: (k5_relat_1(k6_relat_1(A_3), B_4)=k7_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.42  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.42  tff(c_10, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(k1_relat_1(B_2), A_1)=k1_relat_1(k7_relat_1(B_2, A_1)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.42  tff(c_33, plain, (![B_12, C_13, A_14]: (k1_funct_1(k5_relat_1(k6_relat_1(B_12), C_13), A_14)=k1_funct_1(C_13, A_14) | ~r2_hidden(A_14, k3_xboole_0(k1_relat_1(C_13), B_12)) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.42  tff(c_37, plain, (![A_15, B_16, A_17]: (k1_funct_1(k5_relat_1(k6_relat_1(A_15), B_16), A_17)=k1_funct_1(B_16, A_17) | ~r2_hidden(A_17, k1_relat_1(k7_relat_1(B_16, A_15))) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_2, c_33])).
% 2.08/1.42  tff(c_40, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_37])).
% 2.08/1.42  tff(c_43, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_40])).
% 2.08/1.42  tff(c_48, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_43])).
% 2.08/1.42  tff(c_52, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 2.08/1.42  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_52])).
% 2.08/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.42  
% 2.08/1.42  Inference rules
% 2.08/1.42  ----------------------
% 2.08/1.42  #Ref     : 0
% 2.08/1.42  #Sup     : 9
% 2.08/1.42  #Fact    : 0
% 2.08/1.42  #Define  : 0
% 2.08/1.42  #Split   : 0
% 2.08/1.42  #Chain   : 0
% 2.08/1.42  #Close   : 0
% 2.08/1.42  
% 2.08/1.42  Ordering : KBO
% 2.08/1.42  
% 2.08/1.42  Simplification rules
% 2.08/1.42  ----------------------
% 2.08/1.42  #Subsume      : 0
% 2.08/1.42  #Demod        : 3
% 2.08/1.42  #Tautology    : 6
% 2.08/1.42  #SimpNegUnit  : 1
% 2.08/1.42  #BackRed      : 0
% 2.08/1.42  
% 2.08/1.42  #Partial instantiations: 0
% 2.08/1.42  #Strategies tried      : 1
% 2.08/1.42  
% 2.08/1.42  Timing (in seconds)
% 2.08/1.42  ----------------------
% 2.08/1.42  Preprocessing        : 0.45
% 2.08/1.42  Parsing              : 0.24
% 2.08/1.42  CNF conversion       : 0.03
% 2.08/1.42  Main loop            : 0.13
% 2.08/1.42  Inferencing          : 0.06
% 2.08/1.42  Reduction            : 0.04
% 2.08/1.42  Demodulation         : 0.03
% 2.08/1.43  BG Simplification    : 0.01
% 2.08/1.43  Subsumption          : 0.01
% 2.08/1.43  Abstraction          : 0.01
% 2.08/1.43  MUC search           : 0.00
% 2.08/1.43  Cooper               : 0.00
% 2.08/1.43  Total                : 0.62
% 2.08/1.43  Index Insertion      : 0.00
% 2.08/1.43  Index Deletion       : 0.00
% 2.08/1.43  Index Matching       : 0.00
% 2.08/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
