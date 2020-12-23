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
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  41 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_18,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden('#skF_2'(A_16,B_17,C_18),B_17)
      | ~ r2_hidden(A_16,k10_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [B_19,A_20,C_21] :
      ( ~ v1_xboole_0(B_19)
      | ~ r2_hidden(A_20,k10_relat_1(C_21,B_19))
      | ~ v1_relat_1(C_21) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_49,plain,(
    ! [B_22,C_23] :
      ( ~ v1_xboole_0(B_22)
      | ~ v1_relat_1(C_23)
      | v1_xboole_0(k10_relat_1(C_23,B_22)) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [C_27,B_28] :
      ( k10_relat_1(C_27,B_28) = k1_xboole_0
      | ~ v1_xboole_0(B_28)
      | ~ v1_relat_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_49,c_8])).

tff(c_66,plain,(
    ! [C_29] :
      ( k10_relat_1(C_29,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_69,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.63/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.63/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.63/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.13  
% 1.63/1.13  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.63/1.13  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.63/1.13  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.63/1.13  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.63/1.13  tff(c_18, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.63/1.13  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.63/1.13  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.13  tff(c_33, plain, (![A_16, B_17, C_18]: (r2_hidden('#skF_2'(A_16, B_17, C_18), B_17) | ~r2_hidden(A_16, k10_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.63/1.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.13  tff(c_38, plain, (![B_19, A_20, C_21]: (~v1_xboole_0(B_19) | ~r2_hidden(A_20, k10_relat_1(C_21, B_19)) | ~v1_relat_1(C_21))), inference(resolution, [status(thm)], [c_33, c_2])).
% 1.63/1.13  tff(c_49, plain, (![B_22, C_23]: (~v1_xboole_0(B_22) | ~v1_relat_1(C_23) | v1_xboole_0(k10_relat_1(C_23, B_22)))), inference(resolution, [status(thm)], [c_4, c_38])).
% 1.63/1.13  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.63/1.13  tff(c_59, plain, (![C_27, B_28]: (k10_relat_1(C_27, B_28)=k1_xboole_0 | ~v1_xboole_0(B_28) | ~v1_relat_1(C_27))), inference(resolution, [status(thm)], [c_49, c_8])).
% 1.63/1.13  tff(c_66, plain, (![C_29]: (k10_relat_1(C_29, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_29))), inference(resolution, [status(thm)], [c_6, c_59])).
% 1.63/1.13  tff(c_69, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.63/1.13  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_69])).
% 1.63/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  Inference rules
% 1.63/1.13  ----------------------
% 1.63/1.13  #Ref     : 0
% 1.63/1.13  #Sup     : 10
% 1.63/1.13  #Fact    : 0
% 1.63/1.13  #Define  : 0
% 1.63/1.13  #Split   : 0
% 1.63/1.13  #Chain   : 0
% 1.63/1.13  #Close   : 0
% 1.63/1.13  
% 1.63/1.13  Ordering : KBO
% 1.63/1.13  
% 1.63/1.13  Simplification rules
% 1.63/1.13  ----------------------
% 1.63/1.13  #Subsume      : 0
% 1.63/1.13  #Demod        : 0
% 1.63/1.13  #Tautology    : 2
% 1.63/1.13  #SimpNegUnit  : 1
% 1.63/1.13  #BackRed      : 0
% 1.63/1.13  
% 1.63/1.13  #Partial instantiations: 0
% 1.63/1.13  #Strategies tried      : 1
% 1.63/1.13  
% 1.63/1.13  Timing (in seconds)
% 1.63/1.13  ----------------------
% 1.63/1.14  Preprocessing        : 0.26
% 1.63/1.14  Parsing              : 0.15
% 1.63/1.14  CNF conversion       : 0.02
% 1.63/1.14  Main loop            : 0.10
% 1.63/1.14  Inferencing          : 0.05
% 1.63/1.14  Reduction            : 0.02
% 1.63/1.14  Demodulation         : 0.01
% 1.63/1.14  BG Simplification    : 0.01
% 1.63/1.14  Subsumption          : 0.02
% 1.63/1.14  Abstraction          : 0.00
% 1.63/1.14  MUC search           : 0.00
% 1.63/1.14  Cooper               : 0.00
% 1.63/1.14  Total                : 0.38
% 1.63/1.14  Index Insertion      : 0.00
% 1.63/1.14  Index Deletion       : 0.00
% 1.63/1.14  Index Matching       : 0.00
% 1.63/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
