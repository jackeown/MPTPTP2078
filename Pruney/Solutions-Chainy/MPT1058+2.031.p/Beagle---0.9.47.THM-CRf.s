%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_26,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_107,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_xboole_0(A_37,k4_xboole_0(C_38,B_39))
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [A_48,C_49,B_50] :
      ( k4_xboole_0(A_48,k4_xboole_0(C_49,B_50)) = A_48
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(resolution,[status(thm)],[c_107,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_187,plain,(
    ! [C_51,B_52] :
      ( k3_xboole_0(C_51,B_52) = C_51
      | ~ r1_tarski(C_51,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_10])).

tff(c_194,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_187])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_2])).

tff(c_24,plain,(
    ! [A_19,C_21,B_20] :
      ( k3_xboole_0(A_19,k10_relat_1(C_21,B_20)) = k10_relat_1(k7_relat_1(C_21,A_19),B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_232,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_24])).

tff(c_239,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_232])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n002.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.15/1.30  
% 2.15/1.30  %Foreground sorts:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Background operators:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Foreground operators:
% 2.15/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.15/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.30  
% 2.15/1.31  tff(f_67, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.15/1.31  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.15/1.31  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.15/1.31  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.15/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.15/1.31  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.15/1.31  tff(c_26, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.31  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.31  tff(c_28, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.31  tff(c_107, plain, (![A_37, C_38, B_39]: (r1_xboole_0(A_37, k4_xboole_0(C_38, B_39)) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.31  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.31  tff(c_156, plain, (![A_48, C_49, B_50]: (k4_xboole_0(A_48, k4_xboole_0(C_49, B_50))=A_48 | ~r1_tarski(A_48, B_50))), inference(resolution, [status(thm)], [c_107, c_14])).
% 2.15/1.31  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.31  tff(c_187, plain, (![C_51, B_52]: (k3_xboole_0(C_51, B_52)=C_51 | ~r1_tarski(C_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_156, c_10])).
% 2.15/1.31  tff(c_194, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_187])).
% 2.15/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.31  tff(c_199, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_2])).
% 2.15/1.31  tff(c_24, plain, (![A_19, C_21, B_20]: (k3_xboole_0(A_19, k10_relat_1(C_21, B_20))=k10_relat_1(k7_relat_1(C_21, A_19), B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.31  tff(c_232, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_199, c_24])).
% 2.15/1.31  tff(c_239, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_232])).
% 2.15/1.31  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_239])).
% 2.15/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  Inference rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Ref     : 0
% 2.15/1.31  #Sup     : 54
% 2.15/1.31  #Fact    : 0
% 2.15/1.31  #Define  : 0
% 2.15/1.31  #Split   : 1
% 2.15/1.31  #Chain   : 0
% 2.15/1.31  #Close   : 0
% 2.15/1.31  
% 2.15/1.31  Ordering : KBO
% 2.15/1.31  
% 2.15/1.31  Simplification rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Subsume      : 1
% 2.15/1.31  #Demod        : 3
% 2.15/1.31  #Tautology    : 26
% 2.15/1.31  #SimpNegUnit  : 1
% 2.15/1.31  #BackRed      : 0
% 2.15/1.31  
% 2.15/1.31  #Partial instantiations: 0
% 2.15/1.31  #Strategies tried      : 1
% 2.15/1.31  
% 2.15/1.31  Timing (in seconds)
% 2.15/1.31  ----------------------
% 2.15/1.31  Preprocessing        : 0.33
% 2.15/1.31  Parsing              : 0.17
% 2.15/1.31  CNF conversion       : 0.02
% 2.15/1.31  Main loop            : 0.18
% 2.15/1.31  Inferencing          : 0.06
% 2.15/1.31  Reduction            : 0.06
% 2.15/1.31  Demodulation         : 0.05
% 2.15/1.31  BG Simplification    : 0.01
% 2.15/1.31  Subsumption          : 0.03
% 2.15/1.31  Abstraction          : 0.01
% 2.15/1.31  MUC search           : 0.00
% 2.15/1.31  Cooper               : 0.00
% 2.15/1.31  Total                : 0.53
% 2.15/1.31  Index Insertion      : 0.00
% 2.15/1.31  Index Deletion       : 0.00
% 2.15/1.31  Index Matching       : 0.00
% 2.15/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
