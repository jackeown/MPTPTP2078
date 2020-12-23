%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_8,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_14,C_15,B_16] :
      ( k3_xboole_0(A_14,k10_relat_1(C_15,B_16)) = k10_relat_1(k7_relat_1(C_15,A_14),B_16)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_82,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_56])).

tff(c_105,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.17  
% 1.59/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.18  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.59/1.18  
% 1.59/1.18  %Foreground sorts:
% 1.59/1.18  
% 1.59/1.18  
% 1.59/1.18  %Background operators:
% 1.59/1.18  
% 1.59/1.18  
% 1.59/1.18  %Foreground operators:
% 1.59/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.59/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.59/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.59/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.18  
% 1.59/1.18  tff(f_45, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 1.59/1.18  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 1.59/1.18  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.59/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.59/1.18  tff(c_8, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.18  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.18  tff(c_76, plain, (![A_14, C_15, B_16]: (k3_xboole_0(A_14, k10_relat_1(C_15, B_16))=k10_relat_1(k7_relat_1(C_15, A_14), B_16) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.18  tff(c_10, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.59/1.18  tff(c_48, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.18  tff(c_52, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_48])).
% 1.59/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.18  tff(c_56, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_52, c_2])).
% 1.59/1.18  tff(c_82, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_56])).
% 1.59/1.18  tff(c_105, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 1.59/1.18  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_105])).
% 1.59/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.18  
% 1.59/1.18  Inference rules
% 1.59/1.18  ----------------------
% 1.59/1.18  #Ref     : 0
% 1.59/1.18  #Sup     : 25
% 1.59/1.18  #Fact    : 0
% 1.59/1.18  #Define  : 0
% 1.59/1.18  #Split   : 0
% 1.59/1.18  #Chain   : 0
% 1.59/1.18  #Close   : 0
% 1.59/1.18  
% 1.59/1.18  Ordering : KBO
% 1.59/1.18  
% 1.59/1.18  Simplification rules
% 1.59/1.18  ----------------------
% 1.59/1.18  #Subsume      : 0
% 1.59/1.18  #Demod        : 4
% 1.59/1.18  #Tautology    : 16
% 1.59/1.18  #SimpNegUnit  : 1
% 1.59/1.18  #BackRed      : 0
% 1.59/1.18  
% 1.59/1.18  #Partial instantiations: 0
% 1.59/1.18  #Strategies tried      : 1
% 1.59/1.18  
% 1.59/1.18  Timing (in seconds)
% 1.59/1.18  ----------------------
% 1.78/1.19  Preprocessing        : 0.29
% 1.78/1.19  Parsing              : 0.15
% 1.78/1.19  CNF conversion       : 0.02
% 1.78/1.19  Main loop            : 0.09
% 1.78/1.19  Inferencing          : 0.04
% 1.78/1.19  Reduction            : 0.03
% 1.78/1.19  Demodulation         : 0.03
% 1.78/1.19  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.01
% 1.78/1.19  Abstraction          : 0.01
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.40
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
