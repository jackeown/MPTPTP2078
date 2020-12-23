%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:02 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   27 (  31 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [B_18,A_19] :
      ( k1_relat_1(k7_relat_1(B_18,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [B_24,A_25,C_26] :
      ( k1_relat_1(k7_relat_1(B_24,k4_xboole_0(A_25,C_26))) = k4_xboole_0(A_25,C_26)
      | ~ v1_relat_1(B_24)
      | ~ r1_tarski(A_25,k1_relat_1(B_24)) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_10,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k6_subset_1(k1_relat_1('#skF_2'),'#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_93,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_17])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.13  
% 1.64/1.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.64/1.14  tff(f_48, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 1.64/1.14  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.64/1.14  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.64/1.14  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.64/1.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.14  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.14  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.14  tff(c_40, plain, (![B_18, A_19]: (k1_relat_1(k7_relat_1(B_18, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.14  tff(c_81, plain, (![B_24, A_25, C_26]: (k1_relat_1(k7_relat_1(B_24, k4_xboole_0(A_25, C_26)))=k4_xboole_0(A_25, C_26) | ~v1_relat_1(B_24) | ~r1_tarski(A_25, k1_relat_1(B_24)))), inference(resolution, [status(thm)], [c_8, c_40])).
% 1.64/1.14  tff(c_10, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.14  tff(c_14, plain, (k1_relat_1(k7_relat_1('#skF_2', k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.14  tff(c_17, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 1.64/1.14  tff(c_93, plain, (~v1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_17])).
% 1.64/1.14  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_16, c_93])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 18
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 0
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.14  
% 1.64/1.14  Ordering : KBO
% 1.64/1.14  
% 1.64/1.14  Simplification rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Subsume      : 0
% 1.64/1.14  #Demod        : 6
% 1.64/1.14  #Tautology    : 8
% 1.64/1.14  #SimpNegUnit  : 0
% 1.64/1.14  #BackRed      : 0
% 1.64/1.14  
% 1.64/1.14  #Partial instantiations: 0
% 1.64/1.14  #Strategies tried      : 1
% 1.64/1.14  
% 1.64/1.14  Timing (in seconds)
% 1.64/1.14  ----------------------
% 1.64/1.15  Preprocessing        : 0.28
% 1.64/1.15  Parsing              : 0.15
% 1.64/1.15  CNF conversion       : 0.01
% 1.64/1.15  Main loop            : 0.10
% 1.64/1.15  Inferencing          : 0.04
% 1.64/1.15  Reduction            : 0.03
% 1.64/1.15  Demodulation         : 0.02
% 1.64/1.15  BG Simplification    : 0.01
% 1.64/1.15  Subsumption          : 0.02
% 1.64/1.15  Abstraction          : 0.01
% 1.64/1.15  MUC search           : 0.00
% 1.64/1.15  Cooper               : 0.00
% 1.64/1.15  Total                : 0.40
% 1.64/1.15  Index Insertion      : 0.00
% 1.64/1.15  Index Deletion       : 0.00
% 1.64/1.15  Index Matching       : 0.00
% 1.64/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
