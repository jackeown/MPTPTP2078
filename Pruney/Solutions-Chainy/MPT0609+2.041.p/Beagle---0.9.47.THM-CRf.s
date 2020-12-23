%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:36 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   29 (  38 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  37 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k1_relat_1(k6_subset_1(B_6,k7_relat_1(B_6,A_5))) = k6_subset_1(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13,plain,(
    ! [B_6,A_5] :
      ( k1_relat_1(k4_xboole_0(B_6,k7_relat_1(B_6,A_5))) = k4_xboole_0(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_33,plain,(
    ! [B_13,A_14] :
      ( k3_xboole_0(k1_relat_1(B_13),A_14) = k1_relat_1(k7_relat_1(B_13,A_14))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [B_17,A_18] :
      ( k4_xboole_0(k1_relat_1(B_17),k1_relat_1(k7_relat_1(B_17,A_18))) = k4_xboole_0(k1_relat_1(B_17),A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_2])).

tff(c_10,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_10])).

tff(c_63,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_14])).

tff(c_72,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_63])).

tff(c_76,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13,c_72])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:10:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.14  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.64/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.14  
% 1.64/1.15  tff(f_42, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 1.64/1.15  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.64/1.15  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 1.64/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.64/1.15  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.64/1.15  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.15  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.15  tff(c_6, plain, (![B_6, A_5]: (k1_relat_1(k6_subset_1(B_6, k7_relat_1(B_6, A_5)))=k6_subset_1(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.15  tff(c_13, plain, (![B_6, A_5]: (k1_relat_1(k4_xboole_0(B_6, k7_relat_1(B_6, A_5)))=k4_xboole_0(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 1.64/1.15  tff(c_33, plain, (![B_13, A_14]: (k3_xboole_0(k1_relat_1(B_13), A_14)=k1_relat_1(k7_relat_1(B_13, A_14)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.15  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.15  tff(c_57, plain, (![B_17, A_18]: (k4_xboole_0(k1_relat_1(B_17), k1_relat_1(k7_relat_1(B_17, A_18)))=k4_xboole_0(k1_relat_1(B_17), A_18) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_33, c_2])).
% 1.64/1.15  tff(c_10, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.15  tff(c_14, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_10])).
% 1.64/1.15  tff(c_63, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_14])).
% 1.64/1.15  tff(c_72, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_63])).
% 1.64/1.15  tff(c_76, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13, c_72])).
% 1.64/1.15  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_76])).
% 1.64/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  Inference rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Ref     : 0
% 1.64/1.15  #Sup     : 15
% 1.64/1.15  #Fact    : 0
% 1.64/1.15  #Define  : 0
% 1.64/1.15  #Split   : 0
% 1.64/1.15  #Chain   : 0
% 1.64/1.15  #Close   : 0
% 1.64/1.15  
% 1.64/1.15  Ordering : KBO
% 1.64/1.15  
% 1.64/1.15  Simplification rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Subsume      : 0
% 1.64/1.15  #Demod        : 6
% 1.64/1.15  #Tautology    : 10
% 1.64/1.15  #SimpNegUnit  : 0
% 1.64/1.15  #BackRed      : 0
% 1.64/1.15  
% 1.64/1.15  #Partial instantiations: 0
% 1.64/1.15  #Strategies tried      : 1
% 1.64/1.15  
% 1.64/1.15  Timing (in seconds)
% 1.64/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.28
% 1.78/1.15  Parsing              : 0.15
% 1.78/1.15  CNF conversion       : 0.01
% 1.78/1.15  Main loop            : 0.10
% 1.78/1.15  Inferencing          : 0.04
% 1.78/1.15  Reduction            : 0.03
% 1.78/1.16  Demodulation         : 0.02
% 1.78/1.16  BG Simplification    : 0.01
% 1.78/1.16  Subsumption          : 0.01
% 1.78/1.16  Abstraction          : 0.01
% 1.78/1.16  MUC search           : 0.00
% 1.78/1.16  Cooper               : 0.00
% 1.78/1.16  Total                : 0.40
% 1.78/1.16  Index Insertion      : 0.00
% 1.78/1.16  Index Deletion       : 0.00
% 1.78/1.16  Index Matching       : 0.00
% 1.78/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
