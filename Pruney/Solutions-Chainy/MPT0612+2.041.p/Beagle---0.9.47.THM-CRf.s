%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,k4_xboole_0(C_23,B_24))
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [C_23,B_24,A_22] :
      ( r1_xboole_0(k4_xboole_0(C_23,B_24),A_22)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(C_15,k6_subset_1(A_13,B_14)) = k6_subset_1(C_15,k7_relat_1(C_15,B_14))
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [C_31,A_32,B_33] :
      ( k7_relat_1(C_31,k4_xboole_0(A_32,B_33)) = k4_xboole_0(C_31,k7_relat_1(C_31,B_33))
      | ~ r1_tarski(k1_relat_1(C_31),A_32)
      | ~ v1_relat_1(C_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_60,plain,(
    ! [C_34,B_35,B_36] :
      ( k7_relat_1(C_34,k4_xboole_0(k2_xboole_0(k1_relat_1(C_34),B_35),B_36)) = k4_xboole_0(C_34,k7_relat_1(C_34,B_36))
      | ~ v1_relat_1(C_34) ) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_10,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [C_51,B_52,B_53,B_54] :
      ( k7_relat_1(k4_xboole_0(C_51,k7_relat_1(C_51,B_52)),B_53) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_51),B_54),B_52),B_53)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10])).

tff(c_106,plain,(
    ! [C_55,B_56,A_57] :
      ( k7_relat_1(k4_xboole_0(C_55,k7_relat_1(C_55,B_56)),A_57) = k1_xboole_0
      | ~ v1_relat_1(C_55)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_35,c_97])).

tff(c_14,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_126,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_19])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.24  
% 1.84/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.25  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.25  
% 1.84/1.25  %Foreground sorts:
% 1.84/1.25  
% 1.84/1.25  
% 1.84/1.25  %Background operators:
% 1.84/1.25  
% 1.84/1.25  
% 1.84/1.25  %Foreground operators:
% 1.84/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.84/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.25  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.84/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.25  
% 1.87/1.26  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 1.87/1.26  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.87/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.87/1.26  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.87/1.26  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.87/1.26  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 1.87/1.26  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.87/1.26  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.26  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.26  tff(c_32, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, k4_xboole_0(C_23, B_24)) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.26  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.26  tff(c_35, plain, (![C_23, B_24, A_22]: (r1_xboole_0(k4_xboole_0(C_23, B_24), A_22) | ~r1_tarski(A_22, B_24))), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.87/1.26  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.26  tff(c_8, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.26  tff(c_12, plain, (![C_15, A_13, B_14]: (k7_relat_1(C_15, k6_subset_1(A_13, B_14))=k6_subset_1(C_15, k7_relat_1(C_15, B_14)) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.26  tff(c_55, plain, (![C_31, A_32, B_33]: (k7_relat_1(C_31, k4_xboole_0(A_32, B_33))=k4_xboole_0(C_31, k7_relat_1(C_31, B_33)) | ~r1_tarski(k1_relat_1(C_31), A_32) | ~v1_relat_1(C_31))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 1.87/1.26  tff(c_60, plain, (![C_34, B_35, B_36]: (k7_relat_1(C_34, k4_xboole_0(k2_xboole_0(k1_relat_1(C_34), B_35), B_36))=k4_xboole_0(C_34, k7_relat_1(C_34, B_36)) | ~v1_relat_1(C_34))), inference(resolution, [status(thm)], [c_4, c_55])).
% 1.87/1.26  tff(c_10, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.26  tff(c_97, plain, (![C_51, B_52, B_53, B_54]: (k7_relat_1(k4_xboole_0(C_51, k7_relat_1(C_51, B_52)), B_53)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_51), B_54), B_52), B_53) | ~v1_relat_1(C_51) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_60, c_10])).
% 1.87/1.26  tff(c_106, plain, (![C_55, B_56, A_57]: (k7_relat_1(k4_xboole_0(C_55, k7_relat_1(C_55, B_56)), A_57)=k1_xboole_0 | ~v1_relat_1(C_55) | ~r1_tarski(A_57, B_56))), inference(resolution, [status(thm)], [c_35, c_97])).
% 1.87/1.26  tff(c_14, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.26  tff(c_19, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 1.87/1.26  tff(c_126, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_19])).
% 1.87/1.26  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_126])).
% 1.87/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.26  
% 1.87/1.26  Inference rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Ref     : 0
% 1.87/1.27  #Sup     : 34
% 1.87/1.27  #Fact    : 0
% 1.87/1.27  #Define  : 0
% 1.87/1.27  #Split   : 0
% 1.87/1.27  #Chain   : 0
% 1.87/1.27  #Close   : 0
% 1.87/1.27  
% 1.87/1.27  Ordering : KBO
% 1.87/1.27  
% 1.87/1.27  Simplification rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Subsume      : 2
% 1.87/1.27  #Demod        : 5
% 1.87/1.27  #Tautology    : 7
% 1.87/1.27  #SimpNegUnit  : 0
% 1.87/1.27  #BackRed      : 0
% 1.87/1.27  
% 1.87/1.27  #Partial instantiations: 0
% 1.87/1.27  #Strategies tried      : 1
% 1.87/1.27  
% 1.87/1.27  Timing (in seconds)
% 1.87/1.27  ----------------------
% 1.87/1.27  Preprocessing        : 0.28
% 1.87/1.27  Parsing              : 0.15
% 1.87/1.27  CNF conversion       : 0.02
% 1.87/1.27  Main loop            : 0.14
% 1.87/1.27  Inferencing          : 0.06
% 1.87/1.27  Reduction            : 0.04
% 1.87/1.27  Demodulation         : 0.03
% 1.87/1.27  BG Simplification    : 0.01
% 1.87/1.27  Subsumption          : 0.03
% 1.87/1.27  Abstraction          : 0.01
% 1.87/1.27  MUC search           : 0.00
% 1.87/1.27  Cooper               : 0.00
% 1.87/1.27  Total                : 0.45
% 1.87/1.27  Index Insertion      : 0.00
% 1.87/1.27  Index Deletion       : 0.00
% 1.87/1.27  Index Matching       : 0.00
% 1.87/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
