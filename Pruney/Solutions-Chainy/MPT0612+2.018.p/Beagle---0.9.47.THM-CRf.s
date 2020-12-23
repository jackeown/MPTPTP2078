%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  60 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_xboole_0(A_23,k4_xboole_0(C_24,B_25))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [C_24,B_25,A_23] :
      ( r1_xboole_0(k4_xboole_0(C_24,B_25),A_23)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(C_15,k6_subset_1(A_13,B_14)) = k6_subset_1(C_15,k7_relat_1(C_15,B_14))
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [C_32,A_33,B_34] :
      ( k7_relat_1(C_32,k4_xboole_0(A_33,B_34)) = k4_xboole_0(C_32,k7_relat_1(C_32,B_34))
      | ~ r1_tarski(k1_relat_1(C_32),A_33)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_76,plain,(
    ! [C_35,B_36] :
      ( k7_relat_1(C_35,k4_xboole_0(k1_relat_1(C_35),B_36)) = k4_xboole_0(C_35,k7_relat_1(C_35,B_36))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [C_41,B_42,B_43] :
      ( k7_relat_1(k4_xboole_0(C_41,k7_relat_1(C_41,B_42)),B_43) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(C_41),B_42),B_43)
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_112,plain,(
    ! [C_44,B_45,A_46] :
      ( k7_relat_1(k4_xboole_0(C_44,k7_relat_1(C_44,B_45)),A_46) = k1_xboole_0
      | ~ v1_relat_1(C_44)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(resolution,[status(thm)],[c_51,c_103])).

tff(c_18,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_128,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_23])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.70/1.17  
% 1.70/1.17  %Foreground sorts:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Background operators:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Foreground operators:
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.70/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.70/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.17  
% 1.93/1.18  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 1.93/1.18  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.93/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.93/1.18  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.18  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.93/1.18  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 1.93/1.18  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.93/1.18  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.18  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.18  tff(c_48, plain, (![A_23, C_24, B_25]: (r1_xboole_0(A_23, k4_xboole_0(C_24, B_25)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.18  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.18  tff(c_51, plain, (![C_24, B_25, A_23]: (r1_xboole_0(k4_xboole_0(C_24, B_25), A_23) | ~r1_tarski(A_23, B_25))), inference(resolution, [status(thm)], [c_48, c_2])).
% 1.93/1.18  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.18  tff(c_12, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.18  tff(c_16, plain, (![C_15, A_13, B_14]: (k7_relat_1(C_15, k6_subset_1(A_13, B_14))=k6_subset_1(C_15, k7_relat_1(C_15, B_14)) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.18  tff(c_71, plain, (![C_32, A_33, B_34]: (k7_relat_1(C_32, k4_xboole_0(A_33, B_34))=k4_xboole_0(C_32, k7_relat_1(C_32, B_34)) | ~r1_tarski(k1_relat_1(C_32), A_33) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 1.93/1.18  tff(c_76, plain, (![C_35, B_36]: (k7_relat_1(C_35, k4_xboole_0(k1_relat_1(C_35), B_36))=k4_xboole_0(C_35, k7_relat_1(C_35, B_36)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_8, c_71])).
% 1.93/1.18  tff(c_14, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.18  tff(c_103, plain, (![C_41, B_42, B_43]: (k7_relat_1(k4_xboole_0(C_41, k7_relat_1(C_41, B_42)), B_43)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(C_41), B_42), B_43) | ~v1_relat_1(C_41) | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_76, c_14])).
% 1.93/1.18  tff(c_112, plain, (![C_44, B_45, A_46]: (k7_relat_1(k4_xboole_0(C_44, k7_relat_1(C_44, B_45)), A_46)=k1_xboole_0 | ~v1_relat_1(C_44) | ~r1_tarski(A_46, B_45))), inference(resolution, [status(thm)], [c_51, c_103])).
% 1.93/1.18  tff(c_18, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.18  tff(c_23, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 1.93/1.18  tff(c_128, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_112, c_23])).
% 1.93/1.18  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_128])).
% 1.93/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.18  
% 1.93/1.18  Inference rules
% 1.93/1.18  ----------------------
% 1.93/1.18  #Ref     : 0
% 1.93/1.18  #Sup     : 30
% 1.93/1.18  #Fact    : 0
% 1.93/1.18  #Define  : 0
% 1.93/1.18  #Split   : 1
% 1.93/1.18  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 2
% 1.93/1.19  #Demod        : 7
% 1.93/1.19  #Tautology    : 9
% 1.93/1.19  #SimpNegUnit  : 0
% 1.93/1.19  #BackRed      : 0
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.19  Preprocessing        : 0.28
% 1.93/1.19  Parsing              : 0.15
% 1.93/1.19  CNF conversion       : 0.02
% 1.93/1.19  Main loop            : 0.14
% 1.93/1.19  Inferencing          : 0.05
% 1.93/1.19  Reduction            : 0.04
% 1.93/1.19  Demodulation         : 0.03
% 1.93/1.19  BG Simplification    : 0.01
% 1.93/1.19  Subsumption          : 0.03
% 1.93/1.19  Abstraction          : 0.01
% 1.93/1.19  MUC search           : 0.00
% 1.93/1.19  Cooper               : 0.00
% 1.93/1.19  Total                : 0.44
% 1.93/1.19  Index Insertion      : 0.00
% 1.93/1.19  Index Deletion       : 0.00
% 1.93/1.19  Index Matching       : 0.00
% 1.93/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
