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
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 12.60s
% Output     : CNFRefutation 12.60s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  67 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_xboole_0(A_25,k4_xboole_0(C_26,B_27))
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [C_26,B_27,A_25] :
      ( r1_xboole_0(k4_xboole_0(C_26,B_27),A_25)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [B_31,A_32] :
      ( k7_relat_1(B_31,A_32) = B_31
      | ~ r1_tarski(k1_relat_1(B_31),A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    ! [B_31] :
      ( k7_relat_1(B_31,k1_relat_1(B_31)) = B_31
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_12,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( k6_subset_1(k7_relat_1(C_12,A_10),k7_relat_1(C_12,B_11)) = k7_relat_1(C_12,k6_subset_1(A_10,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [C_39,A_40,B_41] :
      ( k4_xboole_0(k7_relat_1(C_39,A_40),k7_relat_1(C_39,B_41)) = k7_relat_1(C_39,k4_xboole_0(A_40,B_41))
      | ~ v1_relat_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_14])).

tff(c_857,plain,(
    ! [B_112,B_113] :
      ( k7_relat_1(B_112,k4_xboole_0(k1_relat_1(B_112),B_113)) = k4_xboole_0(B_112,k7_relat_1(B_112,B_113))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_105])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13934,plain,(
    ! [B_584,B_585,B_586] :
      ( k7_relat_1(k4_xboole_0(B_584,k7_relat_1(B_584,B_585)),B_586) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(B_584),B_585),B_586)
      | ~ v1_relat_1(B_584)
      | ~ v1_relat_1(B_584)
      | ~ v1_relat_1(B_584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_16])).

tff(c_14006,plain,(
    ! [B_587,B_588,A_589] :
      ( k7_relat_1(k4_xboole_0(B_587,k7_relat_1(B_587,B_588)),A_589) = k1_xboole_0
      | ~ v1_relat_1(B_587)
      | ~ r1_tarski(A_589,B_588) ) ),
    inference(resolution,[status(thm)],[c_53,c_13934])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_14616,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14006,c_25])).

tff(c_14722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_14616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.60/5.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.60/5.34  
% 12.60/5.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.60/5.34  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.60/5.34  
% 12.60/5.34  %Foreground sorts:
% 12.60/5.34  
% 12.60/5.34  
% 12.60/5.34  %Background operators:
% 12.60/5.34  
% 12.60/5.34  
% 12.60/5.34  %Foreground operators:
% 12.60/5.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.60/5.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.60/5.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.60/5.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.60/5.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.60/5.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.60/5.34  tff('#skF_2', type, '#skF_2': $i).
% 12.60/5.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.60/5.34  tff('#skF_3', type, '#skF_3': $i).
% 12.60/5.34  tff('#skF_1', type, '#skF_1': $i).
% 12.60/5.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.60/5.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.60/5.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.60/5.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.60/5.34  
% 12.60/5.35  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 12.60/5.35  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 12.60/5.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.60/5.35  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.60/5.35  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 12.60/5.35  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.60/5.35  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 12.60/5.35  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 12.60/5.35  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.60/5.35  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.60/5.35  tff(c_50, plain, (![A_25, C_26, B_27]: (r1_xboole_0(A_25, k4_xboole_0(C_26, B_27)) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.60/5.35  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.60/5.35  tff(c_53, plain, (![C_26, B_27, A_25]: (r1_xboole_0(k4_xboole_0(C_26, B_27), A_25) | ~r1_tarski(A_25, B_27))), inference(resolution, [status(thm)], [c_50, c_2])).
% 12.60/5.35  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.60/5.35  tff(c_58, plain, (![B_31, A_32]: (k7_relat_1(B_31, A_32)=B_31 | ~r1_tarski(k1_relat_1(B_31), A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.60/5.35  tff(c_63, plain, (![B_31]: (k7_relat_1(B_31, k1_relat_1(B_31))=B_31 | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_8, c_58])).
% 12.60/5.35  tff(c_12, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.60/5.35  tff(c_14, plain, (![C_12, A_10, B_11]: (k6_subset_1(k7_relat_1(C_12, A_10), k7_relat_1(C_12, B_11))=k7_relat_1(C_12, k6_subset_1(A_10, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.60/5.35  tff(c_105, plain, (![C_39, A_40, B_41]: (k4_xboole_0(k7_relat_1(C_39, A_40), k7_relat_1(C_39, B_41))=k7_relat_1(C_39, k4_xboole_0(A_40, B_41)) | ~v1_relat_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_14])).
% 12.60/5.35  tff(c_857, plain, (![B_112, B_113]: (k7_relat_1(B_112, k4_xboole_0(k1_relat_1(B_112), B_113))=k4_xboole_0(B_112, k7_relat_1(B_112, B_113)) | ~v1_relat_1(B_112) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_63, c_105])).
% 12.60/5.35  tff(c_16, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.60/5.35  tff(c_13934, plain, (![B_584, B_585, B_586]: (k7_relat_1(k4_xboole_0(B_584, k7_relat_1(B_584, B_585)), B_586)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(B_584), B_585), B_586) | ~v1_relat_1(B_584) | ~v1_relat_1(B_584) | ~v1_relat_1(B_584))), inference(superposition, [status(thm), theory('equality')], [c_857, c_16])).
% 12.60/5.35  tff(c_14006, plain, (![B_587, B_588, A_589]: (k7_relat_1(k4_xboole_0(B_587, k7_relat_1(B_587, B_588)), A_589)=k1_xboole_0 | ~v1_relat_1(B_587) | ~r1_tarski(A_589, B_588))), inference(resolution, [status(thm)], [c_53, c_13934])).
% 12.60/5.35  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.60/5.35  tff(c_25, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 12.60/5.35  tff(c_14616, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14006, c_25])).
% 12.60/5.35  tff(c_14722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_14616])).
% 12.60/5.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.60/5.35  
% 12.60/5.35  Inference rules
% 12.60/5.35  ----------------------
% 12.60/5.35  #Ref     : 0
% 12.60/5.35  #Sup     : 4616
% 12.60/5.35  #Fact    : 0
% 12.60/5.35  #Define  : 0
% 12.60/5.35  #Split   : 18
% 12.60/5.35  #Chain   : 0
% 12.60/5.35  #Close   : 0
% 12.60/5.35  
% 12.60/5.35  Ordering : KBO
% 12.60/5.35  
% 12.60/5.35  Simplification rules
% 12.60/5.35  ----------------------
% 12.60/5.35  #Subsume      : 1476
% 12.60/5.35  #Demod        : 70
% 12.60/5.35  #Tautology    : 135
% 12.60/5.35  #SimpNegUnit  : 0
% 12.60/5.35  #BackRed      : 0
% 12.60/5.35  
% 12.60/5.35  #Partial instantiations: 0
% 12.60/5.35  #Strategies tried      : 1
% 12.60/5.35  
% 12.60/5.35  Timing (in seconds)
% 12.60/5.35  ----------------------
% 12.60/5.35  Preprocessing        : 0.30
% 12.60/5.35  Parsing              : 0.15
% 12.60/5.35  CNF conversion       : 0.02
% 12.60/5.35  Main loop            : 4.30
% 12.60/5.35  Inferencing          : 1.04
% 12.60/5.35  Reduction            : 0.71
% 12.60/5.35  Demodulation         : 0.49
% 12.60/5.35  BG Simplification    : 0.15
% 12.60/5.35  Subsumption          : 2.21
% 12.60/5.35  Abstraction          : 0.18
% 12.60/5.35  MUC search           : 0.00
% 12.60/5.35  Cooper               : 0.00
% 12.60/5.35  Total                : 4.62
% 12.60/5.35  Index Insertion      : 0.00
% 12.60/5.35  Index Deletion       : 0.00
% 12.60/5.35  Index Matching       : 0.00
% 12.60/5.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
