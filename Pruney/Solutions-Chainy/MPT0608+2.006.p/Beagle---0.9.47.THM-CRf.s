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
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  52 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(C_15,k6_subset_1(A_13,B_14)) = k6_subset_1(C_15,k7_relat_1(C_15,B_14))
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_326,plain,(
    ! [C_46,A_47,B_48] :
      ( k7_relat_1(C_46,k4_xboole_0(A_47,B_48)) = k4_xboole_0(C_46,k7_relat_1(C_46,B_48))
      | ~ r1_tarski(k1_relat_1(C_46),A_47)
      | ~ v1_relat_1(C_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_18])).

tff(c_332,plain,(
    ! [C_46,B_48] :
      ( k7_relat_1(C_46,k4_xboole_0(k1_relat_1(C_46),B_48)) = k4_xboole_0(C_46,k7_relat_1(C_46,B_48))
      | ~ v1_relat_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_326])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_9,B_10] : k3_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k4_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_203,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(k1_relat_1(B_39),A_40) = k1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_270,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,k1_relat_1(B_45)) = k1_relat_1(k7_relat_1(B_45,A_44))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_470,plain,(
    ! [B_61,B_62] :
      ( k1_relat_1(k7_relat_1(B_61,k4_xboole_0(k1_relat_1(B_61),B_62))) = k4_xboole_0(k1_relat_1(B_61),B_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_270])).

tff(c_637,plain,(
    ! [C_65,B_66] :
      ( k1_relat_1(k4_xboole_0(C_65,k7_relat_1(C_65,B_66))) = k4_xboole_0(k1_relat_1(C_65),B_66)
      | ~ v1_relat_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_470])).

tff(c_22,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_669,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_25])).

tff(c_680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.32  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.57/1.32  
% 2.57/1.32  %Foreground sorts:
% 2.57/1.32  
% 2.57/1.32  
% 2.57/1.32  %Background operators:
% 2.57/1.32  
% 2.57/1.32  
% 2.57/1.32  %Foreground operators:
% 2.57/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.57/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.32  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.57/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.32  
% 2.57/1.33  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.57/1.33  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.33  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.57/1.33  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.57/1.33  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.57/1.33  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.57/1.33  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.57/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.57/1.33  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.33  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.33  tff(c_18, plain, (![C_15, A_13, B_14]: (k7_relat_1(C_15, k6_subset_1(A_13, B_14))=k6_subset_1(C_15, k7_relat_1(C_15, B_14)) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.33  tff(c_326, plain, (![C_46, A_47, B_48]: (k7_relat_1(C_46, k4_xboole_0(A_47, B_48))=k4_xboole_0(C_46, k7_relat_1(C_46, B_48)) | ~r1_tarski(k1_relat_1(C_46), A_47) | ~v1_relat_1(C_46))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_18])).
% 2.57/1.33  tff(c_332, plain, (![C_46, B_48]: (k7_relat_1(C_46, k4_xboole_0(k1_relat_1(C_46), B_48))=k4_xboole_0(C_46, k7_relat_1(C_46, B_48)) | ~v1_relat_1(C_46))), inference(resolution, [status(thm)], [c_8, c_326])).
% 2.57/1.33  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.33  tff(c_72, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.33  tff(c_79, plain, (![A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k4_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_72])).
% 2.57/1.33  tff(c_203, plain, (![B_39, A_40]: (k3_xboole_0(k1_relat_1(B_39), A_40)=k1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.33  tff(c_270, plain, (![A_44, B_45]: (k3_xboole_0(A_44, k1_relat_1(B_45))=k1_relat_1(k7_relat_1(B_45, A_44)) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 2.57/1.33  tff(c_470, plain, (![B_61, B_62]: (k1_relat_1(k7_relat_1(B_61, k4_xboole_0(k1_relat_1(B_61), B_62)))=k4_xboole_0(k1_relat_1(B_61), B_62) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_79, c_270])).
% 2.57/1.33  tff(c_637, plain, (![C_65, B_66]: (k1_relat_1(k4_xboole_0(C_65, k7_relat_1(C_65, B_66)))=k4_xboole_0(k1_relat_1(C_65), B_66) | ~v1_relat_1(C_65) | ~v1_relat_1(C_65))), inference(superposition, [status(thm), theory('equality')], [c_332, c_470])).
% 2.57/1.33  tff(c_22, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.33  tff(c_25, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 2.57/1.33  tff(c_669, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_637, c_25])).
% 2.57/1.33  tff(c_680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_669])).
% 2.57/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  Inference rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Ref     : 0
% 2.57/1.33  #Sup     : 174
% 2.57/1.33  #Fact    : 0
% 2.57/1.33  #Define  : 0
% 2.57/1.33  #Split   : 0
% 2.57/1.33  #Chain   : 0
% 2.57/1.33  #Close   : 0
% 2.57/1.33  
% 2.57/1.33  Ordering : KBO
% 2.57/1.33  
% 2.57/1.33  Simplification rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Subsume      : 21
% 2.57/1.33  #Demod        : 50
% 2.57/1.33  #Tautology    : 81
% 2.57/1.33  #SimpNegUnit  : 0
% 2.57/1.33  #BackRed      : 0
% 2.57/1.33  
% 2.57/1.33  #Partial instantiations: 0
% 2.57/1.33  #Strategies tried      : 1
% 2.57/1.33  
% 2.57/1.33  Timing (in seconds)
% 2.57/1.33  ----------------------
% 2.57/1.33  Preprocessing        : 0.29
% 2.57/1.33  Parsing              : 0.16
% 2.57/1.33  CNF conversion       : 0.02
% 2.57/1.34  Main loop            : 0.30
% 2.57/1.34  Inferencing          : 0.12
% 2.57/1.34  Reduction            : 0.10
% 2.57/1.34  Demodulation         : 0.07
% 2.57/1.34  BG Simplification    : 0.02
% 2.57/1.34  Subsumption          : 0.05
% 2.57/1.34  Abstraction          : 0.02
% 2.57/1.34  MUC search           : 0.00
% 2.57/1.34  Cooper               : 0.00
% 2.57/1.34  Total                : 0.62
% 2.57/1.34  Index Insertion      : 0.00
% 2.57/1.34  Index Deletion       : 0.00
% 2.57/1.34  Index Matching       : 0.00
% 2.57/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
