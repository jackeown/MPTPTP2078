%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:36 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  57 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_10] :
      ( k7_relat_1(A_10,k1_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [C_7,A_5,B_6] :
      ( k6_subset_1(k7_relat_1(C_7,A_5),k7_relat_1(C_7,B_6)) = k7_relat_1(C_7,k6_subset_1(A_5,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [C_22,A_23,B_24] :
      ( k4_xboole_0(k7_relat_1(C_22,A_23),k7_relat_1(C_22,B_24)) = k7_relat_1(C_22,k4_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_127,plain,(
    ! [A_10,B_24] :
      ( k7_relat_1(A_10,k4_xboole_0(k1_relat_1(A_10),B_24)) = k4_xboole_0(A_10,k7_relat_1(A_10,B_24))
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_221,plain,(
    ! [B_31,A_32] :
      ( k4_xboole_0(k1_relat_1(B_31),k1_relat_1(k7_relat_1(B_31,A_32))) = k3_xboole_0(k1_relat_1(B_31),k4_xboole_0(k1_relat_1(B_31),A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_59])).

tff(c_12,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_12])).

tff(c_236,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_15])).

tff(c_255,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_236])).

tff(c_327,plain,
    ( k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_255])).

tff(c_329,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_332,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_329])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.11/1.30  
% 2.11/1.30  %Foreground sorts:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Background operators:
% 2.11/1.30  
% 2.11/1.30  
% 2.11/1.30  %Foreground operators:
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.11/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.30  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.11/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.30  
% 2.11/1.31  tff(f_46, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 2.11/1.31  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.11/1.31  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.11/1.31  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 2.11/1.31  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.11/1.31  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.11/1.31  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.31  tff(c_10, plain, (![A_10]: (k7_relat_1(A_10, k1_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.31  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.31  tff(c_6, plain, (![C_7, A_5, B_6]: (k6_subset_1(k7_relat_1(C_7, A_5), k7_relat_1(C_7, B_6))=k7_relat_1(C_7, k6_subset_1(A_5, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.31  tff(c_112, plain, (![C_22, A_23, B_24]: (k4_xboole_0(k7_relat_1(C_22, A_23), k7_relat_1(C_22, B_24))=k7_relat_1(C_22, k4_xboole_0(A_23, B_24)) | ~v1_relat_1(C_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 2.11/1.31  tff(c_127, plain, (![A_10, B_24]: (k7_relat_1(A_10, k4_xboole_0(k1_relat_1(A_10), B_24))=k4_xboole_0(A_10, k7_relat_1(A_10, B_24)) | ~v1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_112])).
% 2.11/1.31  tff(c_8, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.31  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.31  tff(c_35, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.31  tff(c_59, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k3_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_35])).
% 2.11/1.31  tff(c_221, plain, (![B_31, A_32]: (k4_xboole_0(k1_relat_1(B_31), k1_relat_1(k7_relat_1(B_31, A_32)))=k3_xboole_0(k1_relat_1(B_31), k4_xboole_0(k1_relat_1(B_31), A_32)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_8, c_59])).
% 2.11/1.31  tff(c_12, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.31  tff(c_15, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_12])).
% 2.11/1.31  tff(c_236, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_15])).
% 2.11/1.31  tff(c_255, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_236])).
% 2.11/1.31  tff(c_327, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_255])).
% 2.11/1.31  tff(c_329, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_327])).
% 2.11/1.31  tff(c_332, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_329])).
% 2.11/1.31  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_332])).
% 2.11/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  Inference rules
% 2.11/1.31  ----------------------
% 2.11/1.31  #Ref     : 0
% 2.11/1.31  #Sup     : 83
% 2.11/1.31  #Fact    : 0
% 2.11/1.31  #Define  : 0
% 2.11/1.31  #Split   : 0
% 2.11/1.31  #Chain   : 0
% 2.11/1.31  #Close   : 0
% 2.11/1.31  
% 2.11/1.31  Ordering : KBO
% 2.11/1.31  
% 2.11/1.31  Simplification rules
% 2.11/1.31  ----------------------
% 2.11/1.31  #Subsume      : 0
% 2.11/1.31  #Demod        : 27
% 2.11/1.31  #Tautology    : 30
% 2.11/1.31  #SimpNegUnit  : 0
% 2.11/1.31  #BackRed      : 0
% 2.11/1.31  
% 2.11/1.31  #Partial instantiations: 0
% 2.11/1.31  #Strategies tried      : 1
% 2.11/1.31  
% 2.11/1.31  Timing (in seconds)
% 2.11/1.31  ----------------------
% 2.11/1.31  Preprocessing        : 0.28
% 2.11/1.31  Parsing              : 0.16
% 2.11/1.31  CNF conversion       : 0.01
% 2.11/1.31  Main loop            : 0.21
% 2.11/1.31  Inferencing          : 0.09
% 2.11/1.31  Reduction            : 0.07
% 2.11/1.31  Demodulation         : 0.05
% 2.11/1.31  BG Simplification    : 0.02
% 2.11/1.31  Subsumption          : 0.03
% 2.11/1.31  Abstraction          : 0.02
% 2.11/1.31  MUC search           : 0.00
% 2.11/1.31  Cooper               : 0.00
% 2.11/1.31  Total                : 0.52
% 2.11/1.31  Index Insertion      : 0.00
% 2.11/1.31  Index Deletion       : 0.00
% 2.11/1.31  Index Matching       : 0.00
% 2.11/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
