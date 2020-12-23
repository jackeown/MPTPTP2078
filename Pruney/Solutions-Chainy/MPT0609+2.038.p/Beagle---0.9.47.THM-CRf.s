%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   38 (  51 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  58 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( k6_subset_1(k7_relat_1(C_9,A_7),k7_relat_1(C_9,B_8)) = k7_relat_1(C_9,k6_subset_1(A_7,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [C_28,A_29,B_30] :
      ( k4_xboole_0(k7_relat_1(C_28,A_29),k7_relat_1(C_28,B_30)) = k7_relat_1(C_28,k4_xboole_0(A_29,B_30))
      | ~ v1_relat_1(C_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_8])).

tff(c_139,plain,(
    ! [A_31,B_32] :
      ( k7_relat_1(A_31,k4_xboole_0(k1_relat_1(A_31),B_32)) = k4_xboole_0(A_31,k7_relat_1(A_31,B_32))
      | ~ v1_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_124])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,k6_subset_1(k1_relat_1(B_11),A_10))) = k6_subset_1(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,k4_xboole_0(k1_relat_1(B_11),A_10))) = k4_xboole_0(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_10])).

tff(c_206,plain,(
    ! [A_35,B_36] :
      ( k1_relat_1(k4_xboole_0(A_35,k7_relat_1(A_35,B_36))) = k4_xboole_0(k1_relat_1(A_35),B_36)
      | ~ v1_relat_1(A_35)
      | ~ v1_relat_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_20])).

tff(c_58,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(k1_relat_1(B_22),A_23) = k1_relat_1(k7_relat_1(B_22,A_23))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [B_26,A_27] :
      ( k4_xboole_0(k1_relat_1(B_26),k1_relat_1(k7_relat_1(B_26,A_27))) = k4_xboole_0(k1_relat_1(B_26),A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2])).

tff(c_16,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_16])).

tff(c_102,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_19])).

tff(c_120,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_218,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_120])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.16  
% 1.92/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.17  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.17  
% 1.92/1.17  %Foreground sorts:
% 1.92/1.17  
% 1.92/1.17  
% 1.92/1.17  %Background operators:
% 1.92/1.17  
% 1.92/1.17  
% 1.92/1.17  %Foreground operators:
% 1.92/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.92/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.17  
% 1.92/1.18  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 1.92/1.18  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.92/1.18  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.92/1.18  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 1.92/1.18  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 1.92/1.18  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.92/1.18  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.92/1.18  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.18  tff(c_14, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.18  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.18  tff(c_8, plain, (![C_9, A_7, B_8]: (k6_subset_1(k7_relat_1(C_9, A_7), k7_relat_1(C_9, B_8))=k7_relat_1(C_9, k6_subset_1(A_7, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.18  tff(c_124, plain, (![C_28, A_29, B_30]: (k4_xboole_0(k7_relat_1(C_28, A_29), k7_relat_1(C_28, B_30))=k7_relat_1(C_28, k4_xboole_0(A_29, B_30)) | ~v1_relat_1(C_28))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_8])).
% 1.92/1.18  tff(c_139, plain, (![A_31, B_32]: (k7_relat_1(A_31, k4_xboole_0(k1_relat_1(A_31), B_32))=k4_xboole_0(A_31, k7_relat_1(A_31, B_32)) | ~v1_relat_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_124])).
% 1.92/1.18  tff(c_10, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, k6_subset_1(k1_relat_1(B_11), A_10)))=k6_subset_1(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.18  tff(c_20, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, k4_xboole_0(k1_relat_1(B_11), A_10)))=k4_xboole_0(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_10])).
% 1.92/1.18  tff(c_206, plain, (![A_35, B_36]: (k1_relat_1(k4_xboole_0(A_35, k7_relat_1(A_35, B_36)))=k4_xboole_0(k1_relat_1(A_35), B_36) | ~v1_relat_1(A_35) | ~v1_relat_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_139, c_20])).
% 1.92/1.18  tff(c_58, plain, (![B_22, A_23]: (k3_xboole_0(k1_relat_1(B_22), A_23)=k1_relat_1(k7_relat_1(B_22, A_23)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.18  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.18  tff(c_96, plain, (![B_26, A_27]: (k4_xboole_0(k1_relat_1(B_26), k1_relat_1(k7_relat_1(B_26, A_27)))=k4_xboole_0(k1_relat_1(B_26), A_27) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_58, c_2])).
% 1.92/1.18  tff(c_16, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.18  tff(c_19, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_16])).
% 1.92/1.18  tff(c_102, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_96, c_19])).
% 1.92/1.18  tff(c_120, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_102])).
% 1.92/1.18  tff(c_218, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_206, c_120])).
% 1.92/1.18  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_218])).
% 1.92/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  Inference rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Ref     : 0
% 1.92/1.18  #Sup     : 60
% 1.92/1.18  #Fact    : 0
% 1.92/1.18  #Define  : 0
% 1.92/1.18  #Split   : 0
% 1.92/1.18  #Chain   : 0
% 1.92/1.18  #Close   : 0
% 1.92/1.18  
% 1.92/1.18  Ordering : KBO
% 1.92/1.18  
% 1.92/1.18  Simplification rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Subsume      : 1
% 1.92/1.18  #Demod        : 9
% 1.92/1.18  #Tautology    : 23
% 1.92/1.18  #SimpNegUnit  : 0
% 1.92/1.18  #BackRed      : 0
% 1.92/1.18  
% 1.92/1.18  #Partial instantiations: 0
% 1.92/1.18  #Strategies tried      : 1
% 1.92/1.18  
% 1.92/1.18  Timing (in seconds)
% 1.92/1.18  ----------------------
% 2.04/1.18  Preprocessing        : 0.30
% 2.04/1.18  Parsing              : 0.17
% 2.04/1.18  CNF conversion       : 0.02
% 2.04/1.18  Main loop            : 0.18
% 2.04/1.18  Inferencing          : 0.08
% 2.04/1.18  Reduction            : 0.05
% 2.04/1.18  Demodulation         : 0.04
% 2.04/1.18  BG Simplification    : 0.02
% 2.04/1.18  Subsumption          : 0.03
% 2.04/1.18  Abstraction          : 0.02
% 2.04/1.18  MUC search           : 0.00
% 2.04/1.18  Cooper               : 0.00
% 2.04/1.18  Total                : 0.50
% 2.04/1.18  Index Insertion      : 0.00
% 2.04/1.18  Index Deletion       : 0.00
% 2.04/1.18  Index Matching       : 0.00
% 2.04/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
