%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:33 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
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
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(C_19,k6_subset_1(A_17,B_18)) = k6_subset_1(C_19,k7_relat_1(C_19,B_18))
      | ~ r1_tarski(k1_relat_1(C_19),A_17)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_358,plain,(
    ! [C_53,A_54,B_55] :
      ( k7_relat_1(C_53,k4_xboole_0(A_54,B_55)) = k4_xboole_0(C_53,k7_relat_1(C_53,B_55))
      | ~ r1_tarski(k1_relat_1(C_53),A_54)
      | ~ v1_relat_1(C_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_365,plain,(
    ! [C_56,B_57] :
      ( k7_relat_1(C_56,k4_xboole_0(k1_relat_1(C_56),B_57)) = k4_xboole_0(C_56,k7_relat_1(C_56,B_57))
      | ~ v1_relat_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_8,c_358])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,k6_subset_1(k1_relat_1(B_16),A_15))) = k6_subset_1(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,k4_xboole_0(k1_relat_1(B_16),A_15))) = k4_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_559,plain,(
    ! [C_62,B_63] :
      ( k1_relat_1(k4_xboole_0(C_62,k7_relat_1(C_62,B_63))) = k4_xboole_0(k1_relat_1(C_62),B_63)
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_31])).

tff(c_187,plain,(
    ! [B_41,A_42] :
      ( k3_xboole_0(k1_relat_1(B_41),A_42) = k1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_324,plain,(
    ! [B_51,A_52] :
      ( k4_xboole_0(k1_relat_1(B_51),k1_relat_1(k7_relat_1(B_51,A_52))) = k4_xboole_0(k1_relat_1(B_51),A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_12])).

tff(c_26,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_26])).

tff(c_337,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_29])).

tff(c_354,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_337])).

tff(c_577,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_354])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.77  
% 2.77/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.78  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.77/1.78  
% 2.77/1.78  %Foreground sorts:
% 2.77/1.78  
% 2.77/1.78  
% 2.77/1.78  %Background operators:
% 2.77/1.78  
% 2.77/1.78  
% 2.77/1.78  %Foreground operators:
% 2.77/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.77/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.78  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.78  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.77/1.78  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.78  
% 3.07/1.79  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 3.07/1.79  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.79  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.07/1.79  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 3.07/1.79  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 3.07/1.79  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.07/1.79  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.07/1.79  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.79  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.79  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.07/1.79  tff(c_22, plain, (![C_19, A_17, B_18]: (k7_relat_1(C_19, k6_subset_1(A_17, B_18))=k6_subset_1(C_19, k7_relat_1(C_19, B_18)) | ~r1_tarski(k1_relat_1(C_19), A_17) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.07/1.79  tff(c_358, plain, (![C_53, A_54, B_55]: (k7_relat_1(C_53, k4_xboole_0(A_54, B_55))=k4_xboole_0(C_53, k7_relat_1(C_53, B_55)) | ~r1_tarski(k1_relat_1(C_53), A_54) | ~v1_relat_1(C_53))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 3.07/1.79  tff(c_365, plain, (![C_56, B_57]: (k7_relat_1(C_56, k4_xboole_0(k1_relat_1(C_56), B_57))=k4_xboole_0(C_56, k7_relat_1(C_56, B_57)) | ~v1_relat_1(C_56))), inference(resolution, [status(thm)], [c_8, c_358])).
% 3.07/1.79  tff(c_20, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, k6_subset_1(k1_relat_1(B_16), A_15)))=k6_subset_1(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.79  tff(c_31, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, k4_xboole_0(k1_relat_1(B_16), A_15)))=k4_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 3.07/1.79  tff(c_559, plain, (![C_62, B_63]: (k1_relat_1(k4_xboole_0(C_62, k7_relat_1(C_62, B_63)))=k4_xboole_0(k1_relat_1(C_62), B_63) | ~v1_relat_1(C_62) | ~v1_relat_1(C_62))), inference(superposition, [status(thm), theory('equality')], [c_365, c_31])).
% 3.07/1.79  tff(c_187, plain, (![B_41, A_42]: (k3_xboole_0(k1_relat_1(B_41), A_42)=k1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.07/1.79  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.79  tff(c_324, plain, (![B_51, A_52]: (k4_xboole_0(k1_relat_1(B_51), k1_relat_1(k7_relat_1(B_51, A_52)))=k4_xboole_0(k1_relat_1(B_51), A_52) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_187, c_12])).
% 3.07/1.79  tff(c_26, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.79  tff(c_29, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_26])).
% 3.07/1.79  tff(c_337, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_324, c_29])).
% 3.07/1.79  tff(c_354, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_337])).
% 3.07/1.79  tff(c_577, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_559, c_354])).
% 3.07/1.79  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_577])).
% 3.07/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.79  
% 3.07/1.79  Inference rules
% 3.07/1.79  ----------------------
% 3.07/1.79  #Ref     : 0
% 3.07/1.79  #Sup     : 153
% 3.07/1.79  #Fact    : 0
% 3.07/1.79  #Define  : 0
% 3.07/1.79  #Split   : 0
% 3.07/1.79  #Chain   : 0
% 3.07/1.79  #Close   : 0
% 3.07/1.79  
% 3.07/1.79  Ordering : KBO
% 3.07/1.79  
% 3.07/1.79  Simplification rules
% 3.11/1.79  ----------------------
% 3.11/1.79  #Subsume      : 21
% 3.11/1.79  #Demod        : 18
% 3.11/1.79  #Tautology    : 64
% 3.11/1.79  #SimpNegUnit  : 0
% 3.11/1.79  #BackRed      : 0
% 3.11/1.79  
% 3.11/1.79  #Partial instantiations: 0
% 3.11/1.79  #Strategies tried      : 1
% 3.11/1.79  
% 3.11/1.79  Timing (in seconds)
% 3.11/1.79  ----------------------
% 3.11/1.80  Preprocessing        : 0.47
% 3.11/1.80  Parsing              : 0.25
% 3.11/1.80  CNF conversion       : 0.02
% 3.11/1.80  Main loop            : 0.44
% 3.11/1.80  Inferencing          : 0.17
% 3.11/1.80  Reduction            : 0.14
% 3.11/1.80  Demodulation         : 0.11
% 3.11/1.80  BG Simplification    : 0.03
% 3.11/1.80  Subsumption          : 0.07
% 3.11/1.80  Abstraction          : 0.04
% 3.11/1.80  MUC search           : 0.00
% 3.11/1.80  Cooper               : 0.00
% 3.11/1.80  Total                : 0.95
% 3.11/1.80  Index Insertion      : 0.00
% 3.11/1.80  Index Deletion       : 0.00
% 3.11/1.80  Index Matching       : 0.00
% 3.11/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
