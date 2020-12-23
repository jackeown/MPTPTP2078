%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:31 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_552,plain,(
    ! [C_57,A_58,B_59] :
      ( k7_relat_1(C_57,k4_xboole_0(A_58,B_59)) = k4_xboole_0(C_57,k7_relat_1(C_57,B_59))
      | ~ r1_tarski(k1_relat_1(C_57),A_58)
      | ~ v1_relat_1(C_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_563,plain,(
    ! [C_60,B_61] :
      ( k7_relat_1(C_60,k4_xboole_0(k1_relat_1(C_60),B_61)) = k4_xboole_0(C_60,k7_relat_1(C_60,B_61))
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_552])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k6_subset_1(k1_relat_1(B_14),A_13))) = k6_subset_1(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k4_xboole_0(k1_relat_1(B_14),A_13))) = k4_xboole_0(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_611,plain,(
    ! [C_62,B_63] :
      ( k1_relat_1(k4_xboole_0(C_62,k7_relat_1(C_62,B_63))) = k4_xboole_0(k1_relat_1(C_62),B_63)
      | ~ v1_relat_1(C_62)
      | ~ v1_relat_1(C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_29])).

tff(c_237,plain,(
    ! [B_41,A_42] :
      ( k3_xboole_0(k1_relat_1(B_41),A_42) = k1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_376,plain,(
    ! [B_51,A_52] :
      ( k4_xboole_0(k1_relat_1(B_51),k1_relat_1(k7_relat_1(B_51,A_52))) = k4_xboole_0(k1_relat_1(B_51),A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_10])).

tff(c_24,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_27,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_24])).

tff(c_389,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_27])).

tff(c_406,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_389])).

tff(c_631,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_406])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.33  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.37/1.33  
% 2.37/1.33  %Foreground sorts:
% 2.37/1.33  
% 2.37/1.33  
% 2.37/1.33  %Background operators:
% 2.37/1.33  
% 2.37/1.33  
% 2.37/1.33  %Foreground operators:
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.37/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.33  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.37/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.37/1.33  
% 2.37/1.34  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 2.37/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.37/1.34  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.37/1.34  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.37/1.34  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 2.37/1.34  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.37/1.34  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.37/1.34  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.34  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.34  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.37/1.34  tff(c_552, plain, (![C_57, A_58, B_59]: (k7_relat_1(C_57, k4_xboole_0(A_58, B_59))=k4_xboole_0(C_57, k7_relat_1(C_57, B_59)) | ~r1_tarski(k1_relat_1(C_57), A_58) | ~v1_relat_1(C_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 2.37/1.34  tff(c_563, plain, (![C_60, B_61]: (k7_relat_1(C_60, k4_xboole_0(k1_relat_1(C_60), B_61))=k4_xboole_0(C_60, k7_relat_1(C_60, B_61)) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_6, c_552])).
% 2.37/1.34  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k6_subset_1(k1_relat_1(B_14), A_13)))=k6_subset_1(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.37/1.34  tff(c_29, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k4_xboole_0(k1_relat_1(B_14), A_13)))=k4_xboole_0(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 2.37/1.34  tff(c_611, plain, (![C_62, B_63]: (k1_relat_1(k4_xboole_0(C_62, k7_relat_1(C_62, B_63)))=k4_xboole_0(k1_relat_1(C_62), B_63) | ~v1_relat_1(C_62) | ~v1_relat_1(C_62))), inference(superposition, [status(thm), theory('equality')], [c_563, c_29])).
% 2.37/1.34  tff(c_237, plain, (![B_41, A_42]: (k3_xboole_0(k1_relat_1(B_41), A_42)=k1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.34  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.34  tff(c_376, plain, (![B_51, A_52]: (k4_xboole_0(k1_relat_1(B_51), k1_relat_1(k7_relat_1(B_51, A_52)))=k4_xboole_0(k1_relat_1(B_51), A_52) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_237, c_10])).
% 2.37/1.34  tff(c_24, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.34  tff(c_27, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_24])).
% 2.37/1.34  tff(c_389, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_376, c_27])).
% 2.37/1.34  tff(c_406, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_389])).
% 2.37/1.34  tff(c_631, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_611, c_406])).
% 2.37/1.34  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_631])).
% 2.37/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  Inference rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Ref     : 0
% 2.37/1.34  #Sup     : 167
% 2.37/1.34  #Fact    : 0
% 2.37/1.34  #Define  : 0
% 2.37/1.34  #Split   : 0
% 2.37/1.34  #Chain   : 0
% 2.37/1.34  #Close   : 0
% 2.37/1.34  
% 2.37/1.34  Ordering : KBO
% 2.37/1.34  
% 2.37/1.34  Simplification rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Subsume      : 23
% 2.37/1.34  #Demod        : 21
% 2.37/1.34  #Tautology    : 75
% 2.37/1.34  #SimpNegUnit  : 0
% 2.37/1.34  #BackRed      : 0
% 2.37/1.34  
% 2.37/1.34  #Partial instantiations: 0
% 2.37/1.34  #Strategies tried      : 1
% 2.37/1.34  
% 2.37/1.34  Timing (in seconds)
% 2.37/1.34  ----------------------
% 2.37/1.35  Preprocessing        : 0.30
% 2.37/1.35  Parsing              : 0.16
% 2.37/1.35  CNF conversion       : 0.02
% 2.37/1.35  Main loop            : 0.27
% 2.37/1.35  Inferencing          : 0.11
% 2.37/1.35  Reduction            : 0.09
% 2.37/1.35  Demodulation         : 0.07
% 2.37/1.35  BG Simplification    : 0.02
% 2.37/1.35  Subsumption          : 0.04
% 2.37/1.35  Abstraction          : 0.02
% 2.37/1.35  MUC search           : 0.00
% 2.37/1.35  Cooper               : 0.00
% 2.37/1.35  Total                : 0.59
% 2.37/1.35  Index Insertion      : 0.00
% 2.37/1.35  Index Deletion       : 0.00
% 2.37/1.35  Index Matching       : 0.00
% 2.37/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
