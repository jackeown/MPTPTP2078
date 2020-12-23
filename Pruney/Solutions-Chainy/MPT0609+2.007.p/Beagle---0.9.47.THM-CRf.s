%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:31 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  68 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k6_subset_1(B_12,k7_relat_1(B_12,A_11))) = k6_subset_1(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k4_xboole_0(B_12,k7_relat_1(B_12,A_11))) = k4_xboole_0(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_27,A_28] : k1_setfam_1(k2_tarski(B_27,A_28)) = k3_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_10,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_181,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_33,A_34)),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_33,A_34)),k1_relat_1(B_33)) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_302,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(k1_relat_1(B_45),k1_relat_1(k7_relat_1(B_45,A_46))) = k1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_184])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_575,plain,(
    ! [B_56,A_57] :
      ( k5_xboole_0(k1_relat_1(B_56),k1_relat_1(k7_relat_1(B_56,A_57))) = k4_xboole_0(k1_relat_1(B_56),k1_relat_1(k7_relat_1(B_56,A_57)))
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_2])).

tff(c_187,plain,(
    ! [B_35,A_36] :
      ( k3_xboole_0(k1_relat_1(B_35),A_36) = k1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_202,plain,(
    ! [B_35,A_36] :
      ( k5_xboole_0(k1_relat_1(B_35),k1_relat_1(k7_relat_1(B_35,A_36))) = k4_xboole_0(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2])).

tff(c_619,plain,(
    ! [B_58,A_59] :
      ( k4_xboole_0(k1_relat_1(B_58),k1_relat_1(k7_relat_1(B_58,A_59))) = k4_xboole_0(k1_relat_1(B_58),A_59)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_202])).

tff(c_18,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_21,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_18])).

tff(c_628,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_21])).

tff(c_655,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_628])).

tff(c_660,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_655])).

tff(c_664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.34  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.43/1.34  
% 2.43/1.34  %Foreground sorts:
% 2.43/1.34  
% 2.43/1.34  
% 2.43/1.34  %Background operators:
% 2.43/1.34  
% 2.43/1.34  
% 2.43/1.34  %Foreground operators:
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.43/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.43/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.43/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.43/1.34  
% 2.43/1.35  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.43/1.35  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.43/1.35  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.43/1.35  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.43/1.35  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.43/1.35  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 2.43/1.35  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.43/1.35  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.43/1.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.43/1.35  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.35  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.35  tff(c_12, plain, (![B_12, A_11]: (k1_relat_1(k6_subset_1(B_12, k7_relat_1(B_12, A_11)))=k6_subset_1(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.35  tff(c_22, plain, (![B_12, A_11]: (k1_relat_1(k4_xboole_0(B_12, k7_relat_1(B_12, A_11)))=k4_xboole_0(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 2.43/1.35  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.35  tff(c_66, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.35  tff(c_90, plain, (![B_27, A_28]: (k1_setfam_1(k2_tarski(B_27, A_28))=k3_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.43/1.35  tff(c_10, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.35  tff(c_96, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_90, c_10])).
% 2.43/1.35  tff(c_181, plain, (![B_33, A_34]: (r1_tarski(k1_relat_1(k7_relat_1(B_33, A_34)), k1_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.35  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.35  tff(c_184, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_33, A_34)), k1_relat_1(B_33))=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_181, c_4])).
% 2.43/1.35  tff(c_302, plain, (![B_45, A_46]: (k3_xboole_0(k1_relat_1(B_45), k1_relat_1(k7_relat_1(B_45, A_46)))=k1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_184])).
% 2.43/1.35  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.43/1.35  tff(c_575, plain, (![B_56, A_57]: (k5_xboole_0(k1_relat_1(B_56), k1_relat_1(k7_relat_1(B_56, A_57)))=k4_xboole_0(k1_relat_1(B_56), k1_relat_1(k7_relat_1(B_56, A_57))) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_302, c_2])).
% 2.43/1.35  tff(c_187, plain, (![B_35, A_36]: (k3_xboole_0(k1_relat_1(B_35), A_36)=k1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.35  tff(c_202, plain, (![B_35, A_36]: (k5_xboole_0(k1_relat_1(B_35), k1_relat_1(k7_relat_1(B_35, A_36)))=k4_xboole_0(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_187, c_2])).
% 2.43/1.35  tff(c_619, plain, (![B_58, A_59]: (k4_xboole_0(k1_relat_1(B_58), k1_relat_1(k7_relat_1(B_58, A_59)))=k4_xboole_0(k1_relat_1(B_58), A_59) | ~v1_relat_1(B_58) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_575, c_202])).
% 2.43/1.35  tff(c_18, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.35  tff(c_21, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_18])).
% 2.43/1.35  tff(c_628, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_619, c_21])).
% 2.43/1.35  tff(c_655, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_628])).
% 2.43/1.35  tff(c_660, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_655])).
% 2.43/1.35  tff(c_664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_660])).
% 2.43/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  Inference rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Ref     : 0
% 2.43/1.35  #Sup     : 176
% 2.43/1.35  #Fact    : 0
% 2.43/1.35  #Define  : 0
% 2.43/1.35  #Split   : 0
% 2.43/1.35  #Chain   : 0
% 2.43/1.35  #Close   : 0
% 2.43/1.35  
% 2.43/1.35  Ordering : KBO
% 2.43/1.35  
% 2.43/1.35  Simplification rules
% 2.43/1.36  ----------------------
% 2.43/1.36  #Subsume      : 22
% 2.43/1.36  #Demod        : 16
% 2.43/1.36  #Tautology    : 65
% 2.43/1.36  #SimpNegUnit  : 0
% 2.43/1.36  #BackRed      : 0
% 2.43/1.36  
% 2.43/1.36  #Partial instantiations: 0
% 2.43/1.36  #Strategies tried      : 1
% 2.43/1.36  
% 2.43/1.36  Timing (in seconds)
% 2.43/1.36  ----------------------
% 2.43/1.36  Preprocessing        : 0.28
% 2.43/1.36  Parsing              : 0.15
% 2.43/1.36  CNF conversion       : 0.02
% 2.43/1.36  Main loop            : 0.31
% 2.43/1.36  Inferencing          : 0.12
% 2.43/1.36  Reduction            : 0.09
% 2.43/1.36  Demodulation         : 0.07
% 2.43/1.36  BG Simplification    : 0.02
% 2.43/1.36  Subsumption          : 0.05
% 2.43/1.36  Abstraction          : 0.02
% 2.60/1.36  MUC search           : 0.00
% 2.60/1.36  Cooper               : 0.00
% 2.60/1.36  Total                : 0.61
% 2.60/1.36  Index Insertion      : 0.00
% 2.60/1.36  Index Deletion       : 0.00
% 2.60/1.36  Index Matching       : 0.00
% 2.60/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
