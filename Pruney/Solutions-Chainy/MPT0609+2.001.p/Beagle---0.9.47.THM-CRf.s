%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:31 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 (  90 expanded)
%              Number of equality atoms :   34 (  50 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_31,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_686,plain,(
    ! [C_64,A_65,B_66] :
      ( k7_relat_1(C_64,k4_xboole_0(A_65,B_66)) = k4_xboole_0(C_64,k7_relat_1(C_64,B_66))
      | ~ r1_tarski(k1_relat_1(C_64),A_65)
      | ~ v1_relat_1(C_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_702,plain,(
    ! [C_67,B_68] :
      ( k7_relat_1(C_67,k4_xboole_0(k1_relat_1(C_67),B_68)) = k4_xboole_0(C_67,k7_relat_1(C_67,B_68))
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_686])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k6_subset_1(k1_relat_1(B_14),A_13))) = k6_subset_1(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k4_xboole_0(k1_relat_1(B_14),A_13))) = k4_xboole_0(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_717,plain,(
    ! [C_67,B_68] :
      ( k1_relat_1(k4_xboole_0(C_67,k7_relat_1(C_67,B_68))) = k4_xboole_0(k1_relat_1(C_67),B_68)
      | ~ v1_relat_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_31])).

tff(c_12,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [B_32,A_33] : k1_setfam_1(k2_tarski(B_32,A_33)) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_81])).

tff(c_16,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_16])).

tff(c_196,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_41,A_42)),k1_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [B_41,A_42] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_41,A_42)),k1_relat_1(B_41)) = k1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_196,c_10])).

tff(c_450,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),k1_relat_1(k7_relat_1(B_58,A_59))) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_201])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1133,plain,(
    ! [B_84,A_85] :
      ( k5_xboole_0(k1_relat_1(B_84),k1_relat_1(k7_relat_1(B_84,A_85))) = k4_xboole_0(k1_relat_1(B_84),k1_relat_1(k7_relat_1(B_84,A_85)))
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_8])).

tff(c_237,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(k1_relat_1(B_45),A_46) = k1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_246,plain,(
    ! [B_45,A_46] :
      ( k5_xboole_0(k1_relat_1(B_45),k1_relat_1(k7_relat_1(B_45,A_46))) = k4_xboole_0(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_8])).

tff(c_1193,plain,(
    ! [B_86,A_87] :
      ( k4_xboole_0(k1_relat_1(B_86),k1_relat_1(k7_relat_1(B_86,A_87))) = k4_xboole_0(k1_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_246])).

tff(c_26,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_29,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_26])).

tff(c_1220,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_29])).

tff(c_1262,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_1220])).

tff(c_1269,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_1262])).

tff(c_1273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:52:35 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.04/1.47  
% 3.04/1.47  %Foreground sorts:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Background operators:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Foreground operators:
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.04/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.47  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.04/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.04/1.47  
% 3.23/1.48  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 3.23/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.48  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.23/1.48  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 3.23/1.48  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 3.23/1.48  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.23/1.48  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.23/1.48  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.23/1.48  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.48  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.48  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.23/1.48  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.23/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.48  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.48  tff(c_686, plain, (![C_64, A_65, B_66]: (k7_relat_1(C_64, k4_xboole_0(A_65, B_66))=k4_xboole_0(C_64, k7_relat_1(C_64, B_66)) | ~r1_tarski(k1_relat_1(C_64), A_65) | ~v1_relat_1(C_64))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 3.23/1.48  tff(c_702, plain, (![C_67, B_68]: (k7_relat_1(C_67, k4_xboole_0(k1_relat_1(C_67), B_68))=k4_xboole_0(C_67, k7_relat_1(C_67, B_68)) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_6, c_686])).
% 3.23/1.48  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k6_subset_1(k1_relat_1(B_14), A_13)))=k6_subset_1(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.48  tff(c_31, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k4_xboole_0(k1_relat_1(B_14), A_13)))=k4_xboole_0(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 3.23/1.48  tff(c_717, plain, (![C_67, B_68]: (k1_relat_1(k4_xboole_0(C_67, k7_relat_1(C_67, B_68)))=k4_xboole_0(k1_relat_1(C_67), B_68) | ~v1_relat_1(C_67) | ~v1_relat_1(C_67))), inference(superposition, [status(thm), theory('equality')], [c_702, c_31])).
% 3.23/1.48  tff(c_12, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.48  tff(c_81, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.48  tff(c_105, plain, (![B_32, A_33]: (k1_setfam_1(k2_tarski(B_32, A_33))=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_12, c_81])).
% 3.23/1.48  tff(c_16, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.48  tff(c_111, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_105, c_16])).
% 3.23/1.48  tff(c_196, plain, (![B_41, A_42]: (r1_tarski(k1_relat_1(k7_relat_1(B_41, A_42)), k1_relat_1(B_41)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.48  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.48  tff(c_201, plain, (![B_41, A_42]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_41, A_42)), k1_relat_1(B_41))=k1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_196, c_10])).
% 3.23/1.48  tff(c_450, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), k1_relat_1(k7_relat_1(B_58, A_59)))=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_201])).
% 3.23/1.48  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.48  tff(c_1133, plain, (![B_84, A_85]: (k5_xboole_0(k1_relat_1(B_84), k1_relat_1(k7_relat_1(B_84, A_85)))=k4_xboole_0(k1_relat_1(B_84), k1_relat_1(k7_relat_1(B_84, A_85))) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_450, c_8])).
% 3.23/1.48  tff(c_237, plain, (![B_45, A_46]: (k3_xboole_0(k1_relat_1(B_45), A_46)=k1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.48  tff(c_246, plain, (![B_45, A_46]: (k5_xboole_0(k1_relat_1(B_45), k1_relat_1(k7_relat_1(B_45, A_46)))=k4_xboole_0(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_237, c_8])).
% 3.23/1.48  tff(c_1193, plain, (![B_86, A_87]: (k4_xboole_0(k1_relat_1(B_86), k1_relat_1(k7_relat_1(B_86, A_87)))=k4_xboole_0(k1_relat_1(B_86), A_87) | ~v1_relat_1(B_86) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_246])).
% 3.23/1.48  tff(c_26, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.23/1.48  tff(c_29, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_26])).
% 3.23/1.48  tff(c_1220, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1193, c_29])).
% 3.23/1.48  tff(c_1262, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_1220])).
% 3.23/1.48  tff(c_1269, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_717, c_1262])).
% 3.23/1.48  tff(c_1273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1269])).
% 3.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  Inference rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Ref     : 0
% 3.23/1.48  #Sup     : 358
% 3.23/1.48  #Fact    : 0
% 3.23/1.48  #Define  : 0
% 3.23/1.48  #Split   : 0
% 3.23/1.48  #Chain   : 0
% 3.23/1.48  #Close   : 0
% 3.23/1.48  
% 3.23/1.48  Ordering : KBO
% 3.23/1.48  
% 3.23/1.48  Simplification rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Subsume      : 33
% 3.23/1.48  #Demod        : 35
% 3.23/1.48  #Tautology    : 88
% 3.23/1.48  #SimpNegUnit  : 0
% 3.23/1.48  #BackRed      : 0
% 3.23/1.48  
% 3.23/1.48  #Partial instantiations: 0
% 3.23/1.48  #Strategies tried      : 1
% 3.23/1.48  
% 3.23/1.48  Timing (in seconds)
% 3.23/1.48  ----------------------
% 3.23/1.49  Preprocessing        : 0.29
% 3.23/1.49  Parsing              : 0.15
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.43
% 3.23/1.49  Inferencing          : 0.17
% 3.23/1.49  Reduction            : 0.13
% 3.23/1.49  Demodulation         : 0.09
% 3.23/1.49  BG Simplification    : 0.03
% 3.23/1.49  Subsumption          : 0.08
% 3.23/1.49  Abstraction          : 0.03
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.75
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
