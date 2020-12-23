%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 12.09s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :   48 (  85 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,k4_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,k3_xboole_0(k1_relat_1(B_15),A_14)) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k6_subset_1(B_17,k7_relat_1(B_17,A_16))) = k6_subset_1(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_108,plain,(
    ! [B_34,A_35] :
      ( k1_relat_1(k4_xboole_0(B_34,k7_relat_1(B_34,A_35))) = k4_xboole_0(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_123,plain,(
    ! [B_15,A_14] :
      ( k4_xboole_0(k1_relat_1(B_15),k3_xboole_0(k1_relat_1(B_15),A_14)) = k1_relat_1(k4_xboole_0(B_15,k7_relat_1(B_15,A_14)))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_108])).

tff(c_129,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),k4_xboole_0(k1_relat_1(B_15),A_14)) = k1_relat_1(k4_xboole_0(B_15,k7_relat_1(B_15,A_14)))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_123])).

tff(c_18,plain,(
    ! [A_18] :
      ( k7_relat_1(A_18,k1_relat_1(A_18)) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( k6_subset_1(k7_relat_1(C_13,A_11),k7_relat_1(C_13,B_12)) = k7_relat_1(C_13,k6_subset_1(A_11,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,(
    ! [C_39,A_40,B_41] :
      ( k4_xboole_0(k7_relat_1(C_39,A_40),k7_relat_1(C_39,B_41)) = k7_relat_1(C_39,k4_xboole_0(A_40,B_41))
      | ~ v1_relat_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_213,plain,(
    ! [A_42,B_43] :
      ( k7_relat_1(A_42,k4_xboole_0(k1_relat_1(A_42),B_43)) = k4_xboole_0(A_42,k7_relat_1(A_42,B_43))
      | ~ v1_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_185])).

tff(c_1366,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,k7_relat_1(A_84,k4_xboole_0(k1_relat_1(A_84),B_85))) = k7_relat_1(A_84,k3_xboole_0(k1_relat_1(A_84),B_85))
      | ~ v1_relat_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_213])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k4_xboole_0(B_17,k7_relat_1(B_17,A_16))) = k4_xboole_0(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_1408,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(k1_relat_1(A_84),k4_xboole_0(k1_relat_1(A_84),B_85)) = k1_relat_1(k7_relat_1(A_84,k3_xboole_0(k1_relat_1(A_84),B_85)))
      | ~ v1_relat_1(A_84)
      | ~ v1_relat_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_24])).

tff(c_1468,plain,(
    ! [A_86,B_87] :
      ( k1_relat_1(k7_relat_1(A_86,k3_xboole_0(k1_relat_1(A_86),B_87))) = k3_xboole_0(k1_relat_1(A_86),B_87)
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1408])).

tff(c_1587,plain,(
    ! [B_88,A_89] :
      ( k3_xboole_0(k1_relat_1(B_88),A_89) = k1_relat_1(k7_relat_1(B_88,A_89))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1468])).

tff(c_16508,plain,(
    ! [B_248,A_249] :
      ( k4_xboole_0(k1_relat_1(B_248),k1_relat_1(k7_relat_1(B_248,A_249))) = k3_xboole_0(k1_relat_1(B_248),k4_xboole_0(k1_relat_1(B_248),A_249))
      | ~ v1_relat_1(B_248)
      | ~ v1_relat_1(B_248)
      | ~ v1_relat_1(B_248)
      | ~ v1_relat_1(B_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_74])).

tff(c_20,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_20])).

tff(c_16598,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16508,c_23])).

tff(c_16720,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_22,c_22,c_16598])).

tff(c_16740,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_16720])).

tff(c_16748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.09/4.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/4.79  
% 12.09/4.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/4.79  %$ v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 12.09/4.79  
% 12.09/4.79  %Foreground sorts:
% 12.09/4.79  
% 12.09/4.79  
% 12.09/4.79  %Background operators:
% 12.09/4.79  
% 12.09/4.79  
% 12.09/4.79  %Foreground operators:
% 12.09/4.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.09/4.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.09/4.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.09/4.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.09/4.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.09/4.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.09/4.79  tff('#skF_2', type, '#skF_2': $i).
% 12.09/4.79  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.09/4.79  tff('#skF_1', type, '#skF_1': $i).
% 12.09/4.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.09/4.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.09/4.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.09/4.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.09/4.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.09/4.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.09/4.79  
% 12.09/4.81  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 12.09/4.81  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.09/4.81  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 12.09/4.81  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.09/4.81  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 12.09/4.81  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 12.09/4.81  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 12.09/4.81  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.09/4.81  tff(c_71, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.09/4.81  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.09/4.81  tff(c_74, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k3_xboole_0(A_28, k4_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 12.09/4.81  tff(c_14, plain, (![B_15, A_14]: (k7_relat_1(B_15, k3_xboole_0(k1_relat_1(B_15), A_14))=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.09/4.81  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.09/4.81  tff(c_16, plain, (![B_17, A_16]: (k1_relat_1(k6_subset_1(B_17, k7_relat_1(B_17, A_16)))=k6_subset_1(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.09/4.81  tff(c_108, plain, (![B_34, A_35]: (k1_relat_1(k4_xboole_0(B_34, k7_relat_1(B_34, A_35)))=k4_xboole_0(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16])).
% 12.09/4.81  tff(c_123, plain, (![B_15, A_14]: (k4_xboole_0(k1_relat_1(B_15), k3_xboole_0(k1_relat_1(B_15), A_14))=k1_relat_1(k4_xboole_0(B_15, k7_relat_1(B_15, A_14))) | ~v1_relat_1(B_15) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_14, c_108])).
% 12.09/4.81  tff(c_129, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), k4_xboole_0(k1_relat_1(B_15), A_14))=k1_relat_1(k4_xboole_0(B_15, k7_relat_1(B_15, A_14))) | ~v1_relat_1(B_15) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_123])).
% 12.09/4.81  tff(c_18, plain, (![A_18]: (k7_relat_1(A_18, k1_relat_1(A_18))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.09/4.81  tff(c_12, plain, (![C_13, A_11, B_12]: (k6_subset_1(k7_relat_1(C_13, A_11), k7_relat_1(C_13, B_12))=k7_relat_1(C_13, k6_subset_1(A_11, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.09/4.81  tff(c_185, plain, (![C_39, A_40, B_41]: (k4_xboole_0(k7_relat_1(C_39, A_40), k7_relat_1(C_39, B_41))=k7_relat_1(C_39, k4_xboole_0(A_40, B_41)) | ~v1_relat_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_12])).
% 12.09/4.81  tff(c_213, plain, (![A_42, B_43]: (k7_relat_1(A_42, k4_xboole_0(k1_relat_1(A_42), B_43))=k4_xboole_0(A_42, k7_relat_1(A_42, B_43)) | ~v1_relat_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_18, c_185])).
% 12.09/4.81  tff(c_1366, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k7_relat_1(A_84, k4_xboole_0(k1_relat_1(A_84), B_85)))=k7_relat_1(A_84, k3_xboole_0(k1_relat_1(A_84), B_85)) | ~v1_relat_1(A_84) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_4, c_213])).
% 12.09/4.81  tff(c_24, plain, (![B_17, A_16]: (k1_relat_1(k4_xboole_0(B_17, k7_relat_1(B_17, A_16)))=k4_xboole_0(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16])).
% 12.09/4.81  tff(c_1408, plain, (![A_84, B_85]: (k4_xboole_0(k1_relat_1(A_84), k4_xboole_0(k1_relat_1(A_84), B_85))=k1_relat_1(k7_relat_1(A_84, k3_xboole_0(k1_relat_1(A_84), B_85))) | ~v1_relat_1(A_84) | ~v1_relat_1(A_84) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_1366, c_24])).
% 12.09/4.81  tff(c_1468, plain, (![A_86, B_87]: (k1_relat_1(k7_relat_1(A_86, k3_xboole_0(k1_relat_1(A_86), B_87)))=k3_xboole_0(k1_relat_1(A_86), B_87) | ~v1_relat_1(A_86) | ~v1_relat_1(A_86) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1408])).
% 12.09/4.81  tff(c_1587, plain, (![B_88, A_89]: (k3_xboole_0(k1_relat_1(B_88), A_89)=k1_relat_1(k7_relat_1(B_88, A_89)) | ~v1_relat_1(B_88) | ~v1_relat_1(B_88) | ~v1_relat_1(B_88) | ~v1_relat_1(B_88))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1468])).
% 12.09/4.81  tff(c_16508, plain, (![B_248, A_249]: (k4_xboole_0(k1_relat_1(B_248), k1_relat_1(k7_relat_1(B_248, A_249)))=k3_xboole_0(k1_relat_1(B_248), k4_xboole_0(k1_relat_1(B_248), A_249)) | ~v1_relat_1(B_248) | ~v1_relat_1(B_248) | ~v1_relat_1(B_248) | ~v1_relat_1(B_248))), inference(superposition, [status(thm), theory('equality')], [c_1587, c_74])).
% 12.09/4.81  tff(c_20, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.09/4.81  tff(c_23, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_20])).
% 12.09/4.81  tff(c_16598, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16508, c_23])).
% 12.09/4.81  tff(c_16720, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_22, c_22, c_16598])).
% 12.09/4.81  tff(c_16740, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_16720])).
% 12.09/4.81  tff(c_16748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_16740])).
% 12.09/4.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/4.81  
% 12.09/4.81  Inference rules
% 12.09/4.81  ----------------------
% 12.09/4.81  #Ref     : 0
% 12.09/4.81  #Sup     : 4826
% 12.09/4.81  #Fact    : 0
% 12.09/4.81  #Define  : 0
% 12.09/4.81  #Split   : 0
% 12.09/4.81  #Chain   : 0
% 12.09/4.81  #Close   : 0
% 12.09/4.81  
% 12.09/4.81  Ordering : KBO
% 12.09/4.81  
% 12.09/4.81  Simplification rules
% 12.09/4.81  ----------------------
% 12.09/4.81  #Subsume      : 322
% 12.09/4.81  #Demod        : 1532
% 12.09/4.81  #Tautology    : 411
% 12.09/4.81  #SimpNegUnit  : 0
% 12.09/4.81  #BackRed      : 0
% 12.09/4.81  
% 12.09/4.81  #Partial instantiations: 0
% 12.09/4.81  #Strategies tried      : 1
% 12.09/4.81  
% 12.09/4.81  Timing (in seconds)
% 12.09/4.81  ----------------------
% 12.09/4.81  Preprocessing        : 0.28
% 12.09/4.81  Parsing              : 0.15
% 12.09/4.81  CNF conversion       : 0.02
% 12.09/4.81  Main loop            : 3.72
% 12.09/4.81  Inferencing          : 1.18
% 12.09/4.81  Reduction            : 0.92
% 12.09/4.81  Demodulation         : 0.70
% 12.09/4.81  BG Simplification    : 0.23
% 12.09/4.81  Subsumption          : 1.23
% 12.09/4.81  Abstraction          : 0.29
% 12.09/4.81  MUC search           : 0.00
% 12.09/4.81  Cooper               : 0.00
% 12.09/4.81  Total                : 4.03
% 12.09/4.81  Index Insertion      : 0.00
% 12.09/4.81  Index Deletion       : 0.00
% 12.09/4.81  Index Matching       : 0.00
% 12.09/4.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
