%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:31 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  58 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :    5 (   3 average)
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

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k6_subset_1(B_16,k7_relat_1(B_16,A_15))) = k6_subset_1(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k4_xboole_0(B_16,k7_relat_1(B_16,A_15))) = k4_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_235,plain,(
    ! [A_43,B_44] : k3_xboole_0(k4_xboole_0(A_43,B_44),A_43) = k4_xboole_0(A_43,B_44) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_14,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_14])).

tff(c_250,plain,(
    ! [A_43,B_44] : k3_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_94])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),A_17) = k1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_160,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_764,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,k4_xboole_0(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_8])).

tff(c_803,plain,(
    ! [B_18,A_17] :
      ( k4_xboole_0(k1_relat_1(B_18),k1_relat_1(k7_relat_1(B_18,A_17))) = k3_xboole_0(k1_relat_1(B_18),k4_xboole_0(k1_relat_1(B_18),A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_764])).

tff(c_2876,plain,(
    ! [B_106,A_107] :
      ( k4_xboole_0(k1_relat_1(B_106),k1_relat_1(k7_relat_1(B_106,A_107))) = k4_xboole_0(k1_relat_1(B_106),A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_803])).

tff(c_20,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_20])).

tff(c_2918,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2876,c_23])).

tff(c_2941,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2918])).

tff(c_2947,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2941])).

tff(c_2951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.42  
% 5.42/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.42  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.50/2.42  
% 5.50/2.42  %Foreground sorts:
% 5.50/2.42  
% 5.50/2.42  
% 5.50/2.42  %Background operators:
% 5.50/2.42  
% 5.50/2.42  
% 5.50/2.42  %Foreground operators:
% 5.50/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.50/2.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.50/2.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.50/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.50/2.42  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.50/2.42  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.50/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.50/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.50/2.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.50/2.42  
% 5.50/2.44  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 5.50/2.44  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.50/2.44  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 5.50/2.44  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.50/2.44  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.50/2.44  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.50/2.44  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.50/2.44  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 5.50/2.44  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.50/2.44  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.50/2.44  tff(c_12, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.50/2.44  tff(c_16, plain, (![B_16, A_15]: (k1_relat_1(k6_subset_1(B_16, k7_relat_1(B_16, A_15)))=k6_subset_1(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.50/2.44  tff(c_24, plain, (![B_16, A_15]: (k1_relat_1(k4_xboole_0(B_16, k7_relat_1(B_16, A_15)))=k4_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 5.50/2.44  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.50/2.44  tff(c_83, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.50/2.44  tff(c_235, plain, (![A_43, B_44]: (k3_xboole_0(k4_xboole_0(A_43, B_44), A_43)=k4_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_83])).
% 5.50/2.44  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.50/2.44  tff(c_68, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.50/2.44  tff(c_88, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 5.50/2.44  tff(c_14, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.50/2.44  tff(c_94, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_88, c_14])).
% 5.50/2.44  tff(c_250, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_235, c_94])).
% 5.50/2.44  tff(c_18, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), A_17)=k1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.44  tff(c_160, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.50/2.44  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.50/2.44  tff(c_764, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k3_xboole_0(A_63, k4_xboole_0(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_8])).
% 5.50/2.44  tff(c_803, plain, (![B_18, A_17]: (k4_xboole_0(k1_relat_1(B_18), k1_relat_1(k7_relat_1(B_18, A_17)))=k3_xboole_0(k1_relat_1(B_18), k4_xboole_0(k1_relat_1(B_18), A_17)) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_764])).
% 5.50/2.44  tff(c_2876, plain, (![B_106, A_107]: (k4_xboole_0(k1_relat_1(B_106), k1_relat_1(k7_relat_1(B_106, A_107)))=k4_xboole_0(k1_relat_1(B_106), A_107) | ~v1_relat_1(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_803])).
% 5.50/2.44  tff(c_20, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.50/2.44  tff(c_23, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_20])).
% 5.50/2.44  tff(c_2918, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2876, c_23])).
% 5.50/2.44  tff(c_2941, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2918])).
% 5.50/2.44  tff(c_2947, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2941])).
% 5.50/2.44  tff(c_2951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_2947])).
% 5.50/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.50/2.44  
% 5.50/2.44  Inference rules
% 5.50/2.44  ----------------------
% 5.50/2.44  #Ref     : 0
% 5.50/2.44  #Sup     : 742
% 5.50/2.44  #Fact    : 0
% 5.50/2.44  #Define  : 0
% 5.50/2.44  #Split   : 0
% 5.50/2.44  #Chain   : 0
% 5.50/2.44  #Close   : 0
% 5.50/2.44  
% 5.50/2.44  Ordering : KBO
% 5.50/2.44  
% 5.50/2.44  Simplification rules
% 5.50/2.44  ----------------------
% 5.50/2.44  #Subsume      : 66
% 5.50/2.44  #Demod        : 908
% 5.50/2.44  #Tautology    : 457
% 5.50/2.44  #SimpNegUnit  : 0
% 5.50/2.44  #BackRed      : 1
% 5.50/2.44  
% 5.50/2.44  #Partial instantiations: 0
% 5.50/2.44  #Strategies tried      : 1
% 5.50/2.44  
% 5.50/2.44  Timing (in seconds)
% 5.50/2.44  ----------------------
% 5.50/2.44  Preprocessing        : 0.47
% 5.50/2.44  Parsing              : 0.24
% 5.50/2.44  CNF conversion       : 0.03
% 5.50/2.44  Main loop            : 1.12
% 5.50/2.44  Inferencing          : 0.31
% 5.50/2.44  Reduction            : 0.56
% 5.50/2.44  Demodulation         : 0.49
% 5.50/2.44  BG Simplification    : 0.04
% 5.50/2.44  Subsumption          : 0.14
% 5.50/2.44  Abstraction          : 0.07
% 5.50/2.44  MUC search           : 0.00
% 5.50/2.44  Cooper               : 0.00
% 5.50/2.45  Total                : 1.64
% 5.50/2.45  Index Insertion      : 0.00
% 5.50/2.45  Index Deletion       : 0.00
% 5.50/2.45  Index Matching       : 0.00
% 5.50/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
