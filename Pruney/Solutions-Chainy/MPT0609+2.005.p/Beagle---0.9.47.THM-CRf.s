%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:31 EST 2020

% Result     : Theorem 15.50s
% Output     : CNFRefutation 15.50s
% Verified   : 
% Statistics : Number of formulae       :   60 (  92 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :   59 (  94 expanded)
%              Number of equality atoms :   35 (  64 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k6_subset_1(B_13,k7_relat_1(B_13,A_12))) = k6_subset_1(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k4_xboole_0(B_13,k7_relat_1(B_13,A_12))) = k4_xboole_0(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_14])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),A_17) = k1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(B_31,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_10,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_31,A_30] : k3_xboole_0(B_31,A_30) = k3_xboole_0(A_30,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_10])).

tff(c_169,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_181,plain,(
    ! [B_31,A_30] : k5_xboole_0(B_31,k3_xboole_0(A_30,B_31)) = k4_xboole_0(B_31,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_169])).

tff(c_12,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [B_38,A_39] :
      ( k3_xboole_0(k1_relat_1(B_38),A_39) = k1_relat_1(k7_relat_1(B_38,A_39))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_210,plain,(
    ! [A_14,A_39] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_39)) = k3_xboole_0(A_14,A_39)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_184])).

tff(c_215,plain,(
    ! [A_40,A_41] : k1_relat_1(k7_relat_1(k6_relat_1(A_40),A_41)) = k3_xboole_0(A_40,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_210])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_224,plain,(
    ! [A_40,A_41] :
      ( r1_tarski(k3_xboole_0(A_40,A_41),A_41)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_20])).

tff(c_232,plain,(
    ! [A_42,A_43] : r1_tarski(k3_xboole_0(A_42,A_43),A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_224])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_294,plain,(
    ! [A_48,A_49] : k3_xboole_0(k3_xboole_0(A_48,A_49),A_49) = k3_xboole_0(A_48,A_49) ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_303,plain,(
    ! [A_49,A_48] : k5_xboole_0(A_49,k3_xboole_0(A_48,A_49)) = k4_xboole_0(A_49,k3_xboole_0(A_48,A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_181])).

tff(c_614,plain,(
    ! [A_60,A_61] : k4_xboole_0(A_60,k3_xboole_0(A_61,A_60)) = k4_xboole_0(A_60,A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_303])).

tff(c_1201,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_614])).

tff(c_10220,plain,(
    ! [B_218,A_219] :
      ( k4_xboole_0(k1_relat_1(B_218),k1_relat_1(k7_relat_1(B_218,A_219))) = k4_xboole_0(k1_relat_1(B_218),A_219)
      | ~ v1_relat_1(B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1201])).

tff(c_24,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_24])).

tff(c_10255,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10220,c_28])).

tff(c_10330,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10255])).

tff(c_10345,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_10330])).

tff(c_10349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.50/5.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/5.40  
% 15.50/5.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/5.41  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 15.50/5.41  
% 15.50/5.41  %Foreground sorts:
% 15.50/5.41  
% 15.50/5.41  
% 15.50/5.41  %Background operators:
% 15.50/5.41  
% 15.50/5.41  
% 15.50/5.41  %Foreground operators:
% 15.50/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.50/5.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.50/5.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.50/5.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.50/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.50/5.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.50/5.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.50/5.41  tff('#skF_2', type, '#skF_2': $i).
% 15.50/5.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 15.50/5.41  tff('#skF_1', type, '#skF_1': $i).
% 15.50/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.50/5.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.50/5.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.50/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.50/5.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.50/5.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.50/5.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.50/5.41  
% 15.50/5.42  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 15.50/5.42  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 15.50/5.42  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 15.50/5.42  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 15.50/5.42  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.50/5.42  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.50/5.42  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.50/5.42  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 15.50/5.42  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.50/5.42  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 15.50/5.42  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.50/5.42  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.50/5.42  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.50/5.42  tff(c_14, plain, (![B_13, A_12]: (k1_relat_1(k6_subset_1(B_13, k7_relat_1(B_13, A_12)))=k6_subset_1(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.50/5.42  tff(c_27, plain, (![B_13, A_12]: (k1_relat_1(k4_xboole_0(B_13, k7_relat_1(B_13, A_12)))=k4_xboole_0(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_14])).
% 15.50/5.42  tff(c_22, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), A_17)=k1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.50/5.42  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.50/5.42  tff(c_90, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.50/5.42  tff(c_106, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(B_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_6, c_90])).
% 15.50/5.42  tff(c_10, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.50/5.42  tff(c_112, plain, (![B_31, A_30]: (k3_xboole_0(B_31, A_30)=k3_xboole_0(A_30, B_31))), inference(superposition, [status(thm), theory('equality')], [c_106, c_10])).
% 15.50/5.42  tff(c_169, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.50/5.42  tff(c_181, plain, (![B_31, A_30]: (k5_xboole_0(B_31, k3_xboole_0(A_30, B_31))=k4_xboole_0(B_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_112, c_169])).
% 15.50/5.42  tff(c_12, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.50/5.42  tff(c_16, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.50/5.42  tff(c_184, plain, (![B_38, A_39]: (k3_xboole_0(k1_relat_1(B_38), A_39)=k1_relat_1(k7_relat_1(B_38, A_39)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.50/5.42  tff(c_210, plain, (![A_14, A_39]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_39))=k3_xboole_0(A_14, A_39) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_184])).
% 15.50/5.42  tff(c_215, plain, (![A_40, A_41]: (k1_relat_1(k7_relat_1(k6_relat_1(A_40), A_41))=k3_xboole_0(A_40, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_210])).
% 15.50/5.42  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.50/5.42  tff(c_224, plain, (![A_40, A_41]: (r1_tarski(k3_xboole_0(A_40, A_41), A_41) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_20])).
% 15.50/5.42  tff(c_232, plain, (![A_42, A_43]: (r1_tarski(k3_xboole_0(A_42, A_43), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_224])).
% 15.50/5.42  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.50/5.42  tff(c_294, plain, (![A_48, A_49]: (k3_xboole_0(k3_xboole_0(A_48, A_49), A_49)=k3_xboole_0(A_48, A_49))), inference(resolution, [status(thm)], [c_232, c_4])).
% 15.50/5.42  tff(c_303, plain, (![A_49, A_48]: (k5_xboole_0(A_49, k3_xboole_0(A_48, A_49))=k4_xboole_0(A_49, k3_xboole_0(A_48, A_49)))), inference(superposition, [status(thm), theory('equality')], [c_294, c_181])).
% 15.50/5.42  tff(c_614, plain, (![A_60, A_61]: (k4_xboole_0(A_60, k3_xboole_0(A_61, A_60))=k4_xboole_0(A_60, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_303])).
% 15.50/5.42  tff(c_1201, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_112, c_614])).
% 15.50/5.42  tff(c_10220, plain, (![B_218, A_219]: (k4_xboole_0(k1_relat_1(B_218), k1_relat_1(k7_relat_1(B_218, A_219)))=k4_xboole_0(k1_relat_1(B_218), A_219) | ~v1_relat_1(B_218))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1201])).
% 15.50/5.42  tff(c_24, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.50/5.42  tff(c_28, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_24])).
% 15.50/5.42  tff(c_10255, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10220, c_28])).
% 15.50/5.42  tff(c_10330, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10255])).
% 15.50/5.42  tff(c_10345, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27, c_10330])).
% 15.50/5.42  tff(c_10349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_10345])).
% 15.50/5.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/5.42  
% 15.50/5.42  Inference rules
% 15.50/5.42  ----------------------
% 15.50/5.42  #Ref     : 0
% 15.50/5.42  #Sup     : 2679
% 15.50/5.42  #Fact    : 0
% 15.50/5.42  #Define  : 0
% 15.50/5.42  #Split   : 0
% 15.50/5.43  #Chain   : 0
% 15.50/5.43  #Close   : 0
% 15.50/5.43  
% 15.50/5.43  Ordering : KBO
% 15.50/5.43  
% 15.50/5.43  Simplification rules
% 15.50/5.43  ----------------------
% 15.50/5.43  #Subsume      : 561
% 15.50/5.43  #Demod        : 3219
% 15.50/5.43  #Tautology    : 890
% 15.50/5.43  #SimpNegUnit  : 0
% 15.50/5.43  #BackRed      : 0
% 15.50/5.43  
% 15.50/5.43  #Partial instantiations: 0
% 15.50/5.43  #Strategies tried      : 1
% 15.50/5.43  
% 15.50/5.43  Timing (in seconds)
% 15.50/5.43  ----------------------
% 15.50/5.43  Preprocessing        : 0.44
% 15.50/5.43  Parsing              : 0.23
% 15.50/5.43  CNF conversion       : 0.03
% 15.50/5.43  Main loop            : 4.09
% 15.50/5.43  Inferencing          : 0.97
% 15.50/5.43  Reduction            : 2.22
% 15.50/5.43  Demodulation         : 1.98
% 15.50/5.43  BG Simplification    : 0.15
% 15.50/5.43  Subsumption          : 0.60
% 15.50/5.43  Abstraction          : 0.25
% 15.50/5.43  MUC search           : 0.00
% 15.50/5.43  Cooper               : 0.00
% 15.50/5.43  Total                : 4.58
% 15.50/5.43  Index Insertion      : 0.00
% 15.50/5.43  Index Deletion       : 0.00
% 15.50/5.43  Index Matching       : 0.00
% 15.50/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
