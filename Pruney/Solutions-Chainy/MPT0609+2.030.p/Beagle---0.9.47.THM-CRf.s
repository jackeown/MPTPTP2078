%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   45 (  58 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  63 expanded)
%              Number of equality atoms :   25 (  37 expanded)
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

tff(f_58,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,(
    ! [C_43,A_44,B_45] :
      ( k7_relat_1(C_43,k4_xboole_0(A_44,B_45)) = k4_xboole_0(C_43,k7_relat_1(C_43,B_45))
      | ~ r1_tarski(k1_relat_1(C_43),A_44)
      | ~ v1_relat_1(C_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_213,plain,(
    ! [C_43,B_45] :
      ( k7_relat_1(C_43,k4_xboole_0(k1_relat_1(C_43),B_45)) = k4_xboole_0(C_43,k7_relat_1(C_43,B_45))
      | ~ v1_relat_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_154,plain,(
    ! [A_39,B_40] : k3_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(k1_relat_1(B_19),A_18) = k1_relat_1(k7_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_309,plain,(
    ! [B_54,B_55] :
      ( k1_relat_1(k7_relat_1(B_54,k4_xboole_0(k1_relat_1(B_54),B_55))) = k4_xboole_0(k1_relat_1(B_54),B_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_22])).

tff(c_435,plain,(
    ! [C_58,B_59] :
      ( k1_relat_1(k4_xboole_0(C_58,k7_relat_1(C_58,B_59))) = k4_xboole_0(k1_relat_1(C_58),B_59)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_309])).

tff(c_127,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(k1_relat_1(B_37),A_38) = k1_relat_1(k7_relat_1(B_37,A_38))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,(
    ! [B_46,A_47] :
      ( k4_xboole_0(k1_relat_1(B_46),k1_relat_1(k7_relat_1(B_46,A_47))) = k4_xboole_0(k1_relat_1(B_46),A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_10])).

tff(c_24,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_24])).

tff(c_226,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_28])).

tff(c_237,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_226])).

tff(c_456,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_237])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:38:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.42  
% 2.29/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.42  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.29/1.42  
% 2.29/1.42  %Foreground sorts:
% 2.29/1.42  
% 2.29/1.42  
% 2.29/1.42  %Background operators:
% 2.29/1.42  
% 2.29/1.42  
% 2.29/1.42  %Foreground operators:
% 2.29/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.29/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.29/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.29/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.29/1.42  
% 2.57/1.44  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.57/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.44  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.57/1.44  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.57/1.44  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.57/1.44  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.57/1.44  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.57/1.44  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.44  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.44  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.44  tff(c_209, plain, (![C_43, A_44, B_45]: (k7_relat_1(C_43, k4_xboole_0(A_44, B_45))=k4_xboole_0(C_43, k7_relat_1(C_43, B_45)) | ~r1_tarski(k1_relat_1(C_43), A_44) | ~v1_relat_1(C_43))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 2.57/1.44  tff(c_213, plain, (![C_43, B_45]: (k7_relat_1(C_43, k4_xboole_0(k1_relat_1(C_43), B_45))=k4_xboole_0(C_43, k7_relat_1(C_43, B_45)) | ~v1_relat_1(C_43))), inference(resolution, [status(thm)], [c_6, c_209])).
% 2.57/1.44  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.44  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.44  tff(c_58, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.44  tff(c_67, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_58])).
% 2.57/1.44  tff(c_154, plain, (![A_39, B_40]: (k3_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_67])).
% 2.57/1.44  tff(c_22, plain, (![B_19, A_18]: (k3_xboole_0(k1_relat_1(B_19), A_18)=k1_relat_1(k7_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.44  tff(c_309, plain, (![B_54, B_55]: (k1_relat_1(k7_relat_1(B_54, k4_xboole_0(k1_relat_1(B_54), B_55)))=k4_xboole_0(k1_relat_1(B_54), B_55) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_154, c_22])).
% 2.57/1.44  tff(c_435, plain, (![C_58, B_59]: (k1_relat_1(k4_xboole_0(C_58, k7_relat_1(C_58, B_59)))=k4_xboole_0(k1_relat_1(C_58), B_59) | ~v1_relat_1(C_58) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_213, c_309])).
% 2.57/1.44  tff(c_127, plain, (![B_37, A_38]: (k3_xboole_0(k1_relat_1(B_37), A_38)=k1_relat_1(k7_relat_1(B_37, A_38)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.44  tff(c_214, plain, (![B_46, A_47]: (k4_xboole_0(k1_relat_1(B_46), k1_relat_1(k7_relat_1(B_46, A_47)))=k4_xboole_0(k1_relat_1(B_46), A_47) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_127, c_10])).
% 2.57/1.44  tff(c_24, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.57/1.44  tff(c_28, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_24])).
% 2.57/1.44  tff(c_226, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_214, c_28])).
% 2.57/1.44  tff(c_237, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_226])).
% 2.57/1.44  tff(c_456, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_435, c_237])).
% 2.57/1.44  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_456])).
% 2.57/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  Inference rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Ref     : 0
% 2.57/1.44  #Sup     : 114
% 2.57/1.44  #Fact    : 0
% 2.57/1.44  #Define  : 0
% 2.57/1.44  #Split   : 0
% 2.57/1.44  #Chain   : 0
% 2.57/1.44  #Close   : 0
% 2.57/1.44  
% 2.57/1.44  Ordering : KBO
% 2.57/1.44  
% 2.57/1.44  Simplification rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Subsume      : 12
% 2.57/1.44  #Demod        : 58
% 2.57/1.44  #Tautology    : 52
% 2.57/1.44  #SimpNegUnit  : 0
% 2.57/1.44  #BackRed      : 0
% 2.57/1.44  
% 2.57/1.44  #Partial instantiations: 0
% 2.57/1.44  #Strategies tried      : 1
% 2.57/1.44  
% 2.57/1.44  Timing (in seconds)
% 2.57/1.44  ----------------------
% 2.57/1.44  Preprocessing        : 0.31
% 2.57/1.44  Parsing              : 0.15
% 2.57/1.44  CNF conversion       : 0.02
% 2.57/1.44  Main loop            : 0.35
% 2.57/1.44  Inferencing          : 0.13
% 2.57/1.44  Reduction            : 0.13
% 2.57/1.44  Demodulation         : 0.10
% 2.57/1.44  BG Simplification    : 0.02
% 2.57/1.44  Subsumption          : 0.05
% 2.57/1.44  Abstraction          : 0.03
% 2.57/1.44  MUC search           : 0.00
% 2.57/1.44  Cooper               : 0.00
% 2.57/1.44  Total                : 0.70
% 2.57/1.44  Index Insertion      : 0.00
% 2.57/1.44  Index Deletion       : 0.00
% 2.57/1.44  Index Matching       : 0.00
% 2.57/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
