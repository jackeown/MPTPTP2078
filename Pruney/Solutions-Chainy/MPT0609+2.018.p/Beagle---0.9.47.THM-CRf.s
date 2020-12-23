%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:33 EST 2020

% Result     : Theorem 9.21s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  63 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_56,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(C_15,k6_subset_1(A_13,B_14)) = k6_subset_1(C_15,k7_relat_1(C_15,B_14))
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_462,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(A_48,B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_18])).

tff(c_466,plain,(
    ! [C_47,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(k1_relat_1(C_47),B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_462])).

tff(c_265,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(k1_relat_1(B_39),A_40) = k1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_119,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_2117,plain,(
    ! [B_86,B_87] :
      ( k1_relat_1(k7_relat_1(B_86,k4_xboole_0(k1_relat_1(B_86),B_87))) = k4_xboole_0(k1_relat_1(B_86),B_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_119])).

tff(c_12156,plain,(
    ! [C_185,B_186] :
      ( k1_relat_1(k4_xboole_0(C_185,k7_relat_1(C_185,B_186))) = k4_xboole_0(k1_relat_1(C_185),B_186)
      | ~ v1_relat_1(C_185)
      | ~ v1_relat_1(C_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_2117])).

tff(c_1118,plain,(
    ! [B_60,A_61] :
      ( k4_xboole_0(k1_relat_1(B_60),k1_relat_1(k7_relat_1(B_60,A_61))) = k4_xboole_0(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_12])).

tff(c_22,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_1136,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_25])).

tff(c_1148,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1136])).

tff(c_12207,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12156,c_1148])).

tff(c_12243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.21/3.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.21/3.32  
% 9.21/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.21/3.33  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 9.21/3.33  
% 9.21/3.33  %Foreground sorts:
% 9.21/3.33  
% 9.21/3.33  
% 9.21/3.33  %Background operators:
% 9.21/3.33  
% 9.21/3.33  
% 9.21/3.33  %Foreground operators:
% 9.21/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.21/3.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.21/3.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.21/3.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.21/3.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.21/3.33  tff('#skF_2', type, '#skF_2': $i).
% 9.21/3.33  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.21/3.33  tff('#skF_1', type, '#skF_1': $i).
% 9.21/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.21/3.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.21/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.21/3.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.21/3.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.21/3.33  
% 9.21/3.34  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 9.21/3.34  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.21/3.34  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.21/3.34  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 9.21/3.34  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 9.21/3.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.21/3.34  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.21/3.34  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.21/3.34  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.21/3.34  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.21/3.34  tff(c_18, plain, (![C_15, A_13, B_14]: (k7_relat_1(C_15, k6_subset_1(A_13, B_14))=k6_subset_1(C_15, k7_relat_1(C_15, B_14)) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.21/3.34  tff(c_462, plain, (![C_47, A_48, B_49]: (k7_relat_1(C_47, k4_xboole_0(A_48, B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_18])).
% 9.21/3.34  tff(c_466, plain, (![C_47, B_49]: (k7_relat_1(C_47, k4_xboole_0(k1_relat_1(C_47), B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_8, c_462])).
% 9.21/3.34  tff(c_265, plain, (![B_39, A_40]: (k3_xboole_0(k1_relat_1(B_39), A_40)=k1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.21/3.34  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.21/3.34  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.21/3.34  tff(c_101, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.21/3.34  tff(c_110, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_101])).
% 9.21/3.34  tff(c_119, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_110])).
% 9.21/3.34  tff(c_2117, plain, (![B_86, B_87]: (k1_relat_1(k7_relat_1(B_86, k4_xboole_0(k1_relat_1(B_86), B_87)))=k4_xboole_0(k1_relat_1(B_86), B_87) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_265, c_119])).
% 9.21/3.34  tff(c_12156, plain, (![C_185, B_186]: (k1_relat_1(k4_xboole_0(C_185, k7_relat_1(C_185, B_186)))=k4_xboole_0(k1_relat_1(C_185), B_186) | ~v1_relat_1(C_185) | ~v1_relat_1(C_185))), inference(superposition, [status(thm), theory('equality')], [c_466, c_2117])).
% 9.21/3.34  tff(c_1118, plain, (![B_60, A_61]: (k4_xboole_0(k1_relat_1(B_60), k1_relat_1(k7_relat_1(B_60, A_61)))=k4_xboole_0(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_265, c_12])).
% 9.21/3.34  tff(c_22, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.21/3.34  tff(c_25, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 9.21/3.34  tff(c_1136, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1118, c_25])).
% 9.21/3.34  tff(c_1148, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1136])).
% 9.21/3.34  tff(c_12207, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12156, c_1148])).
% 9.21/3.34  tff(c_12243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_12207])).
% 9.21/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.21/3.34  
% 9.21/3.34  Inference rules
% 9.21/3.34  ----------------------
% 9.21/3.34  #Ref     : 0
% 9.21/3.34  #Sup     : 3163
% 9.21/3.34  #Fact    : 0
% 9.21/3.34  #Define  : 0
% 9.21/3.34  #Split   : 0
% 9.21/3.34  #Chain   : 0
% 9.21/3.34  #Close   : 0
% 9.21/3.34  
% 9.21/3.34  Ordering : KBO
% 9.21/3.34  
% 9.21/3.34  Simplification rules
% 9.21/3.34  ----------------------
% 9.21/3.34  #Subsume      : 686
% 9.21/3.34  #Demod        : 5951
% 9.21/3.34  #Tautology    : 1597
% 9.21/3.34  #SimpNegUnit  : 0
% 9.21/3.34  #BackRed      : 0
% 9.21/3.34  
% 9.21/3.34  #Partial instantiations: 0
% 9.21/3.34  #Strategies tried      : 1
% 9.21/3.34  
% 9.21/3.34  Timing (in seconds)
% 9.21/3.34  ----------------------
% 9.21/3.34  Preprocessing        : 0.27
% 9.21/3.34  Parsing              : 0.14
% 9.21/3.34  CNF conversion       : 0.02
% 9.21/3.34  Main loop            : 2.24
% 9.21/3.34  Inferencing          : 0.51
% 9.21/3.34  Reduction            : 1.31
% 9.21/3.34  Demodulation         : 1.18
% 9.21/3.34  BG Simplification    : 0.06
% 9.21/3.34  Subsumption          : 0.28
% 9.21/3.34  Abstraction          : 0.15
% 9.21/3.34  MUC search           : 0.00
% 9.21/3.34  Cooper               : 0.00
% 9.21/3.34  Total                : 2.53
% 9.21/3.34  Index Insertion      : 0.00
% 9.21/3.34  Index Deletion       : 0.00
% 9.21/3.34  Index Matching       : 0.00
% 9.21/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
