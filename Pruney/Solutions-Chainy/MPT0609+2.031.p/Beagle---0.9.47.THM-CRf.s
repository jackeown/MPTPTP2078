%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [B_27,A_28] :
      ( k7_relat_1(B_27,A_28) = B_27
      | ~ r1_tarski(k1_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [B_27] :
      ( k7_relat_1(B_27,k1_relat_1(B_27)) = B_27
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_10,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( k6_subset_1(k7_relat_1(C_11,A_9),k7_relat_1(C_11,B_10)) = k7_relat_1(C_11,k6_subset_1(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [C_36,A_37,B_38] :
      ( k4_xboole_0(k7_relat_1(C_36,A_37),k7_relat_1(C_36,B_38)) = k7_relat_1(C_36,k4_xboole_0(A_37,B_38))
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_163,plain,(
    ! [B_39,B_40] :
      ( k7_relat_1(B_39,k4_xboole_0(k1_relat_1(B_39),B_40)) = k4_xboole_0(B_39,k7_relat_1(B_39,B_40))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_148])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,k6_subset_1(k1_relat_1(B_13),A_12))) = k6_subset_1(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,k4_xboole_0(k1_relat_1(B_13),A_12))) = k4_xboole_0(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_307,plain,(
    ! [B_46,B_47] :
      ( k1_relat_1(k4_xboole_0(B_46,k7_relat_1(B_46,B_47))) = k4_xboole_0(k1_relat_1(B_46),B_47)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_26])).

tff(c_79,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(k1_relat_1(B_30),A_31) = k1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [B_34,A_35] :
      ( k4_xboole_0(k1_relat_1(B_34),k1_relat_1(k7_relat_1(B_34,A_35))) = k4_xboole_0(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_8])).

tff(c_22,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_22])).

tff(c_129,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_25])).

tff(c_144,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_129])).

tff(c_322,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_144])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.32  
% 2.33/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.33/1.33  
% 2.33/1.33  %Foreground sorts:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Background operators:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Foreground operators:
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.33/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.33  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.33/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.33  
% 2.33/1.34  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.33/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.34  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.33/1.34  tff(f_35, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.33/1.34  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 2.33/1.34  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 2.33/1.34  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.33/1.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.33/1.34  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.34  tff(c_64, plain, (![B_27, A_28]: (k7_relat_1(B_27, A_28)=B_27 | ~r1_tarski(k1_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.34  tff(c_69, plain, (![B_27]: (k7_relat_1(B_27, k1_relat_1(B_27))=B_27 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_6, c_64])).
% 2.33/1.34  tff(c_10, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.34  tff(c_14, plain, (![C_11, A_9, B_10]: (k6_subset_1(k7_relat_1(C_11, A_9), k7_relat_1(C_11, B_10))=k7_relat_1(C_11, k6_subset_1(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.34  tff(c_148, plain, (![C_36, A_37, B_38]: (k4_xboole_0(k7_relat_1(C_36, A_37), k7_relat_1(C_36, B_38))=k7_relat_1(C_36, k4_xboole_0(A_37, B_38)) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 2.33/1.34  tff(c_163, plain, (![B_39, B_40]: (k7_relat_1(B_39, k4_xboole_0(k1_relat_1(B_39), B_40))=k4_xboole_0(B_39, k7_relat_1(B_39, B_40)) | ~v1_relat_1(B_39) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_69, c_148])).
% 2.33/1.34  tff(c_16, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, k6_subset_1(k1_relat_1(B_13), A_12)))=k6_subset_1(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.34  tff(c_26, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, k4_xboole_0(k1_relat_1(B_13), A_12)))=k4_xboole_0(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.33/1.34  tff(c_307, plain, (![B_46, B_47]: (k1_relat_1(k4_xboole_0(B_46, k7_relat_1(B_46, B_47)))=k4_xboole_0(k1_relat_1(B_46), B_47) | ~v1_relat_1(B_46) | ~v1_relat_1(B_46) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_163, c_26])).
% 2.33/1.34  tff(c_79, plain, (![B_30, A_31]: (k3_xboole_0(k1_relat_1(B_30), A_31)=k1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.33/1.34  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.34  tff(c_120, plain, (![B_34, A_35]: (k4_xboole_0(k1_relat_1(B_34), k1_relat_1(k7_relat_1(B_34, A_35)))=k4_xboole_0(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_79, c_8])).
% 2.33/1.34  tff(c_22, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.34  tff(c_25, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_22])).
% 2.33/1.34  tff(c_129, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_25])).
% 2.33/1.34  tff(c_144, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_129])).
% 2.33/1.34  tff(c_322, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_307, c_144])).
% 2.33/1.34  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_322])).
% 2.33/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  Inference rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Ref     : 0
% 2.33/1.34  #Sup     : 87
% 2.33/1.34  #Fact    : 0
% 2.33/1.34  #Define  : 0
% 2.33/1.34  #Split   : 0
% 2.33/1.34  #Chain   : 0
% 2.33/1.34  #Close   : 0
% 2.33/1.34  
% 2.33/1.34  Ordering : KBO
% 2.33/1.34  
% 2.33/1.34  Simplification rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Subsume      : 2
% 2.33/1.34  #Demod        : 13
% 2.33/1.34  #Tautology    : 27
% 2.33/1.34  #SimpNegUnit  : 0
% 2.33/1.34  #BackRed      : 0
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.34  Preprocessing        : 0.30
% 2.33/1.34  Parsing              : 0.16
% 2.33/1.34  CNF conversion       : 0.02
% 2.33/1.34  Main loop            : 0.22
% 2.33/1.34  Inferencing          : 0.09
% 2.33/1.34  Reduction            : 0.06
% 2.33/1.34  Demodulation         : 0.05
% 2.33/1.34  BG Simplification    : 0.02
% 2.33/1.34  Subsumption          : 0.04
% 2.33/1.34  Abstraction          : 0.02
% 2.33/1.34  MUC search           : 0.00
% 2.33/1.34  Cooper               : 0.00
% 2.33/1.34  Total                : 0.54
% 2.33/1.34  Index Insertion      : 0.00
% 2.33/1.34  Index Deletion       : 0.00
% 2.33/1.34  Index Matching       : 0.00
% 2.33/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
