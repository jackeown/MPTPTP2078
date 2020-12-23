%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:50 EST 2020

% Result     : Theorem 16.45s
% Output     : CNFRefutation 16.50s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  52 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)),k10_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(A_47,k2_xboole_0(B_48,C_49))
      | ~ r1_tarski(k4_xboole_0(A_47,B_48),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [A_53,B_54] : r1_tarski(A_53,k2_xboole_0(B_54,k4_xboole_0(A_53,B_54))) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1676,plain,(
    ! [A_111,B_112] : k2_xboole_0(A_111,k2_xboole_0(B_112,k4_xboole_0(A_111,B_112))) = k2_xboole_0(B_112,k4_xboole_0(A_111,B_112)) ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_163,plain,(
    ! [C_50,A_51,B_52] :
      ( k2_xboole_0(k10_relat_1(C_50,A_51),k10_relat_1(C_50,B_52)) = k10_relat_1(C_50,k2_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [C_50,A_51,B_52] :
      ( r1_tarski(k10_relat_1(C_50,A_51),k10_relat_1(C_50,k2_xboole_0(A_51,B_52)))
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_16])).

tff(c_32521,plain,(
    ! [C_394,A_395,B_396] :
      ( r1_tarski(k10_relat_1(C_394,A_395),k10_relat_1(C_394,k2_xboole_0(B_396,k4_xboole_0(A_395,B_396))))
      | ~ v1_relat_1(C_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_179])).

tff(c_24,plain,(
    ! [C_23,A_21,B_22] :
      ( k2_xboole_0(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k2_xboole_0(A_21,B_22))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_136,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(k4_xboole_0(A_44,B_45),C_46)
      | ~ r1_tarski(A_44,k2_xboole_0(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,(
    ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_26])).

tff(c_145,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k2_xboole_0(k10_relat_1('#skF_3','#skF_2'),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_136,c_29])).

tff(c_247,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_249,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_247])).

tff(c_32526,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32521,c_249])).

tff(c_32691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:21:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.45/5.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.50/5.95  
% 16.50/5.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.50/5.95  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 16.50/5.95  
% 16.50/5.95  %Foreground sorts:
% 16.50/5.95  
% 16.50/5.95  
% 16.50/5.95  %Background operators:
% 16.50/5.95  
% 16.50/5.95  
% 16.50/5.95  %Foreground operators:
% 16.50/5.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.50/5.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.50/5.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.50/5.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.50/5.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.50/5.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.50/5.95  tff('#skF_2', type, '#skF_2': $i).
% 16.50/5.95  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 16.50/5.95  tff('#skF_3', type, '#skF_3': $i).
% 16.50/5.95  tff('#skF_1', type, '#skF_1': $i).
% 16.50/5.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.50/5.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.50/5.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.50/5.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.50/5.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.50/5.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.50/5.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.50/5.95  
% 16.50/5.96  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B)), k10_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_relat_1)).
% 16.50/5.96  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.50/5.96  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 16.50/5.96  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.50/5.96  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 16.50/5.96  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.50/5.96  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 16.50/5.96  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 16.50/5.96  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.50/5.96  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.50/5.96  tff(c_148, plain, (![A_47, B_48, C_49]: (r1_tarski(A_47, k2_xboole_0(B_48, C_49)) | ~r1_tarski(k4_xboole_0(A_47, B_48), C_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.50/5.96  tff(c_191, plain, (![A_53, B_54]: (r1_tarski(A_53, k2_xboole_0(B_54, k4_xboole_0(A_53, B_54))))), inference(resolution, [status(thm)], [c_6, c_148])).
% 16.50/5.96  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.50/5.96  tff(c_1676, plain, (![A_111, B_112]: (k2_xboole_0(A_111, k2_xboole_0(B_112, k4_xboole_0(A_111, B_112)))=k2_xboole_0(B_112, k4_xboole_0(A_111, B_112)))), inference(resolution, [status(thm)], [c_191, c_10])).
% 16.50/5.96  tff(c_163, plain, (![C_50, A_51, B_52]: (k2_xboole_0(k10_relat_1(C_50, A_51), k10_relat_1(C_50, B_52))=k10_relat_1(C_50, k2_xboole_0(A_51, B_52)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.50/5.96  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.50/5.96  tff(c_179, plain, (![C_50, A_51, B_52]: (r1_tarski(k10_relat_1(C_50, A_51), k10_relat_1(C_50, k2_xboole_0(A_51, B_52))) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_163, c_16])).
% 16.50/5.96  tff(c_32521, plain, (![C_394, A_395, B_396]: (r1_tarski(k10_relat_1(C_394, A_395), k10_relat_1(C_394, k2_xboole_0(B_396, k4_xboole_0(A_395, B_396)))) | ~v1_relat_1(C_394))), inference(superposition, [status(thm), theory('equality')], [c_1676, c_179])).
% 16.50/5.96  tff(c_24, plain, (![C_23, A_21, B_22]: (k2_xboole_0(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k2_xboole_0(A_21, B_22)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.50/5.96  tff(c_136, plain, (![A_44, B_45, C_46]: (r1_tarski(k4_xboole_0(A_44, B_45), C_46) | ~r1_tarski(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.50/5.96  tff(c_20, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.50/5.96  tff(c_26, plain, (~r1_tarski(k6_subset_1(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.50/5.96  tff(c_29, plain, (~r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_26])).
% 16.50/5.96  tff(c_145, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k10_relat_1('#skF_3', '#skF_2'), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_136, c_29])).
% 16.50/5.96  tff(c_247, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_145])).
% 16.50/5.96  tff(c_249, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_247])).
% 16.50/5.96  tff(c_32526, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32521, c_249])).
% 16.50/5.96  tff(c_32691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_32526])).
% 16.50/5.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.50/5.96  
% 16.50/5.96  Inference rules
% 16.50/5.96  ----------------------
% 16.50/5.96  #Ref     : 0
% 16.50/5.96  #Sup     : 8189
% 16.50/5.96  #Fact    : 0
% 16.50/5.96  #Define  : 0
% 16.50/5.96  #Split   : 0
% 16.50/5.96  #Chain   : 0
% 16.50/5.96  #Close   : 0
% 16.50/5.96  
% 16.50/5.96  Ordering : KBO
% 16.50/5.96  
% 16.50/5.96  Simplification rules
% 16.50/5.96  ----------------------
% 16.50/5.96  #Subsume      : 1123
% 16.50/5.96  #Demod        : 6981
% 16.50/5.96  #Tautology    : 4209
% 16.50/5.96  #SimpNegUnit  : 0
% 16.50/5.96  #BackRed      : 5
% 16.50/5.96  
% 16.50/5.96  #Partial instantiations: 0
% 16.50/5.96  #Strategies tried      : 1
% 16.50/5.96  
% 16.50/5.96  Timing (in seconds)
% 16.50/5.96  ----------------------
% 16.50/5.96  Preprocessing        : 0.51
% 16.50/5.96  Parsing              : 0.27
% 16.50/5.96  CNF conversion       : 0.03
% 16.50/5.96  Main loop            : 4.59
% 16.50/5.96  Inferencing          : 1.17
% 16.50/5.96  Reduction            : 2.15
% 16.50/5.96  Demodulation         : 1.87
% 16.50/5.96  BG Simplification    : 0.15
% 16.50/5.96  Subsumption          : 0.89
% 16.50/5.96  Abstraction          : 0.26
% 16.50/5.96  MUC search           : 0.00
% 16.50/5.96  Cooper               : 0.00
% 16.50/5.96  Total                : 5.14
% 16.50/5.96  Index Insertion      : 0.00
% 16.50/5.96  Index Deletion       : 0.00
% 16.50/5.96  Index Matching       : 0.00
% 16.50/5.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
