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
% DateTime   : Thu Dec  3 10:01:50 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  43 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)),k10_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2103,plain,(
    ! [C_124,A_125,B_126] :
      ( k2_xboole_0(k10_relat_1(C_124,A_125),k10_relat_1(C_124,B_126)) = k10_relat_1(C_124,k2_xboole_0(A_125,B_126))
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6483,plain,(
    ! [C_200,A_201,B_202] :
      ( k4_xboole_0(k10_relat_1(C_200,A_201),k10_relat_1(C_200,k2_xboole_0(A_201,B_202))) = k1_xboole_0
      | ~ v1_relat_1(C_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2103,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_293,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | k4_xboole_0(A_58,B_59) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_51,plain,(
    ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_48])).

tff(c_301,plain,(
    k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_293,c_51])).

tff(c_1180,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k2_xboole_0(k10_relat_1('#skF_3','#skF_2'),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_2124,plain,
    ( k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')))) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2103,c_1180])).

tff(c_2187,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2,c_10,c_2124])).

tff(c_6510,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6483,c_2187])).

tff(c_6595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.17  
% 5.29/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.29/2.17  
% 5.29/2.17  %Foreground sorts:
% 5.29/2.17  
% 5.29/2.17  
% 5.29/2.17  %Background operators:
% 5.29/2.17  
% 5.29/2.17  
% 5.29/2.17  %Foreground operators:
% 5.29/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.29/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.29/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.29/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.29/2.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.29/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.29/2.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.29/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.29/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.29/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.29/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.29/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.29/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.29/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/2.17  
% 5.29/2.18  tff(f_98, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B)), k10_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_relat_1)).
% 5.29/2.18  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 5.29/2.18  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.29/2.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.29/2.18  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.29/2.18  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.29/2.18  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.29/2.18  tff(f_63, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.29/2.18  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.29/2.18  tff(c_2103, plain, (![C_124, A_125, B_126]: (k2_xboole_0(k10_relat_1(C_124, A_125), k10_relat_1(C_124, B_126))=k10_relat_1(C_124, k2_xboole_0(A_125, B_126)) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.29/2.18  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.29/2.18  tff(c_6483, plain, (![C_200, A_201, B_202]: (k4_xboole_0(k10_relat_1(C_200, A_201), k10_relat_1(C_200, k2_xboole_0(A_201, B_202)))=k1_xboole_0 | ~v1_relat_1(C_200))), inference(superposition, [status(thm), theory('equality')], [c_2103, c_16])).
% 5.29/2.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.29/2.18  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.29/2.18  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.29/2.18  tff(c_293, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | k4_xboole_0(A_58, B_59)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.29/2.18  tff(c_28, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.29/2.18  tff(c_48, plain, (~r1_tarski(k6_subset_1(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.29/2.18  tff(c_51, plain, (~r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_48])).
% 5.29/2.18  tff(c_301, plain, (k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_293, c_51])).
% 5.29/2.18  tff(c_1180, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k10_relat_1('#skF_3', '#skF_2'), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_301])).
% 5.29/2.18  tff(c_2124, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2103, c_1180])).
% 5.29/2.18  tff(c_2187, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2, c_10, c_2124])).
% 5.29/2.18  tff(c_6510, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6483, c_2187])).
% 5.29/2.18  tff(c_6595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_6510])).
% 5.29/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.18  
% 5.29/2.18  Inference rules
% 5.29/2.18  ----------------------
% 5.29/2.18  #Ref     : 0
% 5.29/2.18  #Sup     : 1607
% 5.29/2.18  #Fact    : 0
% 5.29/2.18  #Define  : 0
% 5.29/2.18  #Split   : 3
% 5.29/2.18  #Chain   : 0
% 5.29/2.18  #Close   : 0
% 5.29/2.18  
% 5.29/2.18  Ordering : KBO
% 5.29/2.18  
% 5.29/2.18  Simplification rules
% 5.29/2.18  ----------------------
% 5.29/2.18  #Subsume      : 106
% 5.29/2.18  #Demod        : 1393
% 5.29/2.18  #Tautology    : 1069
% 5.29/2.18  #SimpNegUnit  : 2
% 5.29/2.18  #BackRed      : 2
% 5.29/2.18  
% 5.29/2.18  #Partial instantiations: 0
% 5.29/2.18  #Strategies tried      : 1
% 5.29/2.18  
% 5.29/2.18  Timing (in seconds)
% 5.29/2.18  ----------------------
% 5.29/2.18  Preprocessing        : 0.31
% 5.29/2.18  Parsing              : 0.17
% 5.29/2.18  CNF conversion       : 0.02
% 5.29/2.18  Main loop            : 1.10
% 5.29/2.18  Inferencing          : 0.31
% 5.29/2.18  Reduction            : 0.53
% 5.29/2.18  Demodulation         : 0.44
% 5.29/2.18  BG Simplification    : 0.04
% 5.29/2.18  Subsumption          : 0.16
% 5.29/2.18  Abstraction          : 0.05
% 5.29/2.18  MUC search           : 0.00
% 5.29/2.18  Cooper               : 0.00
% 5.29/2.18  Total                : 1.44
% 5.29/2.18  Index Insertion      : 0.00
% 5.29/2.18  Index Deletion       : 0.00
% 5.29/2.18  Index Matching       : 0.00
% 5.29/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
