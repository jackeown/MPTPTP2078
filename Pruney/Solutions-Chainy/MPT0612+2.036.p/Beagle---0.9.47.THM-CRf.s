%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:46 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  65 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_xboole_0(A_22,k4_xboole_0(C_23,B_24))
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [C_23,B_24,A_22] :
      ( r1_xboole_0(k4_xboole_0(C_23,B_24),A_22)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [B_28,A_29] :
      ( k7_relat_1(B_28,A_29) = B_28
      | ~ r1_tarski(k1_relat_1(B_28),A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [B_28] :
      ( k7_relat_1(B_28,k1_zfmisc_1(k3_tarski(k1_relat_1(B_28)))) = B_28
      | ~ v1_relat_1(B_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_8,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k6_subset_1(k7_relat_1(C_11,A_9),k7_relat_1(C_11,B_10)) = k7_relat_1(C_11,k6_subset_1(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [C_34,A_35,B_36] :
      ( k4_xboole_0(k7_relat_1(C_34,A_35),k7_relat_1(C_34,B_36)) = k7_relat_1(C_34,k4_xboole_0(A_35,B_36))
      | ~ v1_relat_1(C_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_227,plain,(
    ! [B_58,B_59] :
      ( k7_relat_1(B_58,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(B_58))),B_59)) = k4_xboole_0(B_58,k7_relat_1(B_58,B_59))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_83])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3874,plain,(
    ! [B_269,B_270,B_271] :
      ( k7_relat_1(k4_xboole_0(B_269,k7_relat_1(B_269,B_270)),B_271) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(B_269))),B_270),B_271)
      | ~ v1_relat_1(B_269)
      | ~ v1_relat_1(B_269)
      | ~ v1_relat_1(B_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_12])).

tff(c_3918,plain,(
    ! [B_277,B_278,A_279] :
      ( k7_relat_1(k4_xboole_0(B_277,k7_relat_1(B_277,B_278)),A_279) = k1_xboole_0
      | ~ v1_relat_1(B_277)
      | ~ r1_tarski(A_279,B_278) ) ),
    inference(resolution,[status(thm)],[c_37,c_3874])).

tff(c_16,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_4085,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3918,c_21])).

tff(c_4225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_4085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.18  
% 5.85/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.18  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.85/2.18  
% 5.85/2.18  %Foreground sorts:
% 5.85/2.18  
% 5.85/2.18  
% 5.85/2.18  %Background operators:
% 5.85/2.18  
% 5.85/2.18  
% 5.85/2.18  %Foreground operators:
% 5.85/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.85/2.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.85/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.85/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.85/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.85/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.85/2.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.85/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.85/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.85/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.85/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.85/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.85/2.18  
% 5.85/2.19  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 5.85/2.19  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.85/2.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.85/2.19  tff(f_35, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 5.85/2.19  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.85/2.19  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.85/2.19  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 5.85/2.19  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 5.85/2.19  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.19  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.19  tff(c_34, plain, (![A_22, C_23, B_24]: (r1_xboole_0(A_22, k4_xboole_0(C_23, B_24)) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.85/2.19  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.85/2.19  tff(c_37, plain, (![C_23, B_24, A_22]: (r1_xboole_0(k4_xboole_0(C_23, B_24), A_22) | ~r1_tarski(A_22, B_24))), inference(resolution, [status(thm)], [c_34, c_2])).
% 5.85/2.19  tff(c_6, plain, (![A_6]: (r1_tarski(A_6, k1_zfmisc_1(k3_tarski(A_6))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.85/2.19  tff(c_42, plain, (![B_28, A_29]: (k7_relat_1(B_28, A_29)=B_28 | ~r1_tarski(k1_relat_1(B_28), A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.85/2.19  tff(c_47, plain, (![B_28]: (k7_relat_1(B_28, k1_zfmisc_1(k3_tarski(k1_relat_1(B_28))))=B_28 | ~v1_relat_1(B_28))), inference(resolution, [status(thm)], [c_6, c_42])).
% 5.85/2.19  tff(c_8, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.85/2.19  tff(c_10, plain, (![C_11, A_9, B_10]: (k6_subset_1(k7_relat_1(C_11, A_9), k7_relat_1(C_11, B_10))=k7_relat_1(C_11, k6_subset_1(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.85/2.19  tff(c_83, plain, (![C_34, A_35, B_36]: (k4_xboole_0(k7_relat_1(C_34, A_35), k7_relat_1(C_34, B_36))=k7_relat_1(C_34, k4_xboole_0(A_35, B_36)) | ~v1_relat_1(C_34))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_10])).
% 5.85/2.19  tff(c_227, plain, (![B_58, B_59]: (k7_relat_1(B_58, k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(B_58))), B_59))=k4_xboole_0(B_58, k7_relat_1(B_58, B_59)) | ~v1_relat_1(B_58) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_47, c_83])).
% 5.85/2.19  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.85/2.19  tff(c_3874, plain, (![B_269, B_270, B_271]: (k7_relat_1(k4_xboole_0(B_269, k7_relat_1(B_269, B_270)), B_271)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(B_269))), B_270), B_271) | ~v1_relat_1(B_269) | ~v1_relat_1(B_269) | ~v1_relat_1(B_269))), inference(superposition, [status(thm), theory('equality')], [c_227, c_12])).
% 5.85/2.19  tff(c_3918, plain, (![B_277, B_278, A_279]: (k7_relat_1(k4_xboole_0(B_277, k7_relat_1(B_277, B_278)), A_279)=k1_xboole_0 | ~v1_relat_1(B_277) | ~r1_tarski(A_279, B_278))), inference(resolution, [status(thm)], [c_37, c_3874])).
% 5.85/2.19  tff(c_16, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.19  tff(c_21, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 5.85/2.19  tff(c_4085, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3918, c_21])).
% 5.85/2.19  tff(c_4225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_4085])).
% 5.85/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.19  
% 5.85/2.19  Inference rules
% 5.85/2.19  ----------------------
% 5.85/2.19  #Ref     : 0
% 5.85/2.19  #Sup     : 1354
% 5.85/2.19  #Fact    : 0
% 5.85/2.19  #Define  : 0
% 5.85/2.19  #Split   : 4
% 5.85/2.19  #Chain   : 0
% 5.85/2.19  #Close   : 0
% 5.85/2.19  
% 5.85/2.19  Ordering : KBO
% 5.85/2.19  
% 5.85/2.19  Simplification rules
% 5.85/2.19  ----------------------
% 5.85/2.19  #Subsume      : 322
% 5.85/2.19  #Demod        : 5
% 5.85/2.19  #Tautology    : 93
% 5.85/2.19  #SimpNegUnit  : 0
% 5.85/2.19  #BackRed      : 0
% 5.85/2.19  
% 5.85/2.19  #Partial instantiations: 0
% 5.85/2.19  #Strategies tried      : 1
% 5.85/2.19  
% 5.85/2.19  Timing (in seconds)
% 5.85/2.19  ----------------------
% 5.85/2.19  Preprocessing        : 0.28
% 5.85/2.19  Parsing              : 0.15
% 5.85/2.20  CNF conversion       : 0.02
% 5.85/2.20  Main loop            : 1.15
% 5.85/2.20  Inferencing          : 0.38
% 5.85/2.20  Reduction            : 0.31
% 5.85/2.20  Demodulation         : 0.21
% 5.85/2.20  BG Simplification    : 0.06
% 5.85/2.20  Subsumption          : 0.34
% 5.85/2.20  Abstraction          : 0.06
% 5.85/2.20  MUC search           : 0.00
% 5.85/2.20  Cooper               : 0.00
% 5.85/2.20  Total                : 1.45
% 5.85/2.20  Index Insertion      : 0.00
% 5.85/2.20  Index Deletion       : 0.00
% 5.85/2.20  Index Matching       : 0.00
% 5.85/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
