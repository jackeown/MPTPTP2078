%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:50 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  53 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)),k10_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(A_33,k2_xboole_0(B_34,C_35))
      | ~ r1_tarski(k4_xboole_0(A_33,B_34),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(B_34,k4_xboole_0(A_33,B_34))) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,(
    ! [C_49,A_50,B_51] :
      ( k2_xboole_0(k10_relat_1(C_49,A_50),k10_relat_1(C_49,B_51)) = k10_relat_1(C_49,k2_xboole_0(A_50,B_51))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_187,plain,(
    ! [C_52,A_53,B_54] :
      ( r1_tarski(k10_relat_1(C_52,A_53),k10_relat_1(C_52,k2_xboole_0(A_53,B_54)))
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_16])).

tff(c_198,plain,(
    ! [C_52,A_11,B_12] :
      ( r1_tarski(k10_relat_1(C_52,A_11),k10_relat_1(C_52,B_12))
      | ~ v1_relat_1(C_52)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_187])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] :
      ( k2_xboole_0(k10_relat_1(C_19,A_17),k10_relat_1(C_19,B_18)) = k10_relat_1(C_19,k2_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_110,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k4_xboole_0(A_41,B_42),C_43)
      | ~ r1_tarski(A_41,k2_xboole_0(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_15,B_16] : k6_subset_1(A_15,B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25,plain,(
    ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_119,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k2_xboole_0(k10_relat_1('#skF_3','#skF_2'),k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_110,c_25])).

tff(c_207,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_209,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_207])).

tff(c_212,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_198,c_209])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_24,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:42:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  
% 1.95/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.95/1.17  
% 1.95/1.17  %Foreground sorts:
% 1.95/1.17  
% 1.95/1.17  
% 1.95/1.17  %Background operators:
% 1.95/1.17  
% 1.95/1.17  
% 1.95/1.17  %Foreground operators:
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.95/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.17  
% 1.95/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.95/1.18  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.95/1.18  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B)), k10_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_relat_1)).
% 1.95/1.18  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.95/1.18  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 1.95/1.18  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.95/1.18  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.95/1.18  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.95/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.18  tff(c_73, plain, (![A_33, B_34, C_35]: (r1_tarski(A_33, k2_xboole_0(B_34, C_35)) | ~r1_tarski(k4_xboole_0(A_33, B_34), C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.18  tff(c_83, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(B_34, k4_xboole_0(A_33, B_34))))), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.95/1.18  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.18  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.18  tff(c_172, plain, (![C_49, A_50, B_51]: (k2_xboole_0(k10_relat_1(C_49, A_50), k10_relat_1(C_49, B_51))=k10_relat_1(C_49, k2_xboole_0(A_50, B_51)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.18  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.18  tff(c_187, plain, (![C_52, A_53, B_54]: (r1_tarski(k10_relat_1(C_52, A_53), k10_relat_1(C_52, k2_xboole_0(A_53, B_54))) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_172, c_16])).
% 1.95/1.18  tff(c_198, plain, (![C_52, A_11, B_12]: (r1_tarski(k10_relat_1(C_52, A_11), k10_relat_1(C_52, B_12)) | ~v1_relat_1(C_52) | ~r1_tarski(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_187])).
% 1.95/1.18  tff(c_20, plain, (![C_19, A_17, B_18]: (k2_xboole_0(k10_relat_1(C_19, A_17), k10_relat_1(C_19, B_18))=k10_relat_1(C_19, k2_xboole_0(A_17, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.18  tff(c_110, plain, (![A_41, B_42, C_43]: (r1_tarski(k4_xboole_0(A_41, B_42), C_43) | ~r1_tarski(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.18  tff(c_18, plain, (![A_15, B_16]: (k6_subset_1(A_15, B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.95/1.18  tff(c_22, plain, (~r1_tarski(k6_subset_1(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.18  tff(c_25, plain, (~r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 1.95/1.18  tff(c_119, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k2_xboole_0(k10_relat_1('#skF_3', '#skF_2'), k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_110, c_25])).
% 1.95/1.18  tff(c_207, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 1.95/1.18  tff(c_209, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_207])).
% 1.95/1.18  tff(c_212, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_198, c_209])).
% 1.95/1.18  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_24, c_212])).
% 1.95/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  Inference rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Ref     : 0
% 1.95/1.18  #Sup     : 46
% 1.95/1.18  #Fact    : 0
% 1.95/1.18  #Define  : 0
% 1.95/1.18  #Split   : 0
% 1.95/1.18  #Chain   : 0
% 1.95/1.18  #Close   : 0
% 1.95/1.18  
% 1.95/1.18  Ordering : KBO
% 1.95/1.18  
% 1.95/1.18  Simplification rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Subsume      : 5
% 1.95/1.18  #Demod        : 13
% 1.95/1.18  #Tautology    : 20
% 1.95/1.18  #SimpNegUnit  : 0
% 1.95/1.18  #BackRed      : 0
% 1.95/1.18  
% 1.95/1.18  #Partial instantiations: 0
% 1.95/1.18  #Strategies tried      : 1
% 1.95/1.18  
% 1.95/1.18  Timing (in seconds)
% 1.95/1.18  ----------------------
% 1.95/1.19  Preprocessing        : 0.28
% 1.95/1.19  Parsing              : 0.15
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.16
% 1.95/1.19  Inferencing          : 0.06
% 1.95/1.19  Reduction            : 0.05
% 1.95/1.19  Demodulation         : 0.04
% 1.95/1.19  BG Simplification    : 0.01
% 1.95/1.19  Subsumption          : 0.03
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.19  Cooper               : 0.00
% 1.95/1.19  Total                : 0.47
% 1.95/1.19  Index Insertion      : 0.00
% 1.95/1.19  Index Deletion       : 0.00
% 1.95/1.19  Index Matching       : 0.00
% 1.95/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
