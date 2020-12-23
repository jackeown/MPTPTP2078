%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:16 EST 2020

% Result     : Theorem 10.88s
% Output     : CNFRefutation 10.88s
% Verified   : 
% Statistics : Number of formulae       :   47 (  78 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 116 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( k2_xboole_0(k1_relat_1(A_17),k1_relat_1(B_19)) = k1_relat_1(k2_xboole_0(A_17,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,k2_xboole_0(C_34,B_35))
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_510,plain,(
    ! [A_57,C_58,B_59] :
      ( k4_xboole_0(A_57,k2_xboole_0(C_58,B_59)) = k1_xboole_0
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(resolution,[status(thm)],[c_82,c_10])).

tff(c_29020,plain,(
    ! [A_379,A_380,B_381] :
      ( k4_xboole_0(A_379,k1_relat_1(k2_xboole_0(A_380,B_381))) = k1_xboole_0
      | ~ r1_tarski(A_379,k1_relat_1(B_381))
      | ~ v1_relat_1(B_381)
      | ~ v1_relat_1(A_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_510])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k4_xboole_0(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_387,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(k1_relat_1(A_49),k1_relat_1(B_50)) = k1_relat_1(k2_xboole_0(A_49,B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_70,plain,(
    k4_xboole_0(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_29])).

tff(c_199,plain,(
    k4_xboole_0(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_70])).

tff(c_393,plain,
    ( k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')))) != k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_199])).

tff(c_413,plain,
    ( k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2','#skF_1'))) != k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14,c_393])).

tff(c_475,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_478,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_475])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_478])).

tff(c_483,plain,(
    k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_29148,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_29020,c_483])).

tff(c_29304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_6,c_29148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:44:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.88/4.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.88/4.72  
% 10.88/4.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.88/4.72  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.88/4.72  
% 10.88/4.72  %Foreground sorts:
% 10.88/4.72  
% 10.88/4.72  
% 10.88/4.72  %Background operators:
% 10.88/4.72  
% 10.88/4.72  
% 10.88/4.72  %Foreground operators:
% 10.88/4.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.88/4.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.88/4.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.88/4.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.88/4.72  tff('#skF_2', type, '#skF_2': $i).
% 10.88/4.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.88/4.72  tff('#skF_1', type, '#skF_1': $i).
% 10.88/4.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.88/4.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.88/4.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.88/4.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.88/4.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.88/4.72  
% 10.88/4.74  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 10.88/4.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.88/4.74  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 10.88/4.74  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 10.88/4.74  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.88/4.74  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 10.88/4.74  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.88/4.74  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.88/4.74  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.88/4.74  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.88/4.74  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.88/4.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.88/4.74  tff(c_22, plain, (![A_17, B_19]: (k2_xboole_0(k1_relat_1(A_17), k1_relat_1(B_19))=k1_relat_1(k2_xboole_0(A_17, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.88/4.74  tff(c_82, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, k2_xboole_0(C_34, B_35)) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.88/4.74  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.88/4.74  tff(c_510, plain, (![A_57, C_58, B_59]: (k4_xboole_0(A_57, k2_xboole_0(C_58, B_59))=k1_xboole_0 | ~r1_tarski(A_57, B_59))), inference(resolution, [status(thm)], [c_82, c_10])).
% 10.88/4.74  tff(c_29020, plain, (![A_379, A_380, B_381]: (k4_xboole_0(A_379, k1_relat_1(k2_xboole_0(A_380, B_381)))=k1_xboole_0 | ~r1_tarski(A_379, k1_relat_1(B_381)) | ~v1_relat_1(B_381) | ~v1_relat_1(A_380))), inference(superposition, [status(thm), theory('equality')], [c_22, c_510])).
% 10.88/4.74  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k4_xboole_0(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.88/4.74  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.88/4.74  tff(c_387, plain, (![A_49, B_50]: (k2_xboole_0(k1_relat_1(A_49), k1_relat_1(B_50))=k1_relat_1(k2_xboole_0(A_49, B_50)) | ~v1_relat_1(B_50) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.88/4.74  tff(c_16, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.88/4.74  tff(c_63, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | k4_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.88/4.74  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.88/4.74  tff(c_24, plain, (~r1_tarski(k6_subset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.88/4.74  tff(c_29, plain, (~r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 10.88/4.74  tff(c_70, plain, (k4_xboole_0(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_29])).
% 10.88/4.74  tff(c_199, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_70])).
% 10.88/4.74  tff(c_393, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))))!=k1_xboole_0 | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_387, c_199])).
% 10.88/4.74  tff(c_413, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', '#skF_1')))!=k1_xboole_0 | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14, c_393])).
% 10.88/4.74  tff(c_475, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_413])).
% 10.88/4.74  tff(c_478, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_475])).
% 10.88/4.74  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_478])).
% 10.88/4.74  tff(c_483, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', '#skF_1')))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_413])).
% 10.88/4.74  tff(c_29148, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_29020, c_483])).
% 10.88/4.74  tff(c_29304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_6, c_29148])).
% 10.88/4.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.88/4.74  
% 10.88/4.74  Inference rules
% 10.88/4.74  ----------------------
% 10.88/4.74  #Ref     : 0
% 10.88/4.74  #Sup     : 7057
% 10.88/4.74  #Fact    : 0
% 10.88/4.74  #Define  : 0
% 10.88/4.74  #Split   : 2
% 10.88/4.74  #Chain   : 0
% 10.88/4.74  #Close   : 0
% 10.88/4.74  
% 10.88/4.74  Ordering : KBO
% 10.88/4.74  
% 10.88/4.74  Simplification rules
% 10.88/4.74  ----------------------
% 10.88/4.74  #Subsume      : 529
% 10.88/4.74  #Demod        : 6729
% 10.88/4.74  #Tautology    : 3714
% 10.88/4.74  #SimpNegUnit  : 3
% 10.88/4.74  #BackRed      : 25
% 10.88/4.74  
% 10.88/4.74  #Partial instantiations: 0
% 10.88/4.74  #Strategies tried      : 1
% 10.88/4.74  
% 10.88/4.74  Timing (in seconds)
% 10.88/4.74  ----------------------
% 10.88/4.74  Preprocessing        : 0.29
% 10.88/4.74  Parsing              : 0.15
% 10.88/4.74  CNF conversion       : 0.02
% 10.88/4.74  Main loop            : 3.69
% 10.88/4.74  Inferencing          : 0.71
% 10.88/4.74  Reduction            : 1.94
% 10.88/4.74  Demodulation         : 1.72
% 10.88/4.74  BG Simplification    : 0.09
% 10.88/4.74  Subsumption          : 0.77
% 10.88/4.74  Abstraction          : 0.13
% 10.88/4.74  MUC search           : 0.00
% 10.88/4.74  Cooper               : 0.00
% 10.88/4.74  Total                : 4.02
% 10.88/4.74  Index Insertion      : 0.00
% 10.88/4.74  Index Deletion       : 0.00
% 10.88/4.74  Index Matching       : 0.00
% 10.88/4.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
