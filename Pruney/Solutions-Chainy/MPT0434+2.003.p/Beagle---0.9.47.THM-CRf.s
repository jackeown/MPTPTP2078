%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:16 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 ( 112 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_245,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(k1_relat_1(A_53),k1_relat_1(B_54)) = k1_relat_1(k2_xboole_0(A_53,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_281,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_relat_1(A_53),k1_relat_1(k2_xboole_0(A_53,B_54)))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_6])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k4_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_30,A_31] : k3_tarski(k2_tarski(B_30,A_31)) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_172,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k4_xboole_0(A_38,B_39),C_40)
      | ~ r1_tarski(A_38,k2_xboole_0(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_18])).

tff(c_176,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_172,c_23])).

tff(c_263,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_176])).

tff(c_293,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_89,c_2,c_263])).

tff(c_309,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_312,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_309])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_312])).

tff(c_317,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_321,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_281,c_317])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_relat_1 > #skF_2 > #skF_1
% 2.10/1.23  
% 2.10/1.23  %Foreground sorts:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Background operators:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Foreground operators:
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.10/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.23  
% 2.10/1.25  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 2.10/1.25  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 2.10/1.25  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.25  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.10/1.25  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.10/1.25  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.10/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.10/1.25  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.10/1.25  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.10/1.25  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.25  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.25  tff(c_245, plain, (![A_53, B_54]: (k2_xboole_0(k1_relat_1(A_53), k1_relat_1(B_54))=k1_relat_1(k2_xboole_0(A_53, B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.25  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.25  tff(c_281, plain, (![A_53, B_54]: (r1_tarski(k1_relat_1(A_53), k1_relat_1(k2_xboole_0(A_53, B_54))) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_245, c_6])).
% 2.10/1.25  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k4_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.25  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.25  tff(c_68, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.25  tff(c_83, plain, (![B_30, A_31]: (k3_tarski(k2_tarski(B_30, A_31))=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.10/1.25  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.25  tff(c_89, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_83, c_10])).
% 2.10/1.25  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.25  tff(c_172, plain, (![A_38, B_39, C_40]: (r1_tarski(k4_xboole_0(A_38, B_39), C_40) | ~r1_tarski(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.25  tff(c_12, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.25  tff(c_18, plain, (~r1_tarski(k6_subset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.25  tff(c_23, plain, (~r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_18])).
% 2.10/1.25  tff(c_176, plain, (~r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_172, c_23])).
% 2.10/1.25  tff(c_263, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_245, c_176])).
% 2.10/1.25  tff(c_293, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_89, c_2, c_263])).
% 2.10/1.25  tff(c_309, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_293])).
% 2.10/1.25  tff(c_312, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_309])).
% 2.10/1.25  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_312])).
% 2.10/1.25  tff(c_317, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_293])).
% 2.10/1.25  tff(c_321, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_281, c_317])).
% 2.10/1.25  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_321])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 76
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 1
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 1
% 2.10/1.25  #Demod        : 24
% 2.10/1.25  #Tautology    : 42
% 2.10/1.25  #SimpNegUnit  : 0
% 2.10/1.25  #BackRed      : 0
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.28
% 2.10/1.25  Parsing              : 0.15
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.21
% 2.10/1.25  Inferencing          : 0.07
% 2.10/1.25  Reduction            : 0.07
% 2.10/1.25  Demodulation         : 0.06
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.04
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.51
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.25  Index Matching       : 0.00
% 2.10/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
