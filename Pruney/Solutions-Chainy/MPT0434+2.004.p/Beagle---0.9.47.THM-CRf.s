%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:16 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   47 (  99 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 144 expanded)
%              Number of equality atoms :   17 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_376,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(k1_relat_1(A_47),k1_relat_1(B_48)) = k1_relat_1(k2_xboole_0(A_47,B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_406,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(k1_relat_1(A_47),k1_relat_1(k2_xboole_0(A_47,B_48))) = k1_xboole_0
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_12])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k4_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(k4_xboole_0(A_36,B_37),C_38)
      | ~ r1_tarski(A_36,k2_xboole_0(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_167,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_153,c_25])).

tff(c_385,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_167])).

tff(c_418,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_8,c_385])).

tff(c_1378,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_1395,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1378])).

tff(c_1399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1395])).

tff(c_1401,plain,(
    v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_1495,plain,(
    ! [B_82,A_83] :
      ( k2_xboole_0(k1_relat_1(B_82),k1_relat_1(A_83)) = k1_relat_1(k2_xboole_0(A_83,B_82))
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_316,plain,(
    k4_xboole_0(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_1504,plain,
    ( k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2'))) != k1_xboole_0
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_316])).

tff(c_1567,plain,(
    k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_22,c_2,c_8,c_2,c_1504])).

tff(c_1580,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_1567])).

tff(c_1584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_1580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.56  
% 3.14/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.57  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.14/1.57  
% 3.14/1.57  %Foreground sorts:
% 3.14/1.57  
% 3.14/1.57  
% 3.14/1.57  %Background operators:
% 3.14/1.57  
% 3.14/1.57  
% 3.14/1.57  %Foreground operators:
% 3.14/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.57  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.14/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.57  
% 3.14/1.58  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 3.14/1.58  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 3.14/1.58  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.14/1.58  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 3.14/1.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.14/1.58  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.14/1.58  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.14/1.58  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.14/1.58  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.14/1.58  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.58  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.58  tff(c_376, plain, (![A_47, B_48]: (k2_xboole_0(k1_relat_1(A_47), k1_relat_1(B_48))=k1_relat_1(k2_xboole_0(A_47, B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.58  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.58  tff(c_406, plain, (![A_47, B_48]: (k4_xboole_0(k1_relat_1(A_47), k1_relat_1(k2_xboole_0(A_47, B_48)))=k1_xboole_0 | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_376, c_12])).
% 3.14/1.58  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k4_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.58  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.58  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.58  tff(c_153, plain, (![A_36, B_37, C_38]: (r1_tarski(k4_xboole_0(A_36, B_37), C_38) | ~r1_tarski(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.58  tff(c_14, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.58  tff(c_20, plain, (~r1_tarski(k6_subset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.58  tff(c_25, plain, (~r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 3.14/1.58  tff(c_167, plain, (~r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_153, c_25])).
% 3.14/1.58  tff(c_385, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_376, c_167])).
% 3.14/1.58  tff(c_418, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_8, c_385])).
% 3.14/1.58  tff(c_1378, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_418])).
% 3.14/1.58  tff(c_1395, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1378])).
% 3.14/1.58  tff(c_1399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1395])).
% 3.14/1.58  tff(c_1401, plain, (v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_418])).
% 3.14/1.58  tff(c_1495, plain, (![B_82, A_83]: (k2_xboole_0(k1_relat_1(B_82), k1_relat_1(A_83))=k1_relat_1(k2_xboole_0(A_83, B_82)) | ~v1_relat_1(B_82) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_376, c_2])).
% 3.14/1.58  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.58  tff(c_316, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_167])).
% 3.14/1.58  tff(c_1504, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')))!=k1_xboole_0 | ~v1_relat_1('#skF_2') | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1495, c_316])).
% 3.14/1.58  tff(c_1567, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_22, c_2, c_8, c_2, c_1504])).
% 3.14/1.58  tff(c_1580, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_406, c_1567])).
% 3.14/1.58  tff(c_1584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_1580])).
% 3.14/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.58  
% 3.14/1.58  Inference rules
% 3.14/1.58  ----------------------
% 3.14/1.58  #Ref     : 0
% 3.14/1.58  #Sup     : 413
% 3.14/1.58  #Fact    : 0
% 3.14/1.58  #Define  : 0
% 3.14/1.58  #Split   : 2
% 3.14/1.58  #Chain   : 0
% 3.14/1.58  #Close   : 0
% 3.14/1.58  
% 3.14/1.58  Ordering : KBO
% 3.14/1.58  
% 3.14/1.58  Simplification rules
% 3.14/1.58  ----------------------
% 3.14/1.58  #Subsume      : 24
% 3.14/1.58  #Demod        : 154
% 3.14/1.58  #Tautology    : 190
% 3.14/1.58  #SimpNegUnit  : 3
% 3.14/1.58  #BackRed      : 2
% 3.14/1.58  
% 3.14/1.58  #Partial instantiations: 0
% 3.14/1.58  #Strategies tried      : 1
% 3.14/1.58  
% 3.14/1.58  Timing (in seconds)
% 3.14/1.58  ----------------------
% 3.14/1.58  Preprocessing        : 0.31
% 3.14/1.58  Parsing              : 0.16
% 3.14/1.58  CNF conversion       : 0.02
% 3.14/1.58  Main loop            : 0.47
% 3.14/1.58  Inferencing          : 0.14
% 3.14/1.58  Reduction            : 0.20
% 3.14/1.58  Demodulation         : 0.16
% 3.14/1.58  BG Simplification    : 0.02
% 3.14/1.58  Subsumption          : 0.07
% 3.14/1.58  Abstraction          : 0.02
% 3.14/1.58  MUC search           : 0.00
% 3.14/1.58  Cooper               : 0.00
% 3.14/1.58  Total                : 0.80
% 3.14/1.58  Index Insertion      : 0.00
% 3.14/1.58  Index Deletion       : 0.00
% 3.14/1.58  Index Matching       : 0.00
% 3.14/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
