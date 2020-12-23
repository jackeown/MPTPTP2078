%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:16 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  82 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 114 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_656,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(k1_relat_1(A_64),k1_relat_1(B_65)) = k1_relat_1(k2_xboole_0(A_64,B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1495,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(k1_relat_1(A_85),k1_relat_1(k2_xboole_0(A_85,B_86))) = k1_xboole_0
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_12])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14])).

tff(c_127,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_135,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_380,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k4_xboole_0(A_52,B_53),C_54)
      | ~ r1_tarski(A_52,k2_xboole_0(B_53,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_27,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_406,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_380,c_27])).

tff(c_674,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_406])).

tff(c_711,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_8,c_674])).

tff(c_1481,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_1484,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_135,c_1481])).

tff(c_1488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1484])).

tff(c_1489,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_1494,plain,(
    k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1489])).

tff(c_1501,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_1494])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.58  
% 3.19/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.59  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.19/1.59  
% 3.19/1.59  %Foreground sorts:
% 3.19/1.59  
% 3.19/1.59  
% 3.19/1.59  %Background operators:
% 3.19/1.59  
% 3.19/1.59  
% 3.19/1.59  %Foreground operators:
% 3.19/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.59  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.19/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.59  
% 3.19/1.60  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 3.19/1.60  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 3.19/1.60  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.19/1.60  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.19/1.60  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.19/1.60  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.19/1.60  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.19/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.19/1.60  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.19/1.60  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.19/1.60  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.60  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.60  tff(c_656, plain, (![A_64, B_65]: (k2_xboole_0(k1_relat_1(A_64), k1_relat_1(B_65))=k1_relat_1(k2_xboole_0(A_64, B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.60  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.60  tff(c_1495, plain, (![A_85, B_86]: (k4_xboole_0(k1_relat_1(A_85), k1_relat_1(k2_xboole_0(A_85, B_86)))=k1_xboole_0 | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_656, c_12])).
% 3.19/1.60  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.60  tff(c_16, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.60  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k6_subset_1(A_12, B_13), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.60  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(k4_xboole_0(A_12, B_13), k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14])).
% 3.19/1.60  tff(c_127, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.19/1.60  tff(c_135, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_28, c_127])).
% 3.19/1.60  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.60  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.60  tff(c_380, plain, (![A_52, B_53, C_54]: (r1_tarski(k4_xboole_0(A_52, B_53), C_54) | ~r1_tarski(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.60  tff(c_22, plain, (~r1_tarski(k6_subset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.19/1.60  tff(c_27, plain, (~r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 3.19/1.60  tff(c_406, plain, (~r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_380, c_27])).
% 3.19/1.60  tff(c_674, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_656, c_406])).
% 3.19/1.60  tff(c_711, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_8, c_674])).
% 3.19/1.60  tff(c_1481, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_711])).
% 3.19/1.60  tff(c_1484, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_135, c_1481])).
% 3.19/1.60  tff(c_1488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1484])).
% 3.19/1.60  tff(c_1489, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_711])).
% 3.19/1.60  tff(c_1494, plain, (k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_1489])).
% 3.19/1.60  tff(c_1501, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1495, c_1494])).
% 3.19/1.60  tff(c_1554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1501])).
% 3.19/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.60  
% 3.19/1.60  Inference rules
% 3.19/1.60  ----------------------
% 3.19/1.60  #Ref     : 0
% 3.19/1.60  #Sup     : 410
% 3.19/1.60  #Fact    : 0
% 3.19/1.60  #Define  : 0
% 3.19/1.60  #Split   : 2
% 3.19/1.60  #Chain   : 0
% 3.19/1.60  #Close   : 0
% 3.19/1.60  
% 3.19/1.60  Ordering : KBO
% 3.19/1.60  
% 3.19/1.60  Simplification rules
% 3.19/1.60  ----------------------
% 3.19/1.60  #Subsume      : 16
% 3.19/1.60  #Demod        : 141
% 3.19/1.60  #Tautology    : 174
% 3.19/1.60  #SimpNegUnit  : 3
% 3.19/1.60  #BackRed      : 2
% 3.19/1.60  
% 3.19/1.60  #Partial instantiations: 0
% 3.19/1.60  #Strategies tried      : 1
% 3.19/1.60  
% 3.19/1.60  Timing (in seconds)
% 3.19/1.60  ----------------------
% 3.19/1.60  Preprocessing        : 0.33
% 3.19/1.60  Parsing              : 0.18
% 3.19/1.60  CNF conversion       : 0.02
% 3.19/1.60  Main loop            : 0.49
% 3.19/1.60  Inferencing          : 0.16
% 3.19/1.60  Reduction            : 0.20
% 3.19/1.60  Demodulation         : 0.17
% 3.19/1.60  BG Simplification    : 0.02
% 3.19/1.60  Subsumption          : 0.07
% 3.19/1.60  Abstraction          : 0.03
% 3.19/1.60  MUC search           : 0.00
% 3.19/1.60  Cooper               : 0.00
% 3.19/1.60  Total                : 0.84
% 3.19/1.60  Index Insertion      : 0.00
% 3.19/1.60  Index Deletion       : 0.00
% 3.19/1.60  Index Matching       : 0.00
% 3.19/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
