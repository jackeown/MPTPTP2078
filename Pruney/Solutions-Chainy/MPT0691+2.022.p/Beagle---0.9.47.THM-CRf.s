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
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 344 expanded)
%              Number of leaves         :   25 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :   88 ( 489 expanded)
%              Number of equality atoms :   30 ( 262 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_167,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(k1_relat_1(B_36),A_37) = k1_relat_1(k7_relat_1(B_36,A_37))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(B_28,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,A_27) = k3_xboole_0(A_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_6])).

tff(c_190,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,k1_relat_1(B_39)) = k1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_89])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_74,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_206,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_78])).

tff(c_227,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_206])).

tff(c_173,plain,(
    ! [A_37,B_36] :
      ( k3_xboole_0(A_37,k1_relat_1(B_36)) = k1_relat_1(k7_relat_1(B_36,A_37))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_89])).

tff(c_234,plain,(
    ! [A_37] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_37)) = k3_xboole_0(A_37,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_173])).

tff(c_386,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_389,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_389])).

tff(c_395,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_394,plain,(
    ! [A_37] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_37)) = k3_xboole_0(A_37,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_12,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_255,plain,(
    ! [A_40,C_41,B_42] :
      ( k3_xboole_0(A_40,k10_relat_1(C_41,B_42)) = k10_relat_1(k7_relat_1(C_41,A_40),B_42)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_481,plain,(
    ! [C_53,B_54,B_55] :
      ( k10_relat_1(k7_relat_1(C_53,k1_relat_1(B_54)),B_55) = k1_relat_1(k7_relat_1(B_54,k10_relat_1(C_53,B_55)))
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_255])).

tff(c_2418,plain,(
    ! [B_87,C_88] :
      ( k1_relat_1(k7_relat_1(B_87,k10_relat_1(C_88,k2_relat_1(k7_relat_1(C_88,k1_relat_1(B_87)))))) = k1_relat_1(k7_relat_1(C_88,k1_relat_1(B_87)))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(k7_relat_1(C_88,k1_relat_1(B_87))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_481])).

tff(c_2503,plain,(
    ! [C_88] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(C_88,k2_relat_1(k7_relat_1(C_88,'#skF_1'))))) = k1_relat_1(k7_relat_1(C_88,k1_relat_1(k7_relat_1('#skF_2','#skF_1'))))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1(C_88,k1_relat_1(k7_relat_1('#skF_2','#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_2418])).

tff(c_2649,plain,(
    ! [C_91] :
      ( k3_xboole_0('#skF_1',k10_relat_1(C_91,k2_relat_1(k7_relat_1(C_91,'#skF_1')))) = k1_relat_1(k7_relat_1(C_91,'#skF_1'))
      | ~ v1_relat_1(C_91)
      | ~ v1_relat_1(k7_relat_1(C_91,'#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_395,c_89,c_394,c_227,c_2503])).

tff(c_396,plain,(
    ! [A_50] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_50)) = k3_xboole_0(A_50,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_411,plain,(
    ! [A_50] :
      ( r1_tarski(k3_xboole_0(A_50,'#skF_1'),A_50)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_14])).

tff(c_421,plain,(
    ! [A_51] : r1_tarski(k3_xboole_0(A_51,'#skF_1'),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_411])).

tff(c_439,plain,(
    ! [A_27] : r1_tarski(k3_xboole_0('#skF_1',A_27),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_421])).

tff(c_2798,plain,(
    ! [C_94] :
      ( r1_tarski(k1_relat_1(k7_relat_1(C_94,'#skF_1')),k10_relat_1(C_94,k2_relat_1(k7_relat_1(C_94,'#skF_1'))))
      | ~ v1_relat_1(C_94)
      | ~ v1_relat_1(k7_relat_1(C_94,'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2649,c_439])).

tff(c_2820,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_2798])).

tff(c_2830,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_24,c_2820])).

tff(c_2836,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2830])).

tff(c_2839,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2836])).

tff(c_2841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_2839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.28/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.28  
% 5.28/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.29  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.28/2.29  
% 5.28/2.29  %Foreground sorts:
% 5.28/2.29  
% 5.28/2.29  
% 5.28/2.29  %Background operators:
% 5.28/2.29  
% 5.28/2.29  
% 5.28/2.29  %Foreground operators:
% 5.28/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/2.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.28/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.28/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.28/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.28/2.29  tff('#skF_2', type, '#skF_2': $i).
% 5.28/2.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.28/2.29  tff('#skF_1', type, '#skF_1': $i).
% 5.28/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/2.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.28/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.28/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.28/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.28/2.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.28/2.29  
% 5.64/2.30  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.64/2.30  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.64/2.30  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.64/2.30  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 5.64/2.30  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.64/2.30  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.64/2.30  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.64/2.30  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.64/2.30  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.64/2.30  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 5.64/2.30  tff(c_20, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.64/2.30  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.64/2.30  tff(c_10, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.64/2.30  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.64/2.30  tff(c_167, plain, (![B_36, A_37]: (k3_xboole_0(k1_relat_1(B_36), A_37)=k1_relat_1(k7_relat_1(B_36, A_37)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.64/2.30  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.30  tff(c_59, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.64/2.30  tff(c_83, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(B_28, A_27))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 5.64/2.30  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.64/2.30  tff(c_89, plain, (![B_28, A_27]: (k3_xboole_0(B_28, A_27)=k3_xboole_0(A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_83, c_6])).
% 5.64/2.30  tff(c_190, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k1_relat_1(B_39))=k1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_167, c_89])).
% 5.64/2.30  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.64/2.30  tff(c_74, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.64/2.30  tff(c_78, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_74])).
% 5.64/2.30  tff(c_206, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_190, c_78])).
% 5.64/2.30  tff(c_227, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_206])).
% 5.64/2.30  tff(c_173, plain, (![A_37, B_36]: (k3_xboole_0(A_37, k1_relat_1(B_36))=k1_relat_1(k7_relat_1(B_36, A_37)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_167, c_89])).
% 5.64/2.30  tff(c_234, plain, (![A_37]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_37))=k3_xboole_0(A_37, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_227, c_173])).
% 5.64/2.30  tff(c_386, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_234])).
% 5.64/2.30  tff(c_389, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_386])).
% 5.64/2.30  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_389])).
% 5.64/2.30  tff(c_395, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_234])).
% 5.64/2.30  tff(c_394, plain, (![A_37]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_37))=k3_xboole_0(A_37, '#skF_1'))), inference(splitRight, [status(thm)], [c_234])).
% 5.64/2.30  tff(c_12, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.64/2.30  tff(c_16, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.64/2.30  tff(c_255, plain, (![A_40, C_41, B_42]: (k3_xboole_0(A_40, k10_relat_1(C_41, B_42))=k10_relat_1(k7_relat_1(C_41, A_40), B_42) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.64/2.30  tff(c_481, plain, (![C_53, B_54, B_55]: (k10_relat_1(k7_relat_1(C_53, k1_relat_1(B_54)), B_55)=k1_relat_1(k7_relat_1(B_54, k10_relat_1(C_53, B_55))) | ~v1_relat_1(C_53) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_16, c_255])).
% 5.64/2.30  tff(c_2418, plain, (![B_87, C_88]: (k1_relat_1(k7_relat_1(B_87, k10_relat_1(C_88, k2_relat_1(k7_relat_1(C_88, k1_relat_1(B_87))))))=k1_relat_1(k7_relat_1(C_88, k1_relat_1(B_87))) | ~v1_relat_1(C_88) | ~v1_relat_1(B_87) | ~v1_relat_1(k7_relat_1(C_88, k1_relat_1(B_87))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_481])).
% 5.64/2.30  tff(c_2503, plain, (![C_88]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(C_88, k2_relat_1(k7_relat_1(C_88, '#skF_1')))))=k1_relat_1(k7_relat_1(C_88, k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(C_88) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(C_88, k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_227, c_2418])).
% 5.64/2.30  tff(c_2649, plain, (![C_91]: (k3_xboole_0('#skF_1', k10_relat_1(C_91, k2_relat_1(k7_relat_1(C_91, '#skF_1'))))=k1_relat_1(k7_relat_1(C_91, '#skF_1')) | ~v1_relat_1(C_91) | ~v1_relat_1(k7_relat_1(C_91, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_395, c_89, c_394, c_227, c_2503])).
% 5.64/2.30  tff(c_396, plain, (![A_50]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_50))=k3_xboole_0(A_50, '#skF_1'))), inference(splitRight, [status(thm)], [c_234])).
% 5.64/2.30  tff(c_14, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.64/2.30  tff(c_411, plain, (![A_50]: (r1_tarski(k3_xboole_0(A_50, '#skF_1'), A_50) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_396, c_14])).
% 5.64/2.30  tff(c_421, plain, (![A_51]: (r1_tarski(k3_xboole_0(A_51, '#skF_1'), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_411])).
% 5.64/2.30  tff(c_439, plain, (![A_27]: (r1_tarski(k3_xboole_0('#skF_1', A_27), A_27))), inference(superposition, [status(thm), theory('equality')], [c_89, c_421])).
% 5.64/2.30  tff(c_2798, plain, (![C_94]: (r1_tarski(k1_relat_1(k7_relat_1(C_94, '#skF_1')), k10_relat_1(C_94, k2_relat_1(k7_relat_1(C_94, '#skF_1')))) | ~v1_relat_1(C_94) | ~v1_relat_1(k7_relat_1(C_94, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2649, c_439])).
% 5.64/2.30  tff(c_2820, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_2798])).
% 5.64/2.30  tff(c_2830, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_24, c_2820])).
% 5.64/2.30  tff(c_2836, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_2830])).
% 5.64/2.30  tff(c_2839, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2836])).
% 5.64/2.30  tff(c_2841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_2839])).
% 5.64/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.30  
% 5.64/2.30  Inference rules
% 5.64/2.30  ----------------------
% 5.64/2.30  #Ref     : 0
% 5.64/2.30  #Sup     : 668
% 5.64/2.30  #Fact    : 0
% 5.64/2.30  #Define  : 0
% 5.64/2.30  #Split   : 1
% 5.64/2.30  #Chain   : 0
% 5.64/2.30  #Close   : 0
% 5.64/2.30  
% 5.64/2.30  Ordering : KBO
% 5.64/2.30  
% 5.64/2.30  Simplification rules
% 5.64/2.30  ----------------------
% 5.64/2.30  #Subsume      : 66
% 5.64/2.30  #Demod        : 660
% 5.64/2.30  #Tautology    : 294
% 5.64/2.30  #SimpNegUnit  : 1
% 5.64/2.30  #BackRed      : 1
% 5.64/2.30  
% 5.64/2.30  #Partial instantiations: 0
% 5.64/2.30  #Strategies tried      : 1
% 5.64/2.30  
% 5.64/2.30  Timing (in seconds)
% 5.64/2.30  ----------------------
% 5.64/2.30  Preprocessing        : 0.48
% 5.64/2.30  Parsing              : 0.25
% 5.64/2.30  CNF conversion       : 0.03
% 5.64/2.30  Main loop            : 1.02
% 5.64/2.30  Inferencing          : 0.34
% 5.64/2.30  Reduction            : 0.40
% 5.64/2.30  Demodulation         : 0.32
% 5.64/2.30  BG Simplification    : 0.05
% 5.64/2.30  Subsumption          : 0.17
% 5.64/2.31  Abstraction          : 0.06
% 5.64/2.31  MUC search           : 0.00
% 5.64/2.31  Cooper               : 0.00
% 5.64/2.31  Total                : 1.53
% 5.64/2.31  Index Insertion      : 0.00
% 5.64/2.31  Index Deletion       : 0.00
% 5.64/2.31  Index Matching       : 0.00
% 5.64/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
