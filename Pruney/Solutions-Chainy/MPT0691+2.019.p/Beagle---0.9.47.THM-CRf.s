%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 374 expanded)
%              Number of leaves         :   25 ( 134 expanded)
%              Depth                    :   21
%              Number of atoms          :  113 ( 773 expanded)
%              Number of equality atoms :   30 ( 199 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,(
    ! [B_43,A_44] :
      ( k1_relat_1(k7_relat_1(B_43,A_44)) = A_44
      | ~ r1_tarski(A_44,k1_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_180])).

tff(c_190,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_186])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_16])).

tff(c_201,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_204,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_204])).

tff(c_210,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_12,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k10_relat_1(B_39,A_40),k10_relat_1(B_39,k2_relat_1(B_39)))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_226,plain,(
    ! [A_46] :
      ( r1_tarski(k1_relat_1(A_46),k10_relat_1(A_46,k2_relat_1(A_46)))
      | ~ v1_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_232,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_226])).

tff(c_240,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_210,c_232])).

tff(c_246,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_240])).

tff(c_250,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_190,c_246])).

tff(c_175,plain,(
    ! [A_12,A_40] :
      ( r1_tarski(k10_relat_1(A_12,A_40),k1_relat_1(A_12))
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_400,plain,(
    ! [A_53,A_54] :
      ( k1_relat_1(k7_relat_1(A_53,k10_relat_1(A_53,A_54))) = k10_relat_1(A_53,A_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_175,c_180])).

tff(c_999,plain,(
    ! [A_81] :
      ( k1_relat_1(k7_relat_1(A_81,k1_relat_1(A_81))) = k10_relat_1(A_81,k2_relat_1(A_81))
      | ~ v1_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_400])).

tff(c_209,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_1035,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_209])).

tff(c_1091,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_210,c_250,c_190,c_190,c_1035])).

tff(c_1148,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1091])).

tff(c_1180,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1148])).

tff(c_18,plain,(
    ! [A_17,C_19,B_18] :
      ( k3_xboole_0(A_17,k10_relat_1(C_19,B_18)) = k10_relat_1(k7_relat_1(C_19,A_17),B_18)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_251,plain,(
    ! [A_47,C_48,B_49] :
      ( k3_xboole_0(A_47,k10_relat_1(C_48,B_49)) = k10_relat_1(k7_relat_1(C_48,A_47),B_49)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(B_27,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_setfam_1(k2_tarski(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [B_27,A_26] : k3_xboole_0(B_27,A_26) = k3_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_266,plain,(
    ! [C_48,B_49,A_47] :
      ( k3_xboole_0(k10_relat_1(C_48,B_49),A_47) = k10_relat_1(k7_relat_1(C_48,A_47),B_49)
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_80])).

tff(c_1264,plain,(
    ! [A_47] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_47),k9_relat_1('#skF_2','#skF_1')) = k3_xboole_0('#skF_1',A_47)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_266])).

tff(c_1370,plain,(
    ! [A_86] : k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_86),k9_relat_1('#skF_2','#skF_1')) = k3_xboole_0('#skF_1',A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1264])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,A_13),k10_relat_1(B_14,k2_relat_1(B_14)))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_444,plain,(
    ! [A_55,A_56,C_57,B_58] :
      ( r1_tarski(A_55,A_56)
      | ~ r1_tarski(A_55,k10_relat_1(k7_relat_1(C_57,A_56),B_58))
      | ~ v1_relat_1(C_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_2])).

tff(c_470,plain,(
    ! [C_57,A_56,A_13] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_57,A_56),A_13),A_56)
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(k7_relat_1(C_57,A_56)) ) ),
    inference(resolution,[status(thm)],[c_14,c_444])).

tff(c_1380,plain,(
    ! [A_86] :
      ( r1_tarski(k3_xboole_0('#skF_1',A_86),A_86)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1370,c_470])).

tff(c_1415,plain,(
    ! [A_87] :
      ( r1_tarski(k3_xboole_0('#skF_1',A_87),A_87)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_87)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1380])).

tff(c_1420,plain,(
    ! [B_9] :
      ( r1_tarski(k3_xboole_0('#skF_1',B_9),B_9)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1415])).

tff(c_1429,plain,(
    ! [B_88] : r1_tarski(k3_xboole_0('#skF_1',B_88),B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1420])).

tff(c_2105,plain,(
    ! [C_113,B_114] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_113,'#skF_1'),B_114),k10_relat_1(C_113,B_114))
      | ~ v1_relat_1(C_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1429])).

tff(c_2119,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_2105])).

tff(c_2154,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2119])).

tff(c_2156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_2154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.63  
% 3.55/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.63  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.55/1.63  
% 3.55/1.63  %Foreground sorts:
% 3.55/1.63  
% 3.55/1.63  
% 3.55/1.63  %Background operators:
% 3.55/1.63  
% 3.55/1.63  
% 3.55/1.63  %Foreground operators:
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.55/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.55/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.55/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.63  
% 3.55/1.65  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.55/1.65  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.55/1.65  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.55/1.65  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.55/1.65  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.55/1.65  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 3.55/1.65  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.55/1.65  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.55/1.65  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.55/1.65  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.55/1.65  tff(c_20, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.55/1.65  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.55/1.65  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.55/1.65  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.65  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.55/1.65  tff(c_180, plain, (![B_43, A_44]: (k1_relat_1(k7_relat_1(B_43, A_44))=A_44 | ~r1_tarski(A_44, k1_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.65  tff(c_186, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_180])).
% 3.55/1.65  tff(c_190, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_186])).
% 3.55/1.65  tff(c_16, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.65  tff(c_194, plain, (![A_15]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_190, c_16])).
% 3.55/1.65  tff(c_201, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_194])).
% 3.55/1.65  tff(c_204, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_201])).
% 3.55/1.65  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_204])).
% 3.55/1.65  tff(c_210, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_194])).
% 3.55/1.65  tff(c_12, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.55/1.65  tff(c_166, plain, (![B_39, A_40]: (r1_tarski(k10_relat_1(B_39, A_40), k10_relat_1(B_39, k2_relat_1(B_39))) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.65  tff(c_226, plain, (![A_46]: (r1_tarski(k1_relat_1(A_46), k10_relat_1(A_46, k2_relat_1(A_46))) | ~v1_relat_1(A_46) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 3.55/1.65  tff(c_232, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_226])).
% 3.55/1.65  tff(c_240, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_210, c_232])).
% 3.55/1.65  tff(c_246, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_240])).
% 3.55/1.65  tff(c_250, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_190, c_246])).
% 3.55/1.65  tff(c_175, plain, (![A_12, A_40]: (r1_tarski(k10_relat_1(A_12, A_40), k1_relat_1(A_12)) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 3.55/1.65  tff(c_400, plain, (![A_53, A_54]: (k1_relat_1(k7_relat_1(A_53, k10_relat_1(A_53, A_54)))=k10_relat_1(A_53, A_54) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_175, c_180])).
% 3.55/1.65  tff(c_999, plain, (![A_81]: (k1_relat_1(k7_relat_1(A_81, k1_relat_1(A_81)))=k10_relat_1(A_81, k2_relat_1(A_81)) | ~v1_relat_1(A_81) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_12, c_400])).
% 3.55/1.65  tff(c_209, plain, (![A_15]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(splitRight, [status(thm)], [c_194])).
% 3.55/1.65  tff(c_1035, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_999, c_209])).
% 3.55/1.65  tff(c_1091, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_210, c_250, c_190, c_190, c_1035])).
% 3.55/1.65  tff(c_1148, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1091])).
% 3.55/1.65  tff(c_1180, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1148])).
% 3.55/1.65  tff(c_18, plain, (![A_17, C_19, B_18]: (k3_xboole_0(A_17, k10_relat_1(C_19, B_18))=k10_relat_1(k7_relat_1(C_19, A_17), B_18) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.65  tff(c_251, plain, (![A_47, C_48, B_49]: (k3_xboole_0(A_47, k10_relat_1(C_48, B_49))=k10_relat_1(k7_relat_1(C_48, A_47), B_49) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.65  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.65  tff(c_59, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.65  tff(c_74, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(B_27, A_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 3.55/1.65  tff(c_6, plain, (![A_6, B_7]: (k1_setfam_1(k2_tarski(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.65  tff(c_80, plain, (![B_27, A_26]: (k3_xboole_0(B_27, A_26)=k3_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 3.55/1.65  tff(c_266, plain, (![C_48, B_49, A_47]: (k3_xboole_0(k10_relat_1(C_48, B_49), A_47)=k10_relat_1(k7_relat_1(C_48, A_47), B_49) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_251, c_80])).
% 3.55/1.65  tff(c_1264, plain, (![A_47]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_47), k9_relat_1('#skF_2', '#skF_1'))=k3_xboole_0('#skF_1', A_47) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1180, c_266])).
% 3.55/1.65  tff(c_1370, plain, (![A_86]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_86), k9_relat_1('#skF_2', '#skF_1'))=k3_xboole_0('#skF_1', A_86))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1264])).
% 3.55/1.65  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, A_13), k10_relat_1(B_14, k2_relat_1(B_14))) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.65  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.65  tff(c_444, plain, (![A_55, A_56, C_57, B_58]: (r1_tarski(A_55, A_56) | ~r1_tarski(A_55, k10_relat_1(k7_relat_1(C_57, A_56), B_58)) | ~v1_relat_1(C_57))), inference(superposition, [status(thm), theory('equality')], [c_251, c_2])).
% 3.55/1.65  tff(c_470, plain, (![C_57, A_56, A_13]: (r1_tarski(k10_relat_1(k7_relat_1(C_57, A_56), A_13), A_56) | ~v1_relat_1(C_57) | ~v1_relat_1(k7_relat_1(C_57, A_56)))), inference(resolution, [status(thm)], [c_14, c_444])).
% 3.55/1.65  tff(c_1380, plain, (![A_86]: (r1_tarski(k3_xboole_0('#skF_1', A_86), A_86) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_86)))), inference(superposition, [status(thm), theory('equality')], [c_1370, c_470])).
% 3.55/1.65  tff(c_1415, plain, (![A_87]: (r1_tarski(k3_xboole_0('#skF_1', A_87), A_87) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1380])).
% 3.55/1.65  tff(c_1420, plain, (![B_9]: (r1_tarski(k3_xboole_0('#skF_1', B_9), B_9) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1415])).
% 3.55/1.65  tff(c_1429, plain, (![B_88]: (r1_tarski(k3_xboole_0('#skF_1', B_88), B_88))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1420])).
% 3.55/1.65  tff(c_2105, plain, (![C_113, B_114]: (r1_tarski(k10_relat_1(k7_relat_1(C_113, '#skF_1'), B_114), k10_relat_1(C_113, B_114)) | ~v1_relat_1(C_113))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1429])).
% 3.55/1.65  tff(c_2119, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1180, c_2105])).
% 3.55/1.65  tff(c_2154, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2119])).
% 3.55/1.65  tff(c_2156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_2154])).
% 3.55/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.65  
% 3.55/1.65  Inference rules
% 3.55/1.65  ----------------------
% 3.55/1.65  #Ref     : 0
% 3.55/1.65  #Sup     : 498
% 3.55/1.65  #Fact    : 0
% 3.55/1.65  #Define  : 0
% 3.55/1.65  #Split   : 2
% 3.55/1.65  #Chain   : 0
% 3.55/1.65  #Close   : 0
% 3.55/1.65  
% 3.55/1.65  Ordering : KBO
% 3.55/1.65  
% 3.55/1.65  Simplification rules
% 3.55/1.65  ----------------------
% 3.55/1.65  #Subsume      : 35
% 3.55/1.65  #Demod        : 370
% 3.55/1.65  #Tautology    : 193
% 3.55/1.65  #SimpNegUnit  : 1
% 3.55/1.65  #BackRed      : 2
% 3.55/1.65  
% 3.55/1.65  #Partial instantiations: 0
% 3.55/1.65  #Strategies tried      : 1
% 3.55/1.65  
% 3.55/1.65  Timing (in seconds)
% 3.55/1.65  ----------------------
% 3.91/1.65  Preprocessing        : 0.28
% 3.91/1.65  Parsing              : 0.15
% 3.91/1.65  CNF conversion       : 0.02
% 3.91/1.65  Main loop            : 0.59
% 3.91/1.65  Inferencing          : 0.20
% 3.91/1.65  Reduction            : 0.21
% 3.91/1.65  Demodulation         : 0.17
% 3.91/1.65  BG Simplification    : 0.03
% 3.91/1.65  Subsumption          : 0.11
% 3.91/1.65  Abstraction          : 0.03
% 3.91/1.65  MUC search           : 0.00
% 3.91/1.65  Cooper               : 0.00
% 3.91/1.65  Total                : 0.90
% 3.91/1.65  Index Insertion      : 0.00
% 3.91/1.65  Index Deletion       : 0.00
% 3.91/1.65  Index Matching       : 0.00
% 3.91/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
