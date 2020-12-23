%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:41 EST 2020

% Result     : Theorem 9.07s
% Output     : CNFRefutation 9.07s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 114 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 189 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_32,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_109,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_26,plain,(
    ! [A_22] :
      ( k10_relat_1(A_22,k2_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1477,plain,(
    ! [A_108,C_109,B_110] :
      ( k3_xboole_0(A_108,k10_relat_1(C_109,B_110)) = k10_relat_1(k7_relat_1(C_109,A_108),B_110)
      | ~ v1_relat_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5960,plain,(
    ! [A_177,A_178] :
      ( k10_relat_1(k7_relat_1(A_177,A_178),k2_relat_1(A_177)) = k3_xboole_0(A_178,k1_relat_1(A_177))
      | ~ v1_relat_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1477])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18787,plain,(
    ! [A_363,A_364] :
      ( r1_tarski(k3_xboole_0(A_363,k1_relat_1(A_364)),k1_relat_1(k7_relat_1(A_364,A_363)))
      | ~ v1_relat_1(k7_relat_1(A_364,A_363))
      | ~ v1_relat_1(A_364)
      | ~ v1_relat_1(A_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5960,c_24])).

tff(c_18842,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_18787])).

tff(c_18860,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_18842])).

tff(c_18863,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_18860])).

tff(c_18866,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_18863])).

tff(c_18870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18866])).

tff(c_18872,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_18860])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k10_relat_1(B_24,A_23),k10_relat_1(B_24,k2_relat_1(B_24)))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20563,plain,(
    ! [A_377,A_378] :
      ( r1_tarski(k3_xboole_0(A_377,k1_relat_1(A_378)),k10_relat_1(k7_relat_1(A_378,A_377),k2_relat_1(k7_relat_1(A_378,A_377))))
      | ~ v1_relat_1(k7_relat_1(A_378,A_377))
      | ~ v1_relat_1(A_378)
      | ~ v1_relat_1(A_378) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5960,c_28])).

tff(c_20630,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_20563])).

tff(c_20649,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_18872,c_20630])).

tff(c_30,plain,(
    ! [A_25,C_27,B_26] :
      ( k3_xboole_0(A_25,k10_relat_1(C_27,B_26)) = k10_relat_1(k7_relat_1(C_27,A_25),B_26)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_564,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2251,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(A_122,B_123) = A_122
      | ~ r1_tarski(A_122,k3_xboole_0(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_12,c_564])).

tff(c_2266,plain,(
    ! [A_25,C_27,B_26] :
      ( k3_xboole_0(A_25,k10_relat_1(C_27,B_26)) = A_25
      | ~ r1_tarski(A_25,k10_relat_1(k7_relat_1(C_27,A_25),B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2251])).

tff(c_20655,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20649,c_2266])).

tff(c_20678,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20655])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    ! [B_47,A_48] : k1_setfam_1(k2_tarski(B_47,A_48)) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_151])).

tff(c_18,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,A_50) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_18])).

tff(c_219,plain,(
    ! [B_49,A_50] : r1_tarski(k3_xboole_0(B_49,A_50),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_12])).

tff(c_20888,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20678,c_219])).

tff(c_20975,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_20888])).

tff(c_20981,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20975])).

tff(c_20983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:35:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.07/3.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.60  
% 9.07/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.60  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.07/3.60  
% 9.07/3.60  %Foreground sorts:
% 9.07/3.60  
% 9.07/3.60  
% 9.07/3.60  %Background operators:
% 9.07/3.60  
% 9.07/3.60  
% 9.07/3.60  %Foreground operators:
% 9.07/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.07/3.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.07/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.07/3.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.07/3.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.07/3.60  tff('#skF_2', type, '#skF_2': $i).
% 9.07/3.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.07/3.60  tff('#skF_1', type, '#skF_1': $i).
% 9.07/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.07/3.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.07/3.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.07/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.07/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.07/3.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.07/3.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.07/3.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.07/3.60  
% 9.07/3.62  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 9.07/3.62  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.07/3.62  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.07/3.62  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.07/3.62  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 9.07/3.62  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 9.07/3.62  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 9.07/3.62  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 9.07/3.62  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.07/3.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.07/3.62  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.07/3.62  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.07/3.62  tff(c_32, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.07/3.62  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.07/3.62  tff(c_22, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.07/3.62  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.07/3.62  tff(c_34, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.07/3.62  tff(c_109, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.07/3.62  tff(c_120, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_34, c_109])).
% 9.07/3.62  tff(c_26, plain, (![A_22]: (k10_relat_1(A_22, k2_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.07/3.62  tff(c_1477, plain, (![A_108, C_109, B_110]: (k3_xboole_0(A_108, k10_relat_1(C_109, B_110))=k10_relat_1(k7_relat_1(C_109, A_108), B_110) | ~v1_relat_1(C_109))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.07/3.62  tff(c_5960, plain, (![A_177, A_178]: (k10_relat_1(k7_relat_1(A_177, A_178), k2_relat_1(A_177))=k3_xboole_0(A_178, k1_relat_1(A_177)) | ~v1_relat_1(A_177) | ~v1_relat_1(A_177))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1477])).
% 9.07/3.62  tff(c_24, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, A_20), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.07/3.62  tff(c_18787, plain, (![A_363, A_364]: (r1_tarski(k3_xboole_0(A_363, k1_relat_1(A_364)), k1_relat_1(k7_relat_1(A_364, A_363))) | ~v1_relat_1(k7_relat_1(A_364, A_363)) | ~v1_relat_1(A_364) | ~v1_relat_1(A_364))), inference(superposition, [status(thm), theory('equality')], [c_5960, c_24])).
% 9.07/3.62  tff(c_18842, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_18787])).
% 9.07/3.62  tff(c_18860, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_18842])).
% 9.07/3.62  tff(c_18863, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_18860])).
% 9.07/3.62  tff(c_18866, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_18863])).
% 9.07/3.62  tff(c_18870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_18866])).
% 9.07/3.62  tff(c_18872, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_18860])).
% 9.07/3.62  tff(c_28, plain, (![B_24, A_23]: (r1_tarski(k10_relat_1(B_24, A_23), k10_relat_1(B_24, k2_relat_1(B_24))) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.07/3.62  tff(c_20563, plain, (![A_377, A_378]: (r1_tarski(k3_xboole_0(A_377, k1_relat_1(A_378)), k10_relat_1(k7_relat_1(A_378, A_377), k2_relat_1(k7_relat_1(A_378, A_377)))) | ~v1_relat_1(k7_relat_1(A_378, A_377)) | ~v1_relat_1(A_378) | ~v1_relat_1(A_378))), inference(superposition, [status(thm), theory('equality')], [c_5960, c_28])).
% 9.07/3.62  tff(c_20630, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_20563])).
% 9.07/3.62  tff(c_20649, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_18872, c_20630])).
% 9.07/3.62  tff(c_30, plain, (![A_25, C_27, B_26]: (k3_xboole_0(A_25, k10_relat_1(C_27, B_26))=k10_relat_1(k7_relat_1(C_27, A_25), B_26) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.07/3.62  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.07/3.62  tff(c_564, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.07/3.62  tff(c_2251, plain, (![A_122, B_123]: (k3_xboole_0(A_122, B_123)=A_122 | ~r1_tarski(A_122, k3_xboole_0(A_122, B_123)))), inference(resolution, [status(thm)], [c_12, c_564])).
% 9.07/3.62  tff(c_2266, plain, (![A_25, C_27, B_26]: (k3_xboole_0(A_25, k10_relat_1(C_27, B_26))=A_25 | ~r1_tarski(A_25, k10_relat_1(k7_relat_1(C_27, A_25), B_26)) | ~v1_relat_1(C_27))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2251])).
% 9.07/3.62  tff(c_20655, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20649, c_2266])).
% 9.07/3.62  tff(c_20678, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20655])).
% 9.07/3.62  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.07/3.62  tff(c_151, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.07/3.62  tff(c_175, plain, (![B_47, A_48]: (k1_setfam_1(k2_tarski(B_47, A_48))=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_16, c_151])).
% 9.07/3.62  tff(c_18, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.07/3.62  tff(c_198, plain, (![B_49, A_50]: (k3_xboole_0(B_49, A_50)=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_175, c_18])).
% 9.07/3.62  tff(c_219, plain, (![B_49, A_50]: (r1_tarski(k3_xboole_0(B_49, A_50), A_50))), inference(superposition, [status(thm), theory('equality')], [c_198, c_12])).
% 9.07/3.62  tff(c_20888, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_20678, c_219])).
% 9.07/3.62  tff(c_20975, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_20888])).
% 9.07/3.62  tff(c_20981, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_20975])).
% 9.07/3.62  tff(c_20983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_20981])).
% 9.07/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.62  
% 9.07/3.62  Inference rules
% 9.07/3.62  ----------------------
% 9.07/3.62  #Ref     : 0
% 9.07/3.62  #Sup     : 5219
% 9.07/3.62  #Fact    : 0
% 9.07/3.62  #Define  : 0
% 9.07/3.62  #Split   : 2
% 9.07/3.62  #Chain   : 0
% 9.07/3.62  #Close   : 0
% 9.07/3.62  
% 9.07/3.62  Ordering : KBO
% 9.07/3.62  
% 9.07/3.62  Simplification rules
% 9.07/3.62  ----------------------
% 9.07/3.62  #Subsume      : 343
% 9.07/3.62  #Demod        : 4328
% 9.07/3.62  #Tautology    : 3263
% 9.07/3.62  #SimpNegUnit  : 1
% 9.07/3.62  #BackRed      : 0
% 9.07/3.62  
% 9.07/3.62  #Partial instantiations: 0
% 9.07/3.62  #Strategies tried      : 1
% 9.07/3.62  
% 9.07/3.62  Timing (in seconds)
% 9.07/3.62  ----------------------
% 9.07/3.62  Preprocessing        : 0.30
% 9.07/3.62  Parsing              : 0.16
% 9.07/3.62  CNF conversion       : 0.02
% 9.07/3.62  Main loop            : 2.57
% 9.07/3.62  Inferencing          : 0.54
% 9.07/3.62  Reduction            : 1.35
% 9.07/3.62  Demodulation         : 1.17
% 9.07/3.62  BG Simplification    : 0.07
% 9.07/3.62  Subsumption          : 0.46
% 9.26/3.62  Abstraction          : 0.10
% 9.26/3.62  MUC search           : 0.00
% 9.26/3.62  Cooper               : 0.00
% 9.26/3.62  Total                : 2.89
% 9.26/3.62  Index Insertion      : 0.00
% 9.26/3.62  Index Deletion       : 0.00
% 9.26/3.62  Index Matching       : 0.00
% 9.26/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
