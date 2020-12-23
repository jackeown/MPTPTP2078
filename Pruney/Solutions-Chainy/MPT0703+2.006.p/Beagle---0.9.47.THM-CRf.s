%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:09 EST 2020

% Result     : Theorem 19.31s
% Output     : CNFRefutation 19.42s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 178 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 375 expanded)
%              Number of equality atoms :   27 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_89,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_20,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1616,plain,(
    ! [C_95,A_96,B_97] :
      ( r1_tarski(k9_relat_1(C_95,A_96),k9_relat_1(C_95,B_97))
      | ~ r1_tarski(A_96,B_97)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8654,plain,(
    ! [A_203,B_204] :
      ( r1_tarski(k2_relat_1(A_203),k9_relat_1(A_203,B_204))
      | ~ r1_tarski(k1_relat_1(A_203),B_204)
      | ~ v1_relat_1(A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1616])).

tff(c_169,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    ! [C_39] :
      ( r1_tarski('#skF_1',C_39)
      | ~ r1_tarski(k2_relat_1('#skF_3'),C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_169])).

tff(c_8669,plain,(
    ! [B_204] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_204))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_204)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8654,c_172])).

tff(c_8821,plain,(
    ! [B_207] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_207))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8669])).

tff(c_8906,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_8,c_8821])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8924,plain,(
    k2_xboole_0('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8906,c_12])).

tff(c_60656,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_xboole_0('#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8924])).

tff(c_60757,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_60656])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,k9_relat_1(B_24,k1_relat_1(B_24))) = k9_relat_1(B_24,k10_relat_1(B_24,A_23))
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_60811,plain,(
    ! [A_23] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_23)) = k3_xboole_0(A_23,k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60757,c_26])).

tff(c_60857,plain,(
    ! [A_23] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_23)) = k3_xboole_0(A_23,k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_60811])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_689,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(k2_xboole_0(A_65,C_66),k2_xboole_0(B_67,C_66))
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_824,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k2_xboole_0(B_73,C_74))
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_689,c_10])).

tff(c_847,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,k10_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_72,k10_relat_1('#skF_3','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_824])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8923,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8906,c_14])).

tff(c_8930,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8923,c_26])).

tff(c_8940,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_8930])).

tff(c_22,plain,(
    ! [C_20,A_18,B_19] :
      ( r1_tarski(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19))
      | ~ r1_tarski(A_18,B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8958,plain,(
    ! [B_19] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_19))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_19)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8940,c_22])).

tff(c_75008,plain,(
    ! [B_661] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_661))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_661) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8958])).

tff(c_75098,plain,
    ( r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_847,c_75008])).

tff(c_75179,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_60857,c_75098])).

tff(c_60973,plain,(
    ! [A_587] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_587)) = k3_xboole_0(A_587,k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_60811])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1060,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k9_relat_1(B_80,k10_relat_1(B_80,A_81)),A_81)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1068,plain,(
    ! [B_80,A_81] :
      ( k2_xboole_0(k9_relat_1(B_80,k10_relat_1(B_80,A_81)),A_81) = A_81
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_1060,c_12])).

tff(c_1072,plain,(
    ! [A_81,B_80] :
      ( k2_xboole_0(A_81,k9_relat_1(B_80,k10_relat_1(B_80,A_81))) = A_81
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1068])).

tff(c_61038,plain,(
    ! [A_587] :
      ( k2_xboole_0(A_587,k3_xboole_0(A_587,k2_relat_1('#skF_3'))) = A_587
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60973,c_1072])).

tff(c_61264,plain,(
    ! [A_591] : k2_xboole_0(A_591,k3_xboole_0(A_591,k2_relat_1('#skF_3'))) = A_591 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_61038])).

tff(c_859,plain,(
    ! [A_72,A_1,B_2] :
      ( r1_tarski(A_72,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_72,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_824])).

tff(c_62002,plain,(
    ! [A_72,A_591] :
      ( r1_tarski(A_72,A_591)
      | ~ r1_tarski(A_72,k3_xboole_0(A_591,k2_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61264,c_859])).

tff(c_75197,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_75179,c_62002])).

tff(c_75221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_75197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.31/12.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.31/12.13  
% 19.31/12.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.42/12.13  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 19.42/12.13  
% 19.42/12.13  %Foreground sorts:
% 19.42/12.13  
% 19.42/12.13  
% 19.42/12.13  %Background operators:
% 19.42/12.13  
% 19.42/12.13  
% 19.42/12.13  %Foreground operators:
% 19.42/12.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.42/12.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.42/12.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.42/12.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.42/12.13  tff('#skF_2', type, '#skF_2': $i).
% 19.42/12.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.42/12.13  tff('#skF_3', type, '#skF_3': $i).
% 19.42/12.13  tff('#skF_1', type, '#skF_1': $i).
% 19.42/12.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.42/12.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.42/12.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.42/12.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.42/12.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.42/12.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.42/12.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.42/12.13  
% 19.42/12.15  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 19.42/12.15  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.42/12.15  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 19.42/12.15  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 19.42/12.15  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 19.42/12.15  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 19.42/12.15  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 19.42/12.15  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 19.42/12.15  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 19.42/12.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.42/12.15  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 19.42/12.15  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.42/12.15  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.42/12.15  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.42/12.15  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.42/12.15  tff(c_30, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.42/12.15  tff(c_89, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.42/12.15  tff(c_108, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_89])).
% 19.42/12.15  tff(c_20, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.42/12.15  tff(c_1616, plain, (![C_95, A_96, B_97]: (r1_tarski(k9_relat_1(C_95, A_96), k9_relat_1(C_95, B_97)) | ~r1_tarski(A_96, B_97) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.42/12.15  tff(c_8654, plain, (![A_203, B_204]: (r1_tarski(k2_relat_1(A_203), k9_relat_1(A_203, B_204)) | ~r1_tarski(k1_relat_1(A_203), B_204) | ~v1_relat_1(A_203) | ~v1_relat_1(A_203))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1616])).
% 19.42/12.15  tff(c_169, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(k2_xboole_0(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.42/12.15  tff(c_172, plain, (![C_39]: (r1_tarski('#skF_1', C_39) | ~r1_tarski(k2_relat_1('#skF_3'), C_39))), inference(superposition, [status(thm), theory('equality')], [c_108, c_169])).
% 19.42/12.15  tff(c_8669, plain, (![B_204]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_204)) | ~r1_tarski(k1_relat_1('#skF_3'), B_204) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8654, c_172])).
% 19.42/12.15  tff(c_8821, plain, (![B_207]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_207)) | ~r1_tarski(k1_relat_1('#skF_3'), B_207))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8669])).
% 19.42/12.15  tff(c_8906, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_8821])).
% 19.42/12.15  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.42/12.15  tff(c_8924, plain, (k2_xboole_0('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8906, c_12])).
% 19.42/12.15  tff(c_60656, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_xboole_0('#skF_1', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_8924])).
% 19.42/12.15  tff(c_60757, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108, c_60656])).
% 19.42/12.15  tff(c_26, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k9_relat_1(B_24, k1_relat_1(B_24)))=k9_relat_1(B_24, k10_relat_1(B_24, A_23)) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.42/12.15  tff(c_60811, plain, (![A_23]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_23))=k3_xboole_0(A_23, k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60757, c_26])).
% 19.42/12.15  tff(c_60857, plain, (![A_23]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_23))=k3_xboole_0(A_23, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_60811])).
% 19.42/12.15  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.42/12.15  tff(c_105, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_89])).
% 19.42/12.15  tff(c_689, plain, (![A_65, C_66, B_67]: (r1_tarski(k2_xboole_0(A_65, C_66), k2_xboole_0(B_67, C_66)) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.42/12.15  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.42/12.15  tff(c_824, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k2_xboole_0(B_73, C_74)) | ~r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_689, c_10])).
% 19.42/12.15  tff(c_847, plain, (![A_72]: (r1_tarski(A_72, k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_72, k10_relat_1('#skF_3', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_105, c_824])).
% 19.42/12.15  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.42/12.15  tff(c_8923, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))='#skF_1'), inference(resolution, [status(thm)], [c_8906, c_14])).
% 19.42/12.15  tff(c_8930, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8923, c_26])).
% 19.42/12.15  tff(c_8940, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_8930])).
% 19.42/12.15  tff(c_22, plain, (![C_20, A_18, B_19]: (r1_tarski(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19)) | ~r1_tarski(A_18, B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.42/12.15  tff(c_8958, plain, (![B_19]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_19)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_19) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8940, c_22])).
% 19.42/12.15  tff(c_75008, plain, (![B_661]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_661)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_661))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8958])).
% 19.42/12.15  tff(c_75098, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_847, c_75008])).
% 19.42/12.15  tff(c_75179, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_60857, c_75098])).
% 19.42/12.15  tff(c_60973, plain, (![A_587]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_587))=k3_xboole_0(A_587, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_60811])).
% 19.42/12.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.42/12.15  tff(c_1060, plain, (![B_80, A_81]: (r1_tarski(k9_relat_1(B_80, k10_relat_1(B_80, A_81)), A_81) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 19.42/12.15  tff(c_1068, plain, (![B_80, A_81]: (k2_xboole_0(k9_relat_1(B_80, k10_relat_1(B_80, A_81)), A_81)=A_81 | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_1060, c_12])).
% 19.42/12.15  tff(c_1072, plain, (![A_81, B_80]: (k2_xboole_0(A_81, k9_relat_1(B_80, k10_relat_1(B_80, A_81)))=A_81 | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1068])).
% 19.42/12.15  tff(c_61038, plain, (![A_587]: (k2_xboole_0(A_587, k3_xboole_0(A_587, k2_relat_1('#skF_3')))=A_587 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_60973, c_1072])).
% 19.42/12.15  tff(c_61264, plain, (![A_591]: (k2_xboole_0(A_591, k3_xboole_0(A_591, k2_relat_1('#skF_3')))=A_591)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_61038])).
% 19.42/12.15  tff(c_859, plain, (![A_72, A_1, B_2]: (r1_tarski(A_72, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_72, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_824])).
% 19.42/12.15  tff(c_62002, plain, (![A_72, A_591]: (r1_tarski(A_72, A_591) | ~r1_tarski(A_72, k3_xboole_0(A_591, k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_61264, c_859])).
% 19.42/12.15  tff(c_75197, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_75179, c_62002])).
% 19.42/12.15  tff(c_75221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_75197])).
% 19.42/12.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.42/12.15  
% 19.42/12.15  Inference rules
% 19.42/12.15  ----------------------
% 19.42/12.15  #Ref     : 0
% 19.42/12.15  #Sup     : 18600
% 19.42/12.15  #Fact    : 0
% 19.42/12.15  #Define  : 0
% 19.42/12.15  #Split   : 4
% 19.42/12.15  #Chain   : 0
% 19.42/12.15  #Close   : 0
% 19.42/12.15  
% 19.42/12.15  Ordering : KBO
% 19.42/12.15  
% 19.42/12.15  Simplification rules
% 19.42/12.15  ----------------------
% 19.42/12.15  #Subsume      : 3600
% 19.42/12.15  #Demod        : 13261
% 19.42/12.15  #Tautology    : 7741
% 19.42/12.15  #SimpNegUnit  : 9
% 19.42/12.15  #BackRed      : 3
% 19.42/12.15  
% 19.42/12.15  #Partial instantiations: 0
% 19.42/12.15  #Strategies tried      : 1
% 19.42/12.15  
% 19.42/12.15  Timing (in seconds)
% 19.42/12.15  ----------------------
% 19.42/12.15  Preprocessing        : 0.28
% 19.42/12.15  Parsing              : 0.16
% 19.42/12.15  CNF conversion       : 0.02
% 19.42/12.15  Main loop            : 11.09
% 19.42/12.15  Inferencing          : 1.45
% 19.42/12.15  Reduction            : 5.82
% 19.42/12.15  Demodulation         : 5.25
% 19.42/12.15  BG Simplification    : 0.19
% 19.42/12.15  Subsumption          : 3.16
% 19.42/12.15  Abstraction          : 0.31
% 19.42/12.15  MUC search           : 0.00
% 19.42/12.15  Cooper               : 0.00
% 19.42/12.15  Total                : 11.40
% 19.42/12.15  Index Insertion      : 0.00
% 19.42/12.15  Index Deletion       : 0.00
% 19.42/12.15  Index Matching       : 0.00
% 19.42/12.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
