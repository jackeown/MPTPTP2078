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
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 31.83s
% Output     : CNFRefutation 31.83s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  100 ( 147 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k8_relat_1(A_21,B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [A_51,B_52] :
      ( k7_relat_1(k8_relat_1(A_51,B_52),A_51) = k2_wellord1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(k2_wellord1(B_53,A_54))
      | ~ v1_relat_1(k8_relat_1(A_54,B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_14])).

tff(c_170,plain,(
    ! [B_22,A_21] :
      ( v1_relat_1(k2_wellord1(B_22,A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_24,plain,(
    ! [A_32,B_33] :
      ( k7_relat_1(k8_relat_1(A_32,B_33),A_32) = k2_wellord1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28] :
      ( k8_relat_1(k3_xboole_0(A_26,B_27),C_28) = k8_relat_1(A_26,k8_relat_1(B_27,C_28))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(B_45,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_12,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_45,A_44] : k3_xboole_0(B_45,A_44) = k3_xboole_0(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_12])).

tff(c_181,plain,(
    ! [A_61,B_62,C_63] :
      ( k8_relat_1(k3_xboole_0(A_61,B_62),C_63) = k8_relat_1(A_61,k8_relat_1(B_62,C_63))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_273,plain,(
    ! [A_76,B_77,C_78] :
      ( k8_relat_1(k3_xboole_0(A_76,B_77),C_78) = k8_relat_1(B_77,k8_relat_1(A_76,C_78))
      | ~ v1_relat_1(C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_181])).

tff(c_309,plain,(
    ! [B_27,A_26,C_28] :
      ( k8_relat_1(B_27,k8_relat_1(A_26,C_28)) = k8_relat_1(A_26,k8_relat_1(B_27,C_28))
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_273])).

tff(c_210,plain,(
    ! [A_67,C_68,B_69] :
      ( k8_relat_1(A_67,k7_relat_1(C_68,B_69)) = k7_relat_1(k8_relat_1(A_67,C_68),B_69)
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_695,plain,(
    ! [A_105,A_106,B_107] :
      ( k7_relat_1(k8_relat_1(A_105,k8_relat_1(A_106,B_107)),A_106) = k8_relat_1(A_105,k2_wellord1(B_107,A_106))
      | ~ v1_relat_1(k8_relat_1(A_106,B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_210])).

tff(c_15124,plain,(
    ! [B_466,A_467,C_468] :
      ( k7_relat_1(k8_relat_1(B_466,k8_relat_1(A_467,C_468)),B_466) = k8_relat_1(A_467,k2_wellord1(C_468,B_466))
      | ~ v1_relat_1(k8_relat_1(B_466,C_468))
      | ~ v1_relat_1(C_468)
      | ~ v1_relat_1(C_468)
      | ~ v1_relat_1(C_468) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_695])).

tff(c_53082,plain,(
    ! [A_786,C_787,A_788] :
      ( k8_relat_1(A_786,k2_wellord1(C_787,A_788)) = k2_wellord1(k8_relat_1(A_786,C_787),A_788)
      | ~ v1_relat_1(k8_relat_1(A_788,C_787))
      | ~ v1_relat_1(C_787)
      | ~ v1_relat_1(C_787)
      | ~ v1_relat_1(C_787)
      | ~ v1_relat_1(k8_relat_1(A_786,C_787)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_15124])).

tff(c_53247,plain,(
    ! [A_789,B_790,A_791] :
      ( k8_relat_1(A_789,k2_wellord1(B_790,A_791)) = k2_wellord1(k8_relat_1(A_789,B_790),A_791)
      | ~ v1_relat_1(k8_relat_1(A_789,B_790))
      | ~ v1_relat_1(B_790) ) ),
    inference(resolution,[status(thm)],[c_16,c_53082])).

tff(c_53412,plain,(
    ! [A_792,B_793,A_794] :
      ( k8_relat_1(A_792,k2_wellord1(B_793,A_794)) = k2_wellord1(k8_relat_1(A_792,B_793),A_794)
      | ~ v1_relat_1(B_793) ) ),
    inference(resolution,[status(thm)],[c_16,c_53247])).

tff(c_55171,plain,(
    ! [A_816,B_817,A_818] :
      ( k7_relat_1(k2_wellord1(k8_relat_1(A_816,B_817),A_818),A_816) = k2_wellord1(k2_wellord1(B_817,A_818),A_816)
      | ~ v1_relat_1(k2_wellord1(B_817,A_818))
      | ~ v1_relat_1(B_817) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53412,c_24])).

tff(c_190,plain,(
    ! [A_61,B_62,C_63] :
      ( v1_relat_1(k8_relat_1(A_61,k8_relat_1(B_62,C_63)))
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_16])).

tff(c_187,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_relat_1(k8_relat_1(A_61,k8_relat_1(B_62,C_63)),k3_xboole_0(A_61,B_62)) = k2_wellord1(C_63,k3_xboole_0(A_61,B_62))
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_24])).

tff(c_239,plain,(
    ! [C_70,A_71,B_72] :
      ( k7_relat_1(k7_relat_1(C_70,A_71),B_72) = k7_relat_1(C_70,k3_xboole_0(A_71,B_72))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_759,plain,(
    ! [A_108,B_109,B_110] :
      ( k7_relat_1(k8_relat_1(A_108,B_109),k3_xboole_0(A_108,B_110)) = k7_relat_1(k2_wellord1(B_109,A_108),B_110)
      | ~ v1_relat_1(k8_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_239])).

tff(c_8481,plain,(
    ! [B_358,C_359,A_360] :
      ( k7_relat_1(k2_wellord1(k8_relat_1(B_358,C_359),A_360),B_358) = k2_wellord1(C_359,k3_xboole_0(A_360,B_358))
      | ~ v1_relat_1(k8_relat_1(A_360,k8_relat_1(B_358,C_359)))
      | ~ v1_relat_1(k8_relat_1(B_358,C_359))
      | ~ v1_relat_1(C_359)
      | ~ v1_relat_1(C_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_759])).

tff(c_8568,plain,(
    ! [B_62,C_63,A_61] :
      ( k7_relat_1(k2_wellord1(k8_relat_1(B_62,C_63),A_61),B_62) = k2_wellord1(C_63,k3_xboole_0(A_61,B_62))
      | ~ v1_relat_1(k8_relat_1(B_62,C_63))
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_190,c_8481])).

tff(c_65139,plain,(
    ! [B_942,A_943,A_944] :
      ( k2_wellord1(k2_wellord1(B_942,A_943),A_944) = k2_wellord1(B_942,k3_xboole_0(A_943,A_944))
      | ~ v1_relat_1(k8_relat_1(A_944,B_942))
      | ~ v1_relat_1(B_942)
      | ~ v1_relat_1(k2_wellord1(B_942,A_943))
      | ~ v1_relat_1(B_942) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55171,c_8568])).

tff(c_65317,plain,(
    ! [B_945,A_946,A_947] :
      ( k2_wellord1(k2_wellord1(B_945,A_946),A_947) = k2_wellord1(B_945,k3_xboole_0(A_946,A_947))
      | ~ v1_relat_1(k2_wellord1(B_945,A_946))
      | ~ v1_relat_1(B_945) ) ),
    inference(resolution,[status(thm)],[c_16,c_65139])).

tff(c_66459,plain,(
    ! [B_953,A_954,A_955] :
      ( k2_wellord1(k2_wellord1(B_953,A_954),A_955) = k2_wellord1(B_953,k3_xboole_0(A_954,A_955))
      | ~ v1_relat_1(B_953) ) ),
    inference(resolution,[status(thm)],[c_170,c_65317])).

tff(c_26,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66646,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66459,c_26])).

tff(c_66688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.83/19.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.83/19.54  
% 31.83/19.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.83/19.55  %$ v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 31.83/19.55  
% 31.83/19.55  %Foreground sorts:
% 31.83/19.55  
% 31.83/19.55  
% 31.83/19.55  %Background operators:
% 31.83/19.55  
% 31.83/19.55  
% 31.83/19.55  %Foreground operators:
% 31.83/19.55  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 31.83/19.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.83/19.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 31.83/19.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 31.83/19.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 31.83/19.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 31.83/19.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 31.83/19.55  tff('#skF_2', type, '#skF_2': $i).
% 31.83/19.55  tff('#skF_3', type, '#skF_3': $i).
% 31.83/19.55  tff('#skF_1', type, '#skF_1': $i).
% 31.83/19.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 31.83/19.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.83/19.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 31.83/19.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.83/19.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.83/19.55  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 31.83/19.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 31.83/19.55  
% 31.83/19.56  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 31.83/19.56  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 31.83/19.56  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 31.83/19.56  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 31.83/19.56  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 31.83/19.56  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 31.83/19.56  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 31.83/19.56  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 31.83/19.56  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 31.83/19.56  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 31.83/19.56  tff(c_16, plain, (![A_21, B_22]: (v1_relat_1(k8_relat_1(A_21, B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.83/19.56  tff(c_154, plain, (![A_51, B_52]: (k7_relat_1(k8_relat_1(A_51, B_52), A_51)=k2_wellord1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.83/19.56  tff(c_14, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.83/19.56  tff(c_166, plain, (![B_53, A_54]: (v1_relat_1(k2_wellord1(B_53, A_54)) | ~v1_relat_1(k8_relat_1(A_54, B_53)) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_154, c_14])).
% 31.83/19.56  tff(c_170, plain, (![B_22, A_21]: (v1_relat_1(k2_wellord1(B_22, A_21)) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_16, c_166])).
% 31.83/19.56  tff(c_24, plain, (![A_32, B_33]: (k7_relat_1(k8_relat_1(A_32, B_33), A_32)=k2_wellord1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.83/19.56  tff(c_20, plain, (![A_26, B_27, C_28]: (k8_relat_1(k3_xboole_0(A_26, B_27), C_28)=k8_relat_1(A_26, k8_relat_1(B_27, C_28)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 31.83/19.56  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 31.83/19.56  tff(c_64, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.83/19.56  tff(c_88, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(B_45, A_44))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 31.83/19.56  tff(c_12, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.83/19.56  tff(c_94, plain, (![B_45, A_44]: (k3_xboole_0(B_45, A_44)=k3_xboole_0(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_88, c_12])).
% 31.83/19.56  tff(c_181, plain, (![A_61, B_62, C_63]: (k8_relat_1(k3_xboole_0(A_61, B_62), C_63)=k8_relat_1(A_61, k8_relat_1(B_62, C_63)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 31.83/19.56  tff(c_273, plain, (![A_76, B_77, C_78]: (k8_relat_1(k3_xboole_0(A_76, B_77), C_78)=k8_relat_1(B_77, k8_relat_1(A_76, C_78)) | ~v1_relat_1(C_78))), inference(superposition, [status(thm), theory('equality')], [c_94, c_181])).
% 31.83/19.56  tff(c_309, plain, (![B_27, A_26, C_28]: (k8_relat_1(B_27, k8_relat_1(A_26, C_28))=k8_relat_1(A_26, k8_relat_1(B_27, C_28)) | ~v1_relat_1(C_28) | ~v1_relat_1(C_28))), inference(superposition, [status(thm), theory('equality')], [c_20, c_273])).
% 31.83/19.56  tff(c_210, plain, (![A_67, C_68, B_69]: (k8_relat_1(A_67, k7_relat_1(C_68, B_69))=k7_relat_1(k8_relat_1(A_67, C_68), B_69) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.83/19.56  tff(c_695, plain, (![A_105, A_106, B_107]: (k7_relat_1(k8_relat_1(A_105, k8_relat_1(A_106, B_107)), A_106)=k8_relat_1(A_105, k2_wellord1(B_107, A_106)) | ~v1_relat_1(k8_relat_1(A_106, B_107)) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_24, c_210])).
% 31.83/19.56  tff(c_15124, plain, (![B_466, A_467, C_468]: (k7_relat_1(k8_relat_1(B_466, k8_relat_1(A_467, C_468)), B_466)=k8_relat_1(A_467, k2_wellord1(C_468, B_466)) | ~v1_relat_1(k8_relat_1(B_466, C_468)) | ~v1_relat_1(C_468) | ~v1_relat_1(C_468) | ~v1_relat_1(C_468))), inference(superposition, [status(thm), theory('equality')], [c_309, c_695])).
% 31.83/19.56  tff(c_53082, plain, (![A_786, C_787, A_788]: (k8_relat_1(A_786, k2_wellord1(C_787, A_788))=k2_wellord1(k8_relat_1(A_786, C_787), A_788) | ~v1_relat_1(k8_relat_1(A_788, C_787)) | ~v1_relat_1(C_787) | ~v1_relat_1(C_787) | ~v1_relat_1(C_787) | ~v1_relat_1(k8_relat_1(A_786, C_787)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_15124])).
% 31.83/19.56  tff(c_53247, plain, (![A_789, B_790, A_791]: (k8_relat_1(A_789, k2_wellord1(B_790, A_791))=k2_wellord1(k8_relat_1(A_789, B_790), A_791) | ~v1_relat_1(k8_relat_1(A_789, B_790)) | ~v1_relat_1(B_790))), inference(resolution, [status(thm)], [c_16, c_53082])).
% 31.83/19.56  tff(c_53412, plain, (![A_792, B_793, A_794]: (k8_relat_1(A_792, k2_wellord1(B_793, A_794))=k2_wellord1(k8_relat_1(A_792, B_793), A_794) | ~v1_relat_1(B_793))), inference(resolution, [status(thm)], [c_16, c_53247])).
% 31.83/19.56  tff(c_55171, plain, (![A_816, B_817, A_818]: (k7_relat_1(k2_wellord1(k8_relat_1(A_816, B_817), A_818), A_816)=k2_wellord1(k2_wellord1(B_817, A_818), A_816) | ~v1_relat_1(k2_wellord1(B_817, A_818)) | ~v1_relat_1(B_817))), inference(superposition, [status(thm), theory('equality')], [c_53412, c_24])).
% 31.83/19.56  tff(c_190, plain, (![A_61, B_62, C_63]: (v1_relat_1(k8_relat_1(A_61, k8_relat_1(B_62, C_63))) | ~v1_relat_1(C_63) | ~v1_relat_1(C_63))), inference(superposition, [status(thm), theory('equality')], [c_181, c_16])).
% 31.83/19.56  tff(c_187, plain, (![A_61, B_62, C_63]: (k7_relat_1(k8_relat_1(A_61, k8_relat_1(B_62, C_63)), k3_xboole_0(A_61, B_62))=k2_wellord1(C_63, k3_xboole_0(A_61, B_62)) | ~v1_relat_1(C_63) | ~v1_relat_1(C_63))), inference(superposition, [status(thm), theory('equality')], [c_181, c_24])).
% 31.83/19.56  tff(c_239, plain, (![C_70, A_71, B_72]: (k7_relat_1(k7_relat_1(C_70, A_71), B_72)=k7_relat_1(C_70, k3_xboole_0(A_71, B_72)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 31.83/19.56  tff(c_759, plain, (![A_108, B_109, B_110]: (k7_relat_1(k8_relat_1(A_108, B_109), k3_xboole_0(A_108, B_110))=k7_relat_1(k2_wellord1(B_109, A_108), B_110) | ~v1_relat_1(k8_relat_1(A_108, B_109)) | ~v1_relat_1(B_109))), inference(superposition, [status(thm), theory('equality')], [c_24, c_239])).
% 31.83/19.56  tff(c_8481, plain, (![B_358, C_359, A_360]: (k7_relat_1(k2_wellord1(k8_relat_1(B_358, C_359), A_360), B_358)=k2_wellord1(C_359, k3_xboole_0(A_360, B_358)) | ~v1_relat_1(k8_relat_1(A_360, k8_relat_1(B_358, C_359))) | ~v1_relat_1(k8_relat_1(B_358, C_359)) | ~v1_relat_1(C_359) | ~v1_relat_1(C_359))), inference(superposition, [status(thm), theory('equality')], [c_187, c_759])).
% 31.83/19.56  tff(c_8568, plain, (![B_62, C_63, A_61]: (k7_relat_1(k2_wellord1(k8_relat_1(B_62, C_63), A_61), B_62)=k2_wellord1(C_63, k3_xboole_0(A_61, B_62)) | ~v1_relat_1(k8_relat_1(B_62, C_63)) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_190, c_8481])).
% 31.83/19.56  tff(c_65139, plain, (![B_942, A_943, A_944]: (k2_wellord1(k2_wellord1(B_942, A_943), A_944)=k2_wellord1(B_942, k3_xboole_0(A_943, A_944)) | ~v1_relat_1(k8_relat_1(A_944, B_942)) | ~v1_relat_1(B_942) | ~v1_relat_1(k2_wellord1(B_942, A_943)) | ~v1_relat_1(B_942))), inference(superposition, [status(thm), theory('equality')], [c_55171, c_8568])).
% 31.83/19.56  tff(c_65317, plain, (![B_945, A_946, A_947]: (k2_wellord1(k2_wellord1(B_945, A_946), A_947)=k2_wellord1(B_945, k3_xboole_0(A_946, A_947)) | ~v1_relat_1(k2_wellord1(B_945, A_946)) | ~v1_relat_1(B_945))), inference(resolution, [status(thm)], [c_16, c_65139])).
% 31.83/19.56  tff(c_66459, plain, (![B_953, A_954, A_955]: (k2_wellord1(k2_wellord1(B_953, A_954), A_955)=k2_wellord1(B_953, k3_xboole_0(A_954, A_955)) | ~v1_relat_1(B_953))), inference(resolution, [status(thm)], [c_170, c_65317])).
% 31.83/19.56  tff(c_26, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 31.83/19.56  tff(c_66646, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66459, c_26])).
% 31.83/19.56  tff(c_66688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_66646])).
% 31.83/19.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.83/19.56  
% 31.83/19.56  Inference rules
% 31.83/19.56  ----------------------
% 31.83/19.56  #Ref     : 0
% 31.83/19.56  #Sup     : 19847
% 31.83/19.56  #Fact    : 0
% 31.83/19.56  #Define  : 0
% 31.83/19.56  #Split   : 0
% 31.83/19.56  #Chain   : 0
% 31.83/19.56  #Close   : 0
% 31.83/19.56  
% 31.83/19.56  Ordering : KBO
% 31.83/19.56  
% 31.83/19.56  Simplification rules
% 31.83/19.56  ----------------------
% 31.83/19.56  #Subsume      : 2257
% 31.83/19.56  #Demod        : 58
% 31.83/19.56  #Tautology    : 372
% 31.83/19.56  #SimpNegUnit  : 0
% 31.83/19.56  #BackRed      : 0
% 31.83/19.56  
% 31.83/19.56  #Partial instantiations: 0
% 31.83/19.56  #Strategies tried      : 1
% 31.83/19.56  
% 31.83/19.56  Timing (in seconds)
% 31.83/19.56  ----------------------
% 31.83/19.56  Preprocessing        : 0.30
% 31.83/19.56  Parsing              : 0.16
% 31.83/19.56  CNF conversion       : 0.02
% 31.83/19.56  Main loop            : 18.50
% 31.83/19.56  Inferencing          : 3.81
% 31.83/19.56  Reduction            : 3.37
% 31.83/19.56  Demodulation         : 2.71
% 31.83/19.56  BG Simplification    : 0.78
% 31.83/19.56  Subsumption          : 9.90
% 31.83/19.56  Abstraction          : 0.82
% 31.83/19.56  MUC search           : 0.00
% 31.83/19.56  Cooper               : 0.00
% 31.83/19.56  Total                : 18.84
% 31.83/19.56  Index Insertion      : 0.00
% 31.83/19.56  Index Deletion       : 0.00
% 31.83/19.56  Index Matching       : 0.00
% 31.83/19.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
