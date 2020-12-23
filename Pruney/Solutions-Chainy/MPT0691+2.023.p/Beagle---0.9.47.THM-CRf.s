%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 36.41s
% Output     : CNFRefutation 36.49s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 947 expanded)
%              Number of leaves         :   28 ( 341 expanded)
%              Depth                    :   22
%              Number of atoms          :  157 (1936 expanded)
%              Number of equality atoms :   47 ( 483 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k7_relat_1(A_22,B_23))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_167,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_182,plain,(
    k3_xboole_0('#skF_2',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_167])).

tff(c_32,plain,(
    ! [A_28] :
      ( k10_relat_1(A_28,k2_relat_1(A_28)) = k1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2210,plain,(
    ! [A_125,C_126,B_127] :
      ( k3_xboole_0(A_125,k10_relat_1(C_126,B_127)) = k10_relat_1(k7_relat_1(C_126,A_125),B_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9263,plain,(
    ! [A_224,A_225] :
      ( k10_relat_1(k7_relat_1(A_224,A_225),k2_relat_1(A_224)) = k3_xboole_0(A_225,k1_relat_1(A_224))
      | ~ v1_relat_1(A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2210])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k10_relat_1(B_27,A_26),k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28151,plain,(
    ! [A_442,A_443] :
      ( r1_tarski(k3_xboole_0(A_442,k1_relat_1(A_443)),k1_relat_1(k7_relat_1(A_443,A_442)))
      | ~ v1_relat_1(k7_relat_1(A_443,A_442))
      | ~ v1_relat_1(A_443)
      | ~ v1_relat_1(A_443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9263,c_30])).

tff(c_28220,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_28151])).

tff(c_28251,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_28220])).

tff(c_28264,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28251])).

tff(c_28267,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_28264])).

tff(c_28271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28267])).

tff(c_28273,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28251])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5294,plain,(
    ! [C_177,B_178,A_179] :
      ( k3_xboole_0(k10_relat_1(C_177,B_178),A_179) = k10_relat_1(k7_relat_1(C_177,A_179),B_178)
      | ~ v1_relat_1(C_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_2])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),A_15) = A_15 ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_20032,plain,(
    ! [C_363,A_364,B_365] :
      ( k2_xboole_0(k10_relat_1(k7_relat_1(C_363,A_364),B_365),k10_relat_1(C_363,B_365)) = k10_relat_1(C_363,B_365)
      | ~ v1_relat_1(C_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5294,c_108])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_261,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(k2_xboole_0(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_292,plain,(
    ! [A_61,B_62] : r1_tarski(A_61,k2_xboole_0(A_61,B_62)) ),
    inference(resolution,[status(thm)],[c_14,c_261])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_319,plain,(
    ! [A_61,B_62] : k3_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = A_61 ),
    inference(resolution,[status(thm)],[c_292,c_22])).

tff(c_20114,plain,(
    ! [C_363,A_364,B_365] :
      ( k3_xboole_0(k10_relat_1(k7_relat_1(C_363,A_364),B_365),k10_relat_1(C_363,B_365)) = k10_relat_1(k7_relat_1(C_363,A_364),B_365)
      | ~ v1_relat_1(C_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20032,c_319])).

tff(c_128179,plain,(
    ! [C_1120,B_1121,A_1122] :
      ( k3_xboole_0(k10_relat_1(C_1120,B_1121),k10_relat_1(k7_relat_1(C_1120,A_1122),B_1121)) = k10_relat_1(k7_relat_1(C_1120,A_1122),B_1121)
      | ~ v1_relat_1(C_1120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20114])).

tff(c_2988,plain,(
    ! [C_133,A_134,B_135] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_133,A_134),B_135),A_134)
      | ~ v1_relat_1(C_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_20])).

tff(c_3000,plain,(
    ! [C_133,A_134] :
      ( r1_tarski(k1_relat_1(k7_relat_1(C_133,A_134)),A_134)
      | ~ v1_relat_1(C_133)
      | ~ v1_relat_1(k7_relat_1(C_133,A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2988])).

tff(c_28272,plain,(
    r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_28251])).

tff(c_28293,plain,(
    k3_xboole_0('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28272,c_22])).

tff(c_248,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k10_relat_1(B_55,A_56),k1_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_253,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k10_relat_1(B_55,A_56),k1_relat_1(B_55)) = k10_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_248,c_22])).

tff(c_259,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),k10_relat_1(B_55,A_56)) = k10_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_45156,plain,(
    ! [A_580,A_581] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(A_580,A_581)),k3_xboole_0(A_581,k1_relat_1(A_580))) = k10_relat_1(k7_relat_1(A_580,A_581),k2_relat_1(A_580))
      | ~ v1_relat_1(k7_relat_1(A_580,A_581))
      | ~ v1_relat_1(A_580)
      | ~ v1_relat_1(A_580) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9263,c_259])).

tff(c_45512,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),'#skF_2') = k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_45156])).

tff(c_45578,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_28273,c_28293,c_2,c_45512])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_257,plain,(
    ! [B_55,A_56] :
      ( k10_relat_1(B_55,A_56) = k1_relat_1(B_55)
      | ~ r1_tarski(k1_relat_1(B_55),k10_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_248,c_10])).

tff(c_51451,plain,(
    ! [A_633,A_634] :
      ( k10_relat_1(k7_relat_1(A_633,A_634),k2_relat_1(A_633)) = k1_relat_1(k7_relat_1(A_633,A_634))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_633,A_634)),k3_xboole_0(A_634,k1_relat_1(A_633)))
      | ~ v1_relat_1(k7_relat_1(A_633,A_634))
      | ~ v1_relat_1(A_633)
      | ~ v1_relat_1(A_633) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9263,c_257])).

tff(c_51518,plain,
    ( k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k2_relat_1('#skF_3')) = k1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_51451])).

tff(c_51548,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_28273,c_45578,c_51518])).

tff(c_51549,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_51548])).

tff(c_51552,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3000,c_51549])).

tff(c_51556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28273,c_40,c_51552])).

tff(c_51557,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_51548])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_260,plain,(
    ! [B_55,A_56] :
      ( k2_xboole_0(k10_relat_1(B_55,A_56),k1_relat_1(B_55)) = k1_relat_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_248,c_18])).

tff(c_51637,plain,(
    ! [A_56] :
      ( k2_xboole_0(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_56),'#skF_2') = k1_relat_1(k7_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51557,c_260])).

tff(c_51678,plain,(
    ! [A_56] : k2_xboole_0(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_56),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28273,c_51557,c_51637])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(k2_xboole_0(A_10,B_11),C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_392,plain,(
    ! [A_67,B_68,B_69] : r1_tarski(A_67,k2_xboole_0(k2_xboole_0(A_67,B_68),B_69)) ),
    inference(resolution,[status(thm)],[c_292,c_16])).

tff(c_544,plain,(
    ! [A_77,B_78,B_79] : r1_tarski(k3_xboole_0(A_77,B_78),k2_xboole_0(A_77,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_392])).

tff(c_56169,plain,(
    ! [A_671,B_672,B_673] : k2_xboole_0(k3_xboole_0(A_671,B_672),k2_xboole_0(A_671,B_673)) = k2_xboole_0(A_671,B_673) ),
    inference(resolution,[status(thm)],[c_544,c_18])).

tff(c_56370,plain,(
    ! [A_56,B_672] : k2_xboole_0(k3_xboole_0(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_56),B_672),'#skF_2') = k2_xboole_0(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_56),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_51678,c_56169])).

tff(c_56724,plain,(
    ! [A_56,B_672] : k2_xboole_0(k3_xboole_0(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_56),B_672),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51678,c_56370])).

tff(c_128257,plain,(
    ! [A_1122,B_1121] :
      ( k2_xboole_0(k10_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_1122),B_1121),'#skF_2') = '#skF_2'
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128179,c_56724])).

tff(c_128816,plain,(
    ! [A_1122,B_1121] : k2_xboole_0(k10_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_1122),B_1121),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28273,c_128257])).

tff(c_145980,plain,(
    ! [A_1226,A_1227] :
      ( k2_xboole_0(k10_relat_1(k7_relat_1(A_1226,A_1227),k2_relat_1(A_1226)),k1_relat_1(A_1226)) = k10_relat_1(A_1226,k2_relat_1(A_1226))
      | ~ v1_relat_1(A_1226)
      | ~ v1_relat_1(A_1226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_20032])).

tff(c_146275,plain,(
    ! [A_1227] :
      ( k2_xboole_0(k10_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_1227),k2_relat_1(k7_relat_1('#skF_3','#skF_2'))),'#skF_2') = k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k2_relat_1(k7_relat_1('#skF_3','#skF_2')))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51557,c_145980])).

tff(c_146346,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k2_relat_1(k7_relat_1('#skF_3','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28273,c_28273,c_128816,c_146275])).

tff(c_45,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_20])).

tff(c_2295,plain,(
    ! [C_126,A_125,B_127] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_126,A_125),B_127),k10_relat_1(C_126,B_127))
      | ~ v1_relat_1(C_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2210,c_60])).

tff(c_146537,plain,
    ( r1_tarski('#skF_2',k10_relat_1('#skF_3',k2_relat_1(k7_relat_1('#skF_3','#skF_2'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_146346,c_2295])).

tff(c_146695,plain,(
    r1_tarski('#skF_2',k10_relat_1('#skF_3',k2_relat_1(k7_relat_1('#skF_3','#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_146537])).

tff(c_146764,plain,
    ( r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_146695])).

tff(c_146788,plain,(
    r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_146764])).

tff(c_146790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_146788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.41/26.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.49/27.00  
% 36.49/27.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.49/27.00  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 36.49/27.00  
% 36.49/27.00  %Foreground sorts:
% 36.49/27.00  
% 36.49/27.00  
% 36.49/27.00  %Background operators:
% 36.49/27.00  
% 36.49/27.00  
% 36.49/27.00  %Foreground operators:
% 36.49/27.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.49/27.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.49/27.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 36.49/27.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.49/27.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.49/27.00  tff('#skF_2', type, '#skF_2': $i).
% 36.49/27.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.49/27.00  tff('#skF_3', type, '#skF_3': $i).
% 36.49/27.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.49/27.00  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 36.49/27.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.49/27.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.49/27.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.49/27.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.49/27.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.49/27.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.49/27.00  
% 36.49/27.02  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 36.49/27.02  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 36.49/27.02  tff(f_64, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 36.49/27.02  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.49/27.02  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 36.49/27.02  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 36.49/27.02  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 36.49/27.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.49/27.02  tff(f_50, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 36.49/27.02  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 36.49/27.02  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.49/27.02  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 36.49/27.02  tff(c_36, plain, (~r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 36.49/27.02  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 36.49/27.02  tff(c_28, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 36.49/27.02  tff(c_26, plain, (![A_22, B_23]: (v1_relat_1(k7_relat_1(A_22, B_23)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.49/27.02  tff(c_38, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 36.49/27.02  tff(c_167, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.49/27.02  tff(c_182, plain, (k3_xboole_0('#skF_2', k1_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_38, c_167])).
% 36.49/27.02  tff(c_32, plain, (![A_28]: (k10_relat_1(A_28, k2_relat_1(A_28))=k1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 36.49/27.02  tff(c_2210, plain, (![A_125, C_126, B_127]: (k3_xboole_0(A_125, k10_relat_1(C_126, B_127))=k10_relat_1(k7_relat_1(C_126, A_125), B_127) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_80])).
% 36.49/27.02  tff(c_9263, plain, (![A_224, A_225]: (k10_relat_1(k7_relat_1(A_224, A_225), k2_relat_1(A_224))=k3_xboole_0(A_225, k1_relat_1(A_224)) | ~v1_relat_1(A_224) | ~v1_relat_1(A_224))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2210])).
% 36.49/27.02  tff(c_30, plain, (![B_27, A_26]: (r1_tarski(k10_relat_1(B_27, A_26), k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.49/27.02  tff(c_28151, plain, (![A_442, A_443]: (r1_tarski(k3_xboole_0(A_442, k1_relat_1(A_443)), k1_relat_1(k7_relat_1(A_443, A_442))) | ~v1_relat_1(k7_relat_1(A_443, A_442)) | ~v1_relat_1(A_443) | ~v1_relat_1(A_443))), inference(superposition, [status(thm), theory('equality')], [c_9263, c_30])).
% 36.49/27.02  tff(c_28220, plain, (r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_28151])).
% 36.49/27.02  tff(c_28251, plain, (r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_28220])).
% 36.49/27.02  tff(c_28264, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_28251])).
% 36.49/27.02  tff(c_28267, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_28264])).
% 36.49/27.02  tff(c_28271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_28267])).
% 36.49/27.02  tff(c_28273, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_28251])).
% 36.49/27.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.49/27.02  tff(c_5294, plain, (![C_177, B_178, A_179]: (k3_xboole_0(k10_relat_1(C_177, B_178), A_179)=k10_relat_1(k7_relat_1(C_177, A_179), B_178) | ~v1_relat_1(C_177))), inference(superposition, [status(thm), theory('equality')], [c_2210, c_2])).
% 36.49/27.02  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 36.49/27.02  tff(c_94, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 36.49/27.02  tff(c_108, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), A_15)=A_15)), inference(resolution, [status(thm)], [c_20, c_94])).
% 36.49/27.02  tff(c_20032, plain, (![C_363, A_364, B_365]: (k2_xboole_0(k10_relat_1(k7_relat_1(C_363, A_364), B_365), k10_relat_1(C_363, B_365))=k10_relat_1(C_363, B_365) | ~v1_relat_1(C_363))), inference(superposition, [status(thm), theory('equality')], [c_5294, c_108])).
% 36.49/27.02  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.49/27.02  tff(c_261, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(k2_xboole_0(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 36.49/27.02  tff(c_292, plain, (![A_61, B_62]: (r1_tarski(A_61, k2_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_14, c_261])).
% 36.49/27.02  tff(c_22, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.49/27.02  tff(c_319, plain, (![A_61, B_62]: (k3_xboole_0(A_61, k2_xboole_0(A_61, B_62))=A_61)), inference(resolution, [status(thm)], [c_292, c_22])).
% 36.49/27.02  tff(c_20114, plain, (![C_363, A_364, B_365]: (k3_xboole_0(k10_relat_1(k7_relat_1(C_363, A_364), B_365), k10_relat_1(C_363, B_365))=k10_relat_1(k7_relat_1(C_363, A_364), B_365) | ~v1_relat_1(C_363))), inference(superposition, [status(thm), theory('equality')], [c_20032, c_319])).
% 36.49/27.02  tff(c_128179, plain, (![C_1120, B_1121, A_1122]: (k3_xboole_0(k10_relat_1(C_1120, B_1121), k10_relat_1(k7_relat_1(C_1120, A_1122), B_1121))=k10_relat_1(k7_relat_1(C_1120, A_1122), B_1121) | ~v1_relat_1(C_1120))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20114])).
% 36.49/27.02  tff(c_2988, plain, (![C_133, A_134, B_135]: (r1_tarski(k10_relat_1(k7_relat_1(C_133, A_134), B_135), A_134) | ~v1_relat_1(C_133))), inference(superposition, [status(thm), theory('equality')], [c_2210, c_20])).
% 36.49/27.02  tff(c_3000, plain, (![C_133, A_134]: (r1_tarski(k1_relat_1(k7_relat_1(C_133, A_134)), A_134) | ~v1_relat_1(C_133) | ~v1_relat_1(k7_relat_1(C_133, A_134)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2988])).
% 36.49/27.02  tff(c_28272, plain, (r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_28251])).
% 36.49/27.02  tff(c_28293, plain, (k3_xboole_0('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))='#skF_2'), inference(resolution, [status(thm)], [c_28272, c_22])).
% 36.49/27.02  tff(c_248, plain, (![B_55, A_56]: (r1_tarski(k10_relat_1(B_55, A_56), k1_relat_1(B_55)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.49/27.02  tff(c_253, plain, (![B_55, A_56]: (k3_xboole_0(k10_relat_1(B_55, A_56), k1_relat_1(B_55))=k10_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_248, c_22])).
% 36.49/27.02  tff(c_259, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), k10_relat_1(B_55, A_56))=k10_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_253])).
% 36.49/27.02  tff(c_45156, plain, (![A_580, A_581]: (k3_xboole_0(k1_relat_1(k7_relat_1(A_580, A_581)), k3_xboole_0(A_581, k1_relat_1(A_580)))=k10_relat_1(k7_relat_1(A_580, A_581), k2_relat_1(A_580)) | ~v1_relat_1(k7_relat_1(A_580, A_581)) | ~v1_relat_1(A_580) | ~v1_relat_1(A_580))), inference(superposition, [status(thm), theory('equality')], [c_9263, c_259])).
% 36.49/27.02  tff(c_45512, plain, (k3_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), '#skF_2')=k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k2_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_45156])).
% 36.49/27.02  tff(c_45578, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k2_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_28273, c_28293, c_2, c_45512])).
% 36.49/27.02  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.49/27.02  tff(c_257, plain, (![B_55, A_56]: (k10_relat_1(B_55, A_56)=k1_relat_1(B_55) | ~r1_tarski(k1_relat_1(B_55), k10_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_248, c_10])).
% 36.49/27.02  tff(c_51451, plain, (![A_633, A_634]: (k10_relat_1(k7_relat_1(A_633, A_634), k2_relat_1(A_633))=k1_relat_1(k7_relat_1(A_633, A_634)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_633, A_634)), k3_xboole_0(A_634, k1_relat_1(A_633))) | ~v1_relat_1(k7_relat_1(A_633, A_634)) | ~v1_relat_1(A_633) | ~v1_relat_1(A_633))), inference(superposition, [status(thm), theory('equality')], [c_9263, c_257])).
% 36.49/27.02  tff(c_51518, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k2_relat_1('#skF_3'))=k1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_51451])).
% 36.49/27.02  tff(c_51548, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_28273, c_45578, c_51518])).
% 36.49/27.02  tff(c_51549, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_51548])).
% 36.49/27.02  tff(c_51552, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_3000, c_51549])).
% 36.49/27.02  tff(c_51556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28273, c_40, c_51552])).
% 36.49/27.02  tff(c_51557, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_51548])).
% 36.49/27.02  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 36.49/27.02  tff(c_260, plain, (![B_55, A_56]: (k2_xboole_0(k10_relat_1(B_55, A_56), k1_relat_1(B_55))=k1_relat_1(B_55) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_248, c_18])).
% 36.49/27.02  tff(c_51637, plain, (![A_56]: (k2_xboole_0(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_56), '#skF_2')=k1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_51557, c_260])).
% 36.49/27.02  tff(c_51678, plain, (![A_56]: (k2_xboole_0(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_56), '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28273, c_51557, c_51637])).
% 36.49/27.02  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(k2_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 36.49/27.02  tff(c_392, plain, (![A_67, B_68, B_69]: (r1_tarski(A_67, k2_xboole_0(k2_xboole_0(A_67, B_68), B_69)))), inference(resolution, [status(thm)], [c_292, c_16])).
% 36.49/27.02  tff(c_544, plain, (![A_77, B_78, B_79]: (r1_tarski(k3_xboole_0(A_77, B_78), k2_xboole_0(A_77, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_392])).
% 36.49/27.02  tff(c_56169, plain, (![A_671, B_672, B_673]: (k2_xboole_0(k3_xboole_0(A_671, B_672), k2_xboole_0(A_671, B_673))=k2_xboole_0(A_671, B_673))), inference(resolution, [status(thm)], [c_544, c_18])).
% 36.49/27.02  tff(c_56370, plain, (![A_56, B_672]: (k2_xboole_0(k3_xboole_0(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_56), B_672), '#skF_2')=k2_xboole_0(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_56), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51678, c_56169])).
% 36.49/27.02  tff(c_56724, plain, (![A_56, B_672]: (k2_xboole_0(k3_xboole_0(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_56), B_672), '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51678, c_56370])).
% 36.49/27.02  tff(c_128257, plain, (![A_1122, B_1121]: (k2_xboole_0(k10_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_1122), B_1121), '#skF_2')='#skF_2' | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_128179, c_56724])).
% 36.49/27.02  tff(c_128816, plain, (![A_1122, B_1121]: (k2_xboole_0(k10_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_1122), B_1121), '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28273, c_128257])).
% 36.49/27.02  tff(c_145980, plain, (![A_1226, A_1227]: (k2_xboole_0(k10_relat_1(k7_relat_1(A_1226, A_1227), k2_relat_1(A_1226)), k1_relat_1(A_1226))=k10_relat_1(A_1226, k2_relat_1(A_1226)) | ~v1_relat_1(A_1226) | ~v1_relat_1(A_1226))), inference(superposition, [status(thm), theory('equality')], [c_32, c_20032])).
% 36.49/27.02  tff(c_146275, plain, (![A_1227]: (k2_xboole_0(k10_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_1227), k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))), '#skF_2')=k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_51557, c_145980])).
% 36.49/27.02  tff(c_146346, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k2_relat_1(k7_relat_1('#skF_3', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28273, c_28273, c_128816, c_146275])).
% 36.49/27.02  tff(c_45, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.49/27.02  tff(c_60, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_45, c_20])).
% 36.49/27.02  tff(c_2295, plain, (![C_126, A_125, B_127]: (r1_tarski(k10_relat_1(k7_relat_1(C_126, A_125), B_127), k10_relat_1(C_126, B_127)) | ~v1_relat_1(C_126))), inference(superposition, [status(thm), theory('equality')], [c_2210, c_60])).
% 36.49/27.02  tff(c_146537, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_3', k2_relat_1(k7_relat_1('#skF_3', '#skF_2')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_146346, c_2295])).
% 36.49/27.02  tff(c_146695, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_3', k2_relat_1(k7_relat_1('#skF_3', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_146537])).
% 36.49/27.02  tff(c_146764, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_146695])).
% 36.49/27.02  tff(c_146788, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_146764])).
% 36.49/27.02  tff(c_146790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_146788])).
% 36.49/27.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.49/27.02  
% 36.49/27.02  Inference rules
% 36.49/27.02  ----------------------
% 36.49/27.02  #Ref     : 0
% 36.49/27.02  #Sup     : 37566
% 36.49/27.02  #Fact    : 0
% 36.49/27.02  #Define  : 0
% 36.49/27.02  #Split   : 3
% 36.49/27.02  #Chain   : 0
% 36.49/27.02  #Close   : 0
% 36.49/27.02  
% 36.49/27.02  Ordering : KBO
% 36.49/27.02  
% 36.49/27.02  Simplification rules
% 36.49/27.02  ----------------------
% 36.49/27.02  #Subsume      : 7508
% 36.49/27.02  #Demod        : 24321
% 36.49/27.02  #Tautology    : 15359
% 36.49/27.02  #SimpNegUnit  : 7
% 36.49/27.02  #BackRed      : 12
% 36.49/27.02  
% 36.49/27.02  #Partial instantiations: 0
% 36.49/27.02  #Strategies tried      : 1
% 36.49/27.02  
% 36.49/27.02  Timing (in seconds)
% 36.49/27.02  ----------------------
% 36.49/27.03  Preprocessing        : 0.31
% 36.49/27.03  Parsing              : 0.16
% 36.49/27.03  CNF conversion       : 0.02
% 36.49/27.03  Main loop            : 25.91
% 36.49/27.03  Inferencing          : 2.66
% 36.49/27.03  Reduction            : 14.28
% 36.49/27.03  Demodulation         : 13.06
% 36.49/27.03  BG Simplification    : 0.35
% 36.49/27.03  Subsumption          : 7.39
% 36.49/27.03  Abstraction          : 0.61
% 36.49/27.03  MUC search           : 0.00
% 36.49/27.03  Cooper               : 0.00
% 36.49/27.03  Total                : 26.25
% 36.49/27.03  Index Insertion      : 0.00
% 36.49/27.03  Index Deletion       : 0.00
% 36.49/27.03  Index Matching       : 0.00
% 36.49/27.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
