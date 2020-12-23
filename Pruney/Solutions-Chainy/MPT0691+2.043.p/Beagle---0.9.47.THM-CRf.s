%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 10.67s
% Output     : CNFRefutation 10.94s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 117 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  130 ( 172 expanded)
%              Number of equality atoms :   55 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_93,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k3_xboole_0(k1_relat_1(B),A),k9_relat_1(k4_relat_1(B),k9_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

tff(c_46,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k5_relat_1(B_19,k6_relat_1(A_18)) = k8_relat_1(A_18,B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_508,plain,(
    ! [A_79,B_80] :
      ( k10_relat_1(A_79,k1_relat_1(B_80)) = k1_relat_1(k5_relat_1(A_79,B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_520,plain,(
    ! [A_79,A_31] :
      ( k1_relat_1(k5_relat_1(A_79,k6_relat_1(A_31))) = k10_relat_1(A_79,A_31)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_508])).

tff(c_805,plain,(
    ! [A_89,A_90] :
      ( k1_relat_1(k5_relat_1(A_89,k6_relat_1(A_90))) = k10_relat_1(A_89,A_90)
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_520])).

tff(c_821,plain,(
    ! [A_18,B_19] :
      ( k1_relat_1(k8_relat_1(A_18,B_19)) = k10_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_805])).

tff(c_18,plain,(
    ! [A_14] :
      ( v1_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k8_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_27] :
      ( k2_relat_1(k4_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_33,B_34] :
      ( k5_relat_1(k6_relat_1(A_33),B_34) = k7_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_32] : k4_relat_1(k6_relat_1(A_32)) = k6_relat_1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_692,plain,(
    ! [B_85,A_86] :
      ( k5_relat_1(k4_relat_1(B_85),k4_relat_1(A_86)) = k4_relat_1(k5_relat_1(A_86,B_85))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_701,plain,(
    ! [A_32,A_86] :
      ( k5_relat_1(k6_relat_1(A_32),k4_relat_1(A_86)) = k4_relat_1(k5_relat_1(A_86,k6_relat_1(A_32)))
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_692])).

tff(c_1167,plain,(
    ! [A_101,A_102] :
      ( k5_relat_1(k6_relat_1(A_101),k4_relat_1(A_102)) = k4_relat_1(k5_relat_1(A_102,k6_relat_1(A_101)))
      | ~ v1_relat_1(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_701])).

tff(c_2644,plain,(
    ! [A_141,A_142] :
      ( k4_relat_1(k5_relat_1(A_141,k6_relat_1(A_142))) = k7_relat_1(k4_relat_1(A_141),A_142)
      | ~ v1_relat_1(A_141)
      | ~ v1_relat_1(k4_relat_1(A_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1167])).

tff(c_6499,plain,(
    ! [B_202,A_203] :
      ( k7_relat_1(k4_relat_1(B_202),A_203) = k4_relat_1(k8_relat_1(A_203,B_202))
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(k4_relat_1(B_202))
      | ~ v1_relat_1(B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2644])).

tff(c_6522,plain,(
    ! [A_204,A_205] :
      ( k7_relat_1(k4_relat_1(A_204),A_205) = k4_relat_1(k8_relat_1(A_205,A_204))
      | ~ v1_relat_1(A_204) ) ),
    inference(resolution,[status(thm)],[c_18,c_6499])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6656,plain,(
    ! [A_212,A_213] :
      ( k2_relat_1(k4_relat_1(k8_relat_1(A_212,A_213))) = k9_relat_1(k4_relat_1(A_213),A_212)
      | ~ v1_relat_1(k4_relat_1(A_213))
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6522,c_26])).

tff(c_11512,plain,(
    ! [A_301,A_302] :
      ( k9_relat_1(k4_relat_1(A_301),A_302) = k1_relat_1(k8_relat_1(A_302,A_301))
      | ~ v1_relat_1(k4_relat_1(A_301))
      | ~ v1_relat_1(A_301)
      | ~ v1_relat_1(k8_relat_1(A_302,A_301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6656])).

tff(c_11792,plain,(
    ! [B_305,A_306] :
      ( k9_relat_1(k4_relat_1(B_305),A_306) = k1_relat_1(k8_relat_1(A_306,B_305))
      | ~ v1_relat_1(k4_relat_1(B_305))
      | ~ v1_relat_1(B_305) ) ),
    inference(resolution,[status(thm)],[c_22,c_11512])).

tff(c_11826,plain,(
    ! [A_307,A_308] :
      ( k9_relat_1(k4_relat_1(A_307),A_308) = k1_relat_1(k8_relat_1(A_308,A_307))
      | ~ v1_relat_1(A_307) ) ),
    inference(resolution,[status(thm)],[c_18,c_11792])).

tff(c_48,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_241,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_249,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_241])).

tff(c_191,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_195,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_191])).

tff(c_376,plain,(
    ! [A_75,B_76] : k5_xboole_0(k5_xboole_0(A_75,B_76),k2_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_403,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1',k1_relat_1('#skF_2')),k1_relat_1('#skF_2')) = k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_376])).

tff(c_425,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1',k1_relat_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_403])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_463,plain,(
    k5_xboole_0(k1_relat_1('#skF_2'),k5_xboole_0('#skF_1',k1_relat_1('#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_2])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_182])).

tff(c_254,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_267,plain,(
    k5_xboole_0(k1_relat_1('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_254])).

tff(c_274,plain,(
    k2_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_267])).

tff(c_535,plain,(
    ! [A_81,B_82] : k5_xboole_0(k2_xboole_0(A_81,B_82),k5_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_376])).

tff(c_568,plain,(
    k5_xboole_0(k1_relat_1('#skF_2'),k5_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_535])).

tff(c_589,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_2,c_568])).

tff(c_961,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(B_95),A_96),k9_relat_1(k4_relat_1(B_95),k9_relat_1(B_95,A_96)))
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_979,plain,
    ( r1_tarski('#skF_1',k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_961])).

tff(c_999,plain,(
    r1_tarski('#skF_1',k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_979])).

tff(c_11933,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k8_relat_1(k9_relat_1('#skF_2','#skF_1'),'#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11826,c_999])).

tff(c_11989,plain,(
    r1_tarski('#skF_1',k1_relat_1(k8_relat_1(k9_relat_1('#skF_2','#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11933])).

tff(c_12010,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_11989])).

tff(c_12015,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_12010])).

tff(c_12017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_12015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.67/4.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.67/4.09  
% 10.67/4.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.67/4.09  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.67/4.09  
% 10.67/4.09  %Foreground sorts:
% 10.67/4.09  
% 10.67/4.09  
% 10.67/4.09  %Background operators:
% 10.67/4.09  
% 10.67/4.09  
% 10.67/4.09  %Foreground operators:
% 10.67/4.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 10.67/4.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.67/4.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.67/4.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.67/4.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.67/4.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.67/4.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.67/4.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.67/4.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.67/4.09  tff('#skF_2', type, '#skF_2': $i).
% 10.67/4.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.67/4.09  tff('#skF_1', type, '#skF_1': $i).
% 10.67/4.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.67/4.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.67/4.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.67/4.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.67/4.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.67/4.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.67/4.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.67/4.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.67/4.09  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.67/4.09  
% 10.67/4.13  tff(f_104, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 10.67/4.13  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 10.67/4.13  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 10.67/4.13  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.67/4.13  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 10.67/4.13  tff(f_49, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 10.67/4.13  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 10.67/4.13  tff(f_80, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 10.67/4.13  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 10.67/4.13  tff(f_93, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 10.67/4.13  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 10.67/4.13  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 10.67/4.13  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.67/4.13  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.67/4.13  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.67/4.13  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.67/4.13  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.67/4.13  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.67/4.13  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.67/4.13  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k3_xboole_0(k1_relat_1(B), A), k9_relat_1(k4_relat_1(B), k9_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_relat_1)).
% 10.67/4.13  tff(c_46, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.67/4.13  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.67/4.13  tff(c_24, plain, (![B_19, A_18]: (k5_relat_1(B_19, k6_relat_1(A_18))=k8_relat_1(A_18, B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.67/4.13  tff(c_20, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.67/4.13  tff(c_38, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.67/4.13  tff(c_508, plain, (![A_79, B_80]: (k10_relat_1(A_79, k1_relat_1(B_80))=k1_relat_1(k5_relat_1(A_79, B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.67/4.13  tff(c_520, plain, (![A_79, A_31]: (k1_relat_1(k5_relat_1(A_79, k6_relat_1(A_31)))=k10_relat_1(A_79, A_31) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_38, c_508])).
% 10.67/4.13  tff(c_805, plain, (![A_89, A_90]: (k1_relat_1(k5_relat_1(A_89, k6_relat_1(A_90)))=k10_relat_1(A_89, A_90) | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_520])).
% 10.67/4.13  tff(c_821, plain, (![A_18, B_19]: (k1_relat_1(k8_relat_1(A_18, B_19))=k10_relat_1(B_19, A_18) | ~v1_relat_1(B_19) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_805])).
% 10.67/4.13  tff(c_18, plain, (![A_14]: (v1_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.67/4.13  tff(c_22, plain, (![A_16, B_17]: (v1_relat_1(k8_relat_1(A_16, B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.67/4.13  tff(c_32, plain, (![A_27]: (k2_relat_1(k4_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.67/4.13  tff(c_44, plain, (![A_33, B_34]: (k5_relat_1(k6_relat_1(A_33), B_34)=k7_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.67/4.13  tff(c_42, plain, (![A_32]: (k4_relat_1(k6_relat_1(A_32))=k6_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.67/4.13  tff(c_692, plain, (![B_85, A_86]: (k5_relat_1(k4_relat_1(B_85), k4_relat_1(A_86))=k4_relat_1(k5_relat_1(A_86, B_85)) | ~v1_relat_1(B_85) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.67/4.13  tff(c_701, plain, (![A_32, A_86]: (k5_relat_1(k6_relat_1(A_32), k4_relat_1(A_86))=k4_relat_1(k5_relat_1(A_86, k6_relat_1(A_32))) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_42, c_692])).
% 10.67/4.13  tff(c_1167, plain, (![A_101, A_102]: (k5_relat_1(k6_relat_1(A_101), k4_relat_1(A_102))=k4_relat_1(k5_relat_1(A_102, k6_relat_1(A_101))) | ~v1_relat_1(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_701])).
% 10.67/4.13  tff(c_2644, plain, (![A_141, A_142]: (k4_relat_1(k5_relat_1(A_141, k6_relat_1(A_142)))=k7_relat_1(k4_relat_1(A_141), A_142) | ~v1_relat_1(A_141) | ~v1_relat_1(k4_relat_1(A_141)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1167])).
% 10.67/4.13  tff(c_6499, plain, (![B_202, A_203]: (k7_relat_1(k4_relat_1(B_202), A_203)=k4_relat_1(k8_relat_1(A_203, B_202)) | ~v1_relat_1(B_202) | ~v1_relat_1(k4_relat_1(B_202)) | ~v1_relat_1(B_202))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2644])).
% 10.67/4.13  tff(c_6522, plain, (![A_204, A_205]: (k7_relat_1(k4_relat_1(A_204), A_205)=k4_relat_1(k8_relat_1(A_205, A_204)) | ~v1_relat_1(A_204))), inference(resolution, [status(thm)], [c_18, c_6499])).
% 10.67/4.13  tff(c_26, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.67/4.13  tff(c_6656, plain, (![A_212, A_213]: (k2_relat_1(k4_relat_1(k8_relat_1(A_212, A_213)))=k9_relat_1(k4_relat_1(A_213), A_212) | ~v1_relat_1(k4_relat_1(A_213)) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_6522, c_26])).
% 10.67/4.13  tff(c_11512, plain, (![A_301, A_302]: (k9_relat_1(k4_relat_1(A_301), A_302)=k1_relat_1(k8_relat_1(A_302, A_301)) | ~v1_relat_1(k4_relat_1(A_301)) | ~v1_relat_1(A_301) | ~v1_relat_1(k8_relat_1(A_302, A_301)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6656])).
% 10.67/4.13  tff(c_11792, plain, (![B_305, A_306]: (k9_relat_1(k4_relat_1(B_305), A_306)=k1_relat_1(k8_relat_1(A_306, B_305)) | ~v1_relat_1(k4_relat_1(B_305)) | ~v1_relat_1(B_305))), inference(resolution, [status(thm)], [c_22, c_11512])).
% 10.67/4.13  tff(c_11826, plain, (![A_307, A_308]: (k9_relat_1(k4_relat_1(A_307), A_308)=k1_relat_1(k8_relat_1(A_308, A_307)) | ~v1_relat_1(A_307))), inference(resolution, [status(thm)], [c_18, c_11792])).
% 10.67/4.13  tff(c_48, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.67/4.13  tff(c_241, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.67/4.13  tff(c_249, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_48, c_241])).
% 10.67/4.13  tff(c_191, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.67/4.13  tff(c_195, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_191])).
% 10.67/4.13  tff(c_376, plain, (![A_75, B_76]: (k5_xboole_0(k5_xboole_0(A_75, B_76), k2_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.67/4.13  tff(c_403, plain, (k5_xboole_0(k5_xboole_0('#skF_1', k1_relat_1('#skF_2')), k1_relat_1('#skF_2'))=k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_376])).
% 10.67/4.13  tff(c_425, plain, (k5_xboole_0(k5_xboole_0('#skF_1', k1_relat_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_403])).
% 10.67/4.13  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.67/4.13  tff(c_463, plain, (k5_xboole_0(k1_relat_1('#skF_2'), k5_xboole_0('#skF_1', k1_relat_1('#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_425, c_2])).
% 10.67/4.13  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.67/4.13  tff(c_182, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.67/4.13  tff(c_186, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_182])).
% 10.67/4.13  tff(c_254, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.67/4.13  tff(c_267, plain, (k5_xboole_0(k1_relat_1('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_186, c_254])).
% 10.67/4.13  tff(c_274, plain, (k2_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_267])).
% 10.67/4.13  tff(c_535, plain, (![A_81, B_82]: (k5_xboole_0(k2_xboole_0(A_81, B_82), k5_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_2, c_376])).
% 10.67/4.13  tff(c_568, plain, (k5_xboole_0(k1_relat_1('#skF_2'), k5_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_274, c_535])).
% 10.67/4.13  tff(c_589, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_463, c_2, c_568])).
% 10.67/4.13  tff(c_961, plain, (![B_95, A_96]: (r1_tarski(k3_xboole_0(k1_relat_1(B_95), A_96), k9_relat_1(k4_relat_1(B_95), k9_relat_1(B_95, A_96))) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.67/4.13  tff(c_979, plain, (r1_tarski('#skF_1', k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_589, c_961])).
% 10.67/4.13  tff(c_999, plain, (r1_tarski('#skF_1', k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_979])).
% 10.67/4.13  tff(c_11933, plain, (r1_tarski('#skF_1', k1_relat_1(k8_relat_1(k9_relat_1('#skF_2', '#skF_1'), '#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11826, c_999])).
% 10.67/4.13  tff(c_11989, plain, (r1_tarski('#skF_1', k1_relat_1(k8_relat_1(k9_relat_1('#skF_2', '#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_11933])).
% 10.94/4.13  tff(c_12010, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_821, c_11989])).
% 10.94/4.13  tff(c_12015, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_12010])).
% 10.94/4.13  tff(c_12017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_12015])).
% 10.94/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.13  
% 10.94/4.13  Inference rules
% 10.94/4.13  ----------------------
% 10.94/4.13  #Ref     : 0
% 10.94/4.13  #Sup     : 3075
% 10.94/4.13  #Fact    : 0
% 10.94/4.13  #Define  : 0
% 10.94/4.13  #Split   : 3
% 10.94/4.13  #Chain   : 0
% 10.94/4.13  #Close   : 0
% 10.94/4.13  
% 10.94/4.13  Ordering : KBO
% 10.94/4.13  
% 10.94/4.13  Simplification rules
% 10.94/4.13  ----------------------
% 10.94/4.13  #Subsume      : 76
% 10.94/4.13  #Demod        : 3594
% 10.94/4.13  #Tautology    : 933
% 10.94/4.13  #SimpNegUnit  : 1
% 10.94/4.13  #BackRed      : 27
% 10.94/4.13  
% 10.94/4.13  #Partial instantiations: 0
% 10.94/4.13  #Strategies tried      : 1
% 10.94/4.13  
% 10.94/4.13  Timing (in seconds)
% 10.94/4.13  ----------------------
% 10.94/4.13  Preprocessing        : 0.35
% 10.94/4.13  Parsing              : 0.18
% 10.94/4.13  CNF conversion       : 0.02
% 10.94/4.13  Main loop            : 2.99
% 10.94/4.13  Inferencing          : 0.68
% 10.94/4.13  Reduction            : 1.62
% 10.94/4.14  Demodulation         : 1.36
% 10.94/4.14  BG Simplification    : 0.10
% 10.94/4.14  Subsumption          : 0.42
% 10.94/4.14  Abstraction          : 0.19
% 10.94/4.14  MUC search           : 0.00
% 10.94/4.14  Cooper               : 0.00
% 10.94/4.14  Total                : 3.39
% 10.94/4.14  Index Insertion      : 0.00
% 10.94/4.14  Index Deletion       : 0.00
% 10.94/4.14  Index Matching       : 0.00
% 10.94/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
