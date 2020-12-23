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
% DateTime   : Thu Dec  3 10:04:56 EST 2020

% Result     : Theorem 19.26s
% Output     : CNFRefutation 19.26s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 250 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(k7_relat_1(C,A),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1052,plain,(
    ! [C_126,A_127,D_128,B_129] :
      ( r1_tarski(k9_relat_1(C_126,A_127),k9_relat_1(D_128,B_129))
      | ~ r1_tarski(A_127,B_129)
      | ~ r1_tarski(C_126,D_128)
      | ~ v1_relat_1(D_128)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_213,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(A_77,k3_xboole_0(B_78,C_79))
      | ~ r1_tarski(A_77,C_79)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_240,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2')
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_213,c_34])).

tff(c_580,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_1058,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1052,c_580])).

tff(c_1078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6,c_8,c_1058])).

tff(c_1079,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    ! [B_31,A_30] :
      ( k10_relat_1(B_31,k3_xboole_0(k2_relat_1(B_31),A_30)) = k10_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1395,plain,(
    ! [B_145,A_146] :
      ( k9_relat_1(B_145,k10_relat_1(B_145,A_146)) = A_146
      | ~ r1_tarski(A_146,k2_relat_1(B_145))
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8649,plain,(
    ! [B_353,B_354] :
      ( k9_relat_1(B_353,k10_relat_1(B_353,k3_xboole_0(k2_relat_1(B_353),B_354))) = k3_xboole_0(k2_relat_1(B_353),B_354)
      | ~ v1_funct_1(B_353)
      | ~ v1_relat_1(B_353) ) ),
    inference(resolution,[status(thm)],[c_8,c_1395])).

tff(c_8712,plain,(
    ! [B_31,A_30] :
      ( k9_relat_1(B_31,k10_relat_1(B_31,A_30)) = k3_xboole_0(k2_relat_1(B_31),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8649])).

tff(c_1080,plain,(
    r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_43,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_221,plain,(
    ! [B_78,C_79] :
      ( k3_xboole_0(B_78,C_79) = B_78
      | ~ r1_tarski(B_78,C_79)
      | ~ r1_tarski(B_78,B_78) ) ),
    inference(resolution,[status(thm)],[c_213,c_48])).

tff(c_238,plain,(
    ! [B_78,C_79] :
      ( k3_xboole_0(B_78,C_79) = B_78
      | ~ r1_tarski(B_78,C_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_221])).

tff(c_1088,plain,(
    k3_xboole_0(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) = k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1080,c_238])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1207,plain,(
    ! [C_136,A_137,B_138] :
      ( k7_relat_1(k7_relat_1(C_136,A_137),B_138) = k7_relat_1(C_136,k3_xboole_0(A_137,B_138))
      | ~ v1_relat_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10137,plain,(
    ! [C_385,A_386,B_387] :
      ( k2_relat_1(k7_relat_1(C_385,k3_xboole_0(A_386,B_387))) = k9_relat_1(k7_relat_1(C_385,A_386),B_387)
      | ~ v1_relat_1(k7_relat_1(C_385,A_386))
      | ~ v1_relat_1(C_385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_22])).

tff(c_55675,plain,(
    ! [C_972,A_973,B_974] :
      ( k9_relat_1(k7_relat_1(C_972,A_973),B_974) = k9_relat_1(C_972,k3_xboole_0(A_973,B_974))
      | ~ v1_relat_1(C_972)
      | ~ v1_relat_1(k7_relat_1(C_972,A_973))
      | ~ v1_relat_1(C_972) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10137,c_22])).

tff(c_55799,plain,(
    ! [A_977,B_978,B_979] :
      ( k9_relat_1(k7_relat_1(A_977,B_978),B_979) = k9_relat_1(A_977,k3_xboole_0(B_978,B_979))
      | ~ v1_relat_1(A_977) ) ),
    inference(resolution,[status(thm)],[c_14,c_55675])).

tff(c_26,plain,(
    ! [C_29,A_27,B_28] :
      ( r1_tarski(k9_relat_1(k7_relat_1(C_29,A_27),B_28),k9_relat_1(C_29,B_28))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56295,plain,(
    ! [A_984,B_985,B_986] :
      ( r1_tarski(k9_relat_1(A_984,k3_xboole_0(B_985,B_986)),k9_relat_1(A_984,B_986))
      | ~ v1_relat_1(A_984)
      | ~ v1_relat_1(A_984) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55799,c_26])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57465,plain,(
    ! [A_998,A_999,B_1000,B_1001] :
      ( r1_tarski(A_998,k9_relat_1(A_999,B_1000))
      | ~ r1_tarski(A_998,k9_relat_1(A_999,k3_xboole_0(B_1001,B_1000)))
      | ~ v1_relat_1(A_999) ) ),
    inference(resolution,[status(thm)],[c_56295,c_12])).

tff(c_59352,plain,(
    ! [A_1021,B_1022,B_1023,B_1024] :
      ( r1_tarski(k3_xboole_0(k9_relat_1(A_1021,k3_xboole_0(B_1022,B_1023)),B_1024),k9_relat_1(A_1021,B_1023))
      | ~ v1_relat_1(A_1021) ) ),
    inference(resolution,[status(thm)],[c_8,c_57465])).

tff(c_59541,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_59352])).

tff(c_59605,plain,(
    r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_59541])).

tff(c_61141,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k2_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8712,c_59605])).

tff(c_61168,plain,(
    r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k2_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_36,c_61141])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(k2_relat_1(B_19),A_18) = k2_relat_1(k8_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_243,plain,(
    ! [B_80,C_81] :
      ( k3_xboole_0(B_80,C_81) = B_80
      | ~ r1_tarski(B_80,C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_221])).

tff(c_345,plain,(
    ! [A_83,B_84] : k3_xboole_0(k3_xboole_0(A_83,B_84),A_83) = k3_xboole_0(A_83,B_84) ),
    inference(resolution,[status(thm)],[c_8,c_243])).

tff(c_5677,plain,(
    ! [A_301,B_302] :
      ( k3_xboole_0(k2_relat_1(k8_relat_1(A_301,B_302)),k2_relat_1(B_302)) = k3_xboole_0(k2_relat_1(B_302),A_301)
      | ~ v1_relat_1(B_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_345])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_16,B_17)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_469,plain,(
    ! [A_88,A_89,B_90] :
      ( r1_tarski(A_88,A_89)
      | ~ r1_tarski(A_88,k2_relat_1(k8_relat_1(A_89,B_90)))
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_506,plain,(
    ! [A_89,B_90,B_4] :
      ( r1_tarski(k3_xboole_0(k2_relat_1(k8_relat_1(A_89,B_90)),B_4),A_89)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_8,c_469])).

tff(c_5834,plain,(
    ! [B_303,A_304] :
      ( r1_tarski(k3_xboole_0(k2_relat_1(B_303),A_304),A_304)
      | ~ v1_relat_1(B_303)
      | ~ v1_relat_1(B_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5677,c_506])).

tff(c_5957,plain,(
    ! [A_8,A_304,B_303] :
      ( r1_tarski(A_8,A_304)
      | ~ r1_tarski(A_8,k3_xboole_0(k2_relat_1(B_303),A_304))
      | ~ v1_relat_1(B_303) ) ),
    inference(resolution,[status(thm)],[c_5834,c_12])).

tff(c_61212,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61168,c_5957])).

tff(c_61268,plain,(
    r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_61212])).

tff(c_61270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1079,c_61268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.26/11.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.26/11.18  
% 19.26/11.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.26/11.18  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 19.26/11.18  
% 19.26/11.18  %Foreground sorts:
% 19.26/11.18  
% 19.26/11.18  
% 19.26/11.18  %Background operators:
% 19.26/11.18  
% 19.26/11.18  
% 19.26/11.18  %Foreground operators:
% 19.26/11.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 19.26/11.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.26/11.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.26/11.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.26/11.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.26/11.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.26/11.18  tff('#skF_2', type, '#skF_2': $i).
% 19.26/11.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.26/11.18  tff('#skF_3', type, '#skF_3': $i).
% 19.26/11.18  tff('#skF_1', type, '#skF_1': $i).
% 19.26/11.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.26/11.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.26/11.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.26/11.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.26/11.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.26/11.18  
% 19.26/11.20  tff(f_103, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 19.26/11.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.26/11.20  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 19.26/11.20  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 19.26/11.20  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 19.26/11.20  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 19.26/11.20  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 19.26/11.20  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 19.26/11.20  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 19.26/11.20  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 19.26/11.20  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(k7_relat_1(C, A), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_relat_1)).
% 19.26/11.20  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 19.26/11.20  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 19.26/11.20  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 19.26/11.20  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.26/11.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.26/11.20  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.26/11.20  tff(c_1052, plain, (![C_126, A_127, D_128, B_129]: (r1_tarski(k9_relat_1(C_126, A_127), k9_relat_1(D_128, B_129)) | ~r1_tarski(A_127, B_129) | ~r1_tarski(C_126, D_128) | ~v1_relat_1(D_128) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_76])).
% 19.26/11.20  tff(c_213, plain, (![A_77, B_78, C_79]: (r1_tarski(A_77, k3_xboole_0(B_78, C_79)) | ~r1_tarski(A_77, C_79) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.26/11.20  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.26/11.20  tff(c_240, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2') | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_213, c_34])).
% 19.26/11.20  tff(c_580, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_240])).
% 19.26/11.20  tff(c_1058, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1052, c_580])).
% 19.26/11.20  tff(c_1078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_6, c_8, c_1058])).
% 19.26/11.20  tff(c_1079, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitRight, [status(thm)], [c_240])).
% 19.26/11.20  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.26/11.20  tff(c_28, plain, (![B_31, A_30]: (k10_relat_1(B_31, k3_xboole_0(k2_relat_1(B_31), A_30))=k10_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.26/11.20  tff(c_1395, plain, (![B_145, A_146]: (k9_relat_1(B_145, k10_relat_1(B_145, A_146))=A_146 | ~r1_tarski(A_146, k2_relat_1(B_145)) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.26/11.20  tff(c_8649, plain, (![B_353, B_354]: (k9_relat_1(B_353, k10_relat_1(B_353, k3_xboole_0(k2_relat_1(B_353), B_354)))=k3_xboole_0(k2_relat_1(B_353), B_354) | ~v1_funct_1(B_353) | ~v1_relat_1(B_353))), inference(resolution, [status(thm)], [c_8, c_1395])).
% 19.26/11.20  tff(c_8712, plain, (![B_31, A_30]: (k9_relat_1(B_31, k10_relat_1(B_31, A_30))=k3_xboole_0(k2_relat_1(B_31), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8649])).
% 19.26/11.20  tff(c_1080, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_240])).
% 19.26/11.20  tff(c_43, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.26/11.20  tff(c_48, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_43])).
% 19.26/11.20  tff(c_221, plain, (![B_78, C_79]: (k3_xboole_0(B_78, C_79)=B_78 | ~r1_tarski(B_78, C_79) | ~r1_tarski(B_78, B_78))), inference(resolution, [status(thm)], [c_213, c_48])).
% 19.26/11.20  tff(c_238, plain, (![B_78, C_79]: (k3_xboole_0(B_78, C_79)=B_78 | ~r1_tarski(B_78, C_79))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_221])).
% 19.26/11.20  tff(c_1088, plain, (k3_xboole_0(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))=k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_1080, c_238])).
% 19.26/11.20  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.26/11.20  tff(c_1207, plain, (![C_136, A_137, B_138]: (k7_relat_1(k7_relat_1(C_136, A_137), B_138)=k7_relat_1(C_136, k3_xboole_0(A_137, B_138)) | ~v1_relat_1(C_136))), inference(cnfTransformation, [status(thm)], [f_53])).
% 19.26/11.20  tff(c_22, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.26/11.20  tff(c_10137, plain, (![C_385, A_386, B_387]: (k2_relat_1(k7_relat_1(C_385, k3_xboole_0(A_386, B_387)))=k9_relat_1(k7_relat_1(C_385, A_386), B_387) | ~v1_relat_1(k7_relat_1(C_385, A_386)) | ~v1_relat_1(C_385))), inference(superposition, [status(thm), theory('equality')], [c_1207, c_22])).
% 19.26/11.20  tff(c_55675, plain, (![C_972, A_973, B_974]: (k9_relat_1(k7_relat_1(C_972, A_973), B_974)=k9_relat_1(C_972, k3_xboole_0(A_973, B_974)) | ~v1_relat_1(C_972) | ~v1_relat_1(k7_relat_1(C_972, A_973)) | ~v1_relat_1(C_972))), inference(superposition, [status(thm), theory('equality')], [c_10137, c_22])).
% 19.26/11.20  tff(c_55799, plain, (![A_977, B_978, B_979]: (k9_relat_1(k7_relat_1(A_977, B_978), B_979)=k9_relat_1(A_977, k3_xboole_0(B_978, B_979)) | ~v1_relat_1(A_977))), inference(resolution, [status(thm)], [c_14, c_55675])).
% 19.26/11.20  tff(c_26, plain, (![C_29, A_27, B_28]: (r1_tarski(k9_relat_1(k7_relat_1(C_29, A_27), B_28), k9_relat_1(C_29, B_28)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.26/11.20  tff(c_56295, plain, (![A_984, B_985, B_986]: (r1_tarski(k9_relat_1(A_984, k3_xboole_0(B_985, B_986)), k9_relat_1(A_984, B_986)) | ~v1_relat_1(A_984) | ~v1_relat_1(A_984))), inference(superposition, [status(thm), theory('equality')], [c_55799, c_26])).
% 19.26/11.20  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.26/11.20  tff(c_57465, plain, (![A_998, A_999, B_1000, B_1001]: (r1_tarski(A_998, k9_relat_1(A_999, B_1000)) | ~r1_tarski(A_998, k9_relat_1(A_999, k3_xboole_0(B_1001, B_1000))) | ~v1_relat_1(A_999))), inference(resolution, [status(thm)], [c_56295, c_12])).
% 19.26/11.20  tff(c_59352, plain, (![A_1021, B_1022, B_1023, B_1024]: (r1_tarski(k3_xboole_0(k9_relat_1(A_1021, k3_xboole_0(B_1022, B_1023)), B_1024), k9_relat_1(A_1021, B_1023)) | ~v1_relat_1(A_1021))), inference(resolution, [status(thm)], [c_8, c_57465])).
% 19.26/11.20  tff(c_59541, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_59352])).
% 19.26/11.20  tff(c_59605, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_59541])).
% 19.26/11.20  tff(c_61141, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k2_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8712, c_59605])).
% 19.26/11.20  tff(c_61168, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k2_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_36, c_61141])).
% 19.26/11.20  tff(c_20, plain, (![B_19, A_18]: (k3_xboole_0(k2_relat_1(B_19), A_18)=k2_relat_1(k8_relat_1(A_18, B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.26/11.20  tff(c_243, plain, (![B_80, C_81]: (k3_xboole_0(B_80, C_81)=B_80 | ~r1_tarski(B_80, C_81))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_221])).
% 19.26/11.20  tff(c_345, plain, (![A_83, B_84]: (k3_xboole_0(k3_xboole_0(A_83, B_84), A_83)=k3_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_8, c_243])).
% 19.26/11.20  tff(c_5677, plain, (![A_301, B_302]: (k3_xboole_0(k2_relat_1(k8_relat_1(A_301, B_302)), k2_relat_1(B_302))=k3_xboole_0(k2_relat_1(B_302), A_301) | ~v1_relat_1(B_302))), inference(superposition, [status(thm), theory('equality')], [c_20, c_345])).
% 19.26/11.20  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k8_relat_1(A_16, B_17)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.26/11.20  tff(c_66, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.26/11.20  tff(c_469, plain, (![A_88, A_89, B_90]: (r1_tarski(A_88, A_89) | ~r1_tarski(A_88, k2_relat_1(k8_relat_1(A_89, B_90))) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_18, c_66])).
% 19.26/11.20  tff(c_506, plain, (![A_89, B_90, B_4]: (r1_tarski(k3_xboole_0(k2_relat_1(k8_relat_1(A_89, B_90)), B_4), A_89) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_8, c_469])).
% 19.26/11.20  tff(c_5834, plain, (![B_303, A_304]: (r1_tarski(k3_xboole_0(k2_relat_1(B_303), A_304), A_304) | ~v1_relat_1(B_303) | ~v1_relat_1(B_303))), inference(superposition, [status(thm), theory('equality')], [c_5677, c_506])).
% 19.26/11.20  tff(c_5957, plain, (![A_8, A_304, B_303]: (r1_tarski(A_8, A_304) | ~r1_tarski(A_8, k3_xboole_0(k2_relat_1(B_303), A_304)) | ~v1_relat_1(B_303))), inference(resolution, [status(thm)], [c_5834, c_12])).
% 19.26/11.20  tff(c_61212, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61168, c_5957])).
% 19.26/11.20  tff(c_61268, plain, (r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_61212])).
% 19.26/11.20  tff(c_61270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1079, c_61268])).
% 19.26/11.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.26/11.20  
% 19.26/11.20  Inference rules
% 19.26/11.20  ----------------------
% 19.26/11.20  #Ref     : 0
% 19.26/11.20  #Sup     : 16302
% 19.26/11.20  #Fact    : 0
% 19.26/11.20  #Define  : 0
% 19.26/11.20  #Split   : 3
% 19.26/11.20  #Chain   : 0
% 19.26/11.20  #Close   : 0
% 19.26/11.20  
% 19.26/11.20  Ordering : KBO
% 19.26/11.20  
% 19.26/11.20  Simplification rules
% 19.26/11.20  ----------------------
% 19.26/11.20  #Subsume      : 4502
% 19.26/11.20  #Demod        : 2069
% 19.26/11.20  #Tautology    : 1598
% 19.26/11.20  #SimpNegUnit  : 1
% 19.26/11.20  #BackRed      : 0
% 19.26/11.20  
% 19.26/11.20  #Partial instantiations: 0
% 19.26/11.20  #Strategies tried      : 1
% 19.26/11.20  
% 19.26/11.20  Timing (in seconds)
% 19.26/11.20  ----------------------
% 19.26/11.20  Preprocessing        : 0.33
% 19.26/11.20  Parsing              : 0.18
% 19.26/11.20  CNF conversion       : 0.02
% 19.26/11.20  Main loop            : 10.10
% 19.26/11.20  Inferencing          : 1.69
% 19.26/11.20  Reduction            : 2.24
% 19.26/11.20  Demodulation         : 1.70
% 19.26/11.20  BG Simplification    : 0.25
% 19.26/11.20  Subsumption          : 5.32
% 19.26/11.20  Abstraction          : 0.39
% 19.26/11.20  MUC search           : 0.00
% 19.26/11.20  Cooper               : 0.00
% 19.26/11.20  Total                : 10.46
% 19.26/11.20  Index Insertion      : 0.00
% 19.26/11.20  Index Deletion       : 0.00
% 19.26/11.20  Index Matching       : 0.00
% 19.26/11.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
