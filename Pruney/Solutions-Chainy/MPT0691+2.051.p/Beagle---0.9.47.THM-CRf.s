%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:46 EST 2020

% Result     : Theorem 9.19s
% Output     : CNFRefutation 9.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 490 expanded)
%              Number of leaves         :   36 ( 189 expanded)
%              Depth                    :   19
%              Number of atoms          :  133 ( 979 expanded)
%              Number of equality atoms :   50 ( 296 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_91,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_95,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_46])).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_218,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_227,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_218])).

tff(c_230,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_227])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_366,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_380,plain,(
    ! [A_29,A_77] :
      ( k7_relat_1(k6_relat_1(A_29),A_77) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_77)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_366])).

tff(c_389,plain,(
    ! [A_29,A_77] :
      ( k7_relat_1(k6_relat_1(A_29),A_77) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_380])).

tff(c_902,plain,(
    ! [A_111,B_112] :
      ( k7_relat_1(A_111,k1_relat_1(k7_relat_1(B_112,k1_relat_1(A_111)))) = k7_relat_1(A_111,k1_relat_1(B_112))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_30)),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4342,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_222,k1_relat_1(B_223))),k1_relat_1(k7_relat_1(B_223,k1_relat_1(A_222))))
      | ~ v1_relat_1(A_222)
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_38])).

tff(c_4467,plain,(
    ! [A_29,B_223] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_29)),k1_relat_1(k7_relat_1(B_223,k1_relat_1(k6_relat_1(A_29)))))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ r1_tarski(A_29,k1_relat_1(B_223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_4342])).

tff(c_10347,plain,(
    ! [A_300,B_301] :
      ( r1_tarski(A_300,k1_relat_1(k7_relat_1(B_301,A_300)))
      | ~ v1_relat_1(B_301)
      | ~ r1_tarski(A_300,k1_relat_1(B_301)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34,c_34,c_4467])).

tff(c_174,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [B_31,A_30] :
      ( k1_relat_1(k7_relat_1(B_31,A_30)) = A_30
      | ~ r1_tarski(A_30,k1_relat_1(k7_relat_1(B_31,A_30)))
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_38,c_174])).

tff(c_10932,plain,(
    ! [B_306,A_307] :
      ( k1_relat_1(k7_relat_1(B_306,A_307)) = A_307
      | ~ v1_relat_1(B_306)
      | ~ r1_tarski(A_307,k1_relat_1(B_306)) ) ),
    inference(resolution,[status(thm)],[c_10347,c_183])).

tff(c_11063,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_10932])).

tff(c_11126,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11063])).

tff(c_42,plain,(
    ! [A_34] :
      ( k7_relat_1(A_34,k1_relat_1(A_34)) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_11268,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11126,c_42])).

tff(c_11882,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_11268])).

tff(c_11885,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_11882])).

tff(c_11889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11885])).

tff(c_11891,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_11268])).

tff(c_11890,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_11268])).

tff(c_604,plain,(
    ! [A_93,C_94,B_95] :
      ( k9_relat_1(k7_relat_1(A_93,C_94),B_95) = k9_relat_1(A_93,B_95)
      | ~ r1_tarski(B_95,C_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_611,plain,(
    ! [A_93,C_94] :
      ( k9_relat_1(A_93,k1_relat_1(k7_relat_1(A_93,C_94))) = k2_relat_1(k7_relat_1(A_93,C_94))
      | ~ v1_relat_1(k7_relat_1(A_93,C_94))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_93,C_94)),C_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_26])).

tff(c_11900,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))) = k2_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11890,c_611])).

tff(c_11968,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11891,c_8,c_11126,c_11891,c_11890,c_11890,c_11126,c_11890,c_11900])).

tff(c_28,plain,(
    ! [A_20,C_24,B_23] :
      ( k9_relat_1(k7_relat_1(A_20,C_24),B_23) = k9_relat_1(A_20,B_23)
      | ~ r1_tarski(B_23,C_24)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12937,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11968,c_28])).

tff(c_12944,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_12937])).

tff(c_30,plain,(
    ! [A_25] :
      ( k10_relat_1(A_25,k2_relat_1(A_25)) = k1_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12955,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12944,c_30])).

tff(c_12961,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11891,c_11126,c_12955])).

tff(c_391,plain,(
    ! [A_78,C_79,B_80] :
      ( k3_xboole_0(A_78,k10_relat_1(C_79,B_80)) = k10_relat_1(k7_relat_1(C_79,A_78),B_80)
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_397,plain,(
    ! [A_78,C_79,B_80] :
      ( k5_xboole_0(A_78,k10_relat_1(k7_relat_1(C_79,A_78),B_80)) = k4_xboole_0(A_78,k10_relat_1(C_79,B_80))
      | ~ v1_relat_1(C_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_14])).

tff(c_13092,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12961,c_397])).

tff(c_13102,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_230,c_13092])).

tff(c_13104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_13102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.19/3.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.14  
% 9.19/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.15  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.19/3.15  
% 9.19/3.15  %Foreground sorts:
% 9.19/3.15  
% 9.19/3.15  
% 9.19/3.15  %Background operators:
% 9.19/3.15  
% 9.19/3.15  
% 9.19/3.15  %Foreground operators:
% 9.19/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.19/3.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.19/3.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.19/3.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.19/3.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.19/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.19/3.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.19/3.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.19/3.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.19/3.15  tff('#skF_2', type, '#skF_2': $i).
% 9.19/3.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.19/3.15  tff('#skF_1', type, '#skF_1': $i).
% 9.19/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.19/3.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.19/3.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.19/3.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.19/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.19/3.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.19/3.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.19/3.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.19/3.15  
% 9.19/3.16  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.19/3.16  tff(f_106, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 9.19/3.16  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.19/3.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.19/3.16  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.19/3.16  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.19/3.16  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 9.19/3.16  tff(f_81, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.19/3.16  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 9.19/3.16  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 9.19/3.16  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.19/3.16  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 9.19/3.16  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 9.19/3.16  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 9.19/3.16  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.19/3.16  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 9.19/3.16  tff(c_91, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.19/3.16  tff(c_46, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.19/3.16  tff(c_95, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_46])).
% 9.19/3.16  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.19/3.16  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.19/3.16  tff(c_96, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.19/3.16  tff(c_108, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_96])).
% 9.19/3.16  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.19/3.16  tff(c_218, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.19/3.16  tff(c_227, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_218])).
% 9.19/3.16  tff(c_230, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_227])).
% 9.19/3.16  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.19/3.16  tff(c_48, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.19/3.16  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.19/3.16  tff(c_34, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.19/3.16  tff(c_366, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.19/3.16  tff(c_380, plain, (![A_29, A_77]: (k7_relat_1(k6_relat_1(A_29), A_77)=k6_relat_1(A_29) | ~r1_tarski(A_29, A_77) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_366])).
% 9.19/3.16  tff(c_389, plain, (![A_29, A_77]: (k7_relat_1(k6_relat_1(A_29), A_77)=k6_relat_1(A_29) | ~r1_tarski(A_29, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_380])).
% 9.19/3.16  tff(c_902, plain, (![A_111, B_112]: (k7_relat_1(A_111, k1_relat_1(k7_relat_1(B_112, k1_relat_1(A_111))))=k7_relat_1(A_111, k1_relat_1(B_112)) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.19/3.16  tff(c_38, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_30)), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.19/3.16  tff(c_4342, plain, (![A_222, B_223]: (r1_tarski(k1_relat_1(k7_relat_1(A_222, k1_relat_1(B_223))), k1_relat_1(k7_relat_1(B_223, k1_relat_1(A_222)))) | ~v1_relat_1(A_222) | ~v1_relat_1(B_223) | ~v1_relat_1(A_222))), inference(superposition, [status(thm), theory('equality')], [c_902, c_38])).
% 9.19/3.16  tff(c_4467, plain, (![A_29, B_223]: (r1_tarski(k1_relat_1(k6_relat_1(A_29)), k1_relat_1(k7_relat_1(B_223, k1_relat_1(k6_relat_1(A_29))))) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(B_223) | ~v1_relat_1(k6_relat_1(A_29)) | ~r1_tarski(A_29, k1_relat_1(B_223)))), inference(superposition, [status(thm), theory('equality')], [c_389, c_4342])).
% 9.19/3.16  tff(c_10347, plain, (![A_300, B_301]: (r1_tarski(A_300, k1_relat_1(k7_relat_1(B_301, A_300))) | ~v1_relat_1(B_301) | ~r1_tarski(A_300, k1_relat_1(B_301)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34, c_34, c_4467])).
% 9.19/3.16  tff(c_174, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.19/3.16  tff(c_183, plain, (![B_31, A_30]: (k1_relat_1(k7_relat_1(B_31, A_30))=A_30 | ~r1_tarski(A_30, k1_relat_1(k7_relat_1(B_31, A_30))) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_38, c_174])).
% 9.19/3.16  tff(c_10932, plain, (![B_306, A_307]: (k1_relat_1(k7_relat_1(B_306, A_307))=A_307 | ~v1_relat_1(B_306) | ~r1_tarski(A_307, k1_relat_1(B_306)))), inference(resolution, [status(thm)], [c_10347, c_183])).
% 9.19/3.16  tff(c_11063, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_10932])).
% 9.19/3.16  tff(c_11126, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_11063])).
% 9.19/3.16  tff(c_42, plain, (![A_34]: (k7_relat_1(A_34, k1_relat_1(A_34))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.19/3.16  tff(c_11268, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11126, c_42])).
% 9.19/3.16  tff(c_11882, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_11268])).
% 9.19/3.16  tff(c_11885, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_11882])).
% 9.19/3.16  tff(c_11889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_11885])).
% 9.19/3.16  tff(c_11891, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_11268])).
% 9.19/3.16  tff(c_11890, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_11268])).
% 9.19/3.16  tff(c_604, plain, (![A_93, C_94, B_95]: (k9_relat_1(k7_relat_1(A_93, C_94), B_95)=k9_relat_1(A_93, B_95) | ~r1_tarski(B_95, C_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.19/3.16  tff(c_26, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.19/3.16  tff(c_611, plain, (![A_93, C_94]: (k9_relat_1(A_93, k1_relat_1(k7_relat_1(A_93, C_94)))=k2_relat_1(k7_relat_1(A_93, C_94)) | ~v1_relat_1(k7_relat_1(A_93, C_94)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_93, C_94)), C_94) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_604, c_26])).
% 9.19/3.16  tff(c_11900, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')))=k2_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11890, c_611])).
% 9.19/3.16  tff(c_11968, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11891, c_8, c_11126, c_11891, c_11890, c_11890, c_11126, c_11890, c_11900])).
% 9.19/3.16  tff(c_28, plain, (![A_20, C_24, B_23]: (k9_relat_1(k7_relat_1(A_20, C_24), B_23)=k9_relat_1(A_20, B_23) | ~r1_tarski(B_23, C_24) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.19/3.16  tff(c_12937, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11968, c_28])).
% 9.19/3.16  tff(c_12944, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_12937])).
% 9.19/3.16  tff(c_30, plain, (![A_25]: (k10_relat_1(A_25, k2_relat_1(A_25))=k1_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.19/3.16  tff(c_12955, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12944, c_30])).
% 9.19/3.16  tff(c_12961, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11891, c_11126, c_12955])).
% 9.19/3.16  tff(c_391, plain, (![A_78, C_79, B_80]: (k3_xboole_0(A_78, k10_relat_1(C_79, B_80))=k10_relat_1(k7_relat_1(C_79, A_78), B_80) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.19/3.16  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.19/3.16  tff(c_397, plain, (![A_78, C_79, B_80]: (k5_xboole_0(A_78, k10_relat_1(k7_relat_1(C_79, A_78), B_80))=k4_xboole_0(A_78, k10_relat_1(C_79, B_80)) | ~v1_relat_1(C_79))), inference(superposition, [status(thm), theory('equality')], [c_391, c_14])).
% 9.19/3.16  tff(c_13092, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12961, c_397])).
% 9.19/3.16  tff(c_13102, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_230, c_13092])).
% 9.19/3.16  tff(c_13104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_13102])).
% 9.19/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.16  
% 9.19/3.16  Inference rules
% 9.19/3.16  ----------------------
% 9.19/3.16  #Ref     : 0
% 9.19/3.16  #Sup     : 2941
% 9.19/3.16  #Fact    : 0
% 9.19/3.16  #Define  : 0
% 9.19/3.16  #Split   : 2
% 9.19/3.16  #Chain   : 0
% 9.19/3.16  #Close   : 0
% 9.19/3.16  
% 9.19/3.16  Ordering : KBO
% 9.19/3.16  
% 9.19/3.16  Simplification rules
% 9.19/3.16  ----------------------
% 9.19/3.16  #Subsume      : 648
% 9.19/3.16  #Demod        : 2641
% 9.19/3.16  #Tautology    : 955
% 9.19/3.16  #SimpNegUnit  : 2
% 9.19/3.16  #BackRed      : 6
% 9.19/3.16  
% 9.19/3.16  #Partial instantiations: 0
% 9.19/3.16  #Strategies tried      : 1
% 9.19/3.16  
% 9.19/3.16  Timing (in seconds)
% 9.19/3.16  ----------------------
% 9.19/3.17  Preprocessing        : 0.39
% 9.19/3.17  Parsing              : 0.22
% 9.19/3.17  CNF conversion       : 0.03
% 9.19/3.17  Main loop            : 1.93
% 9.19/3.17  Inferencing          : 0.55
% 9.19/3.17  Reduction            : 0.70
% 9.19/3.17  Demodulation         : 0.53
% 9.19/3.17  BG Simplification    : 0.07
% 9.19/3.17  Subsumption          : 0.49
% 9.19/3.17  Abstraction          : 0.11
% 9.19/3.17  MUC search           : 0.00
% 9.19/3.17  Cooper               : 0.00
% 9.19/3.17  Total                : 2.36
% 9.19/3.17  Index Insertion      : 0.00
% 9.19/3.17  Index Deletion       : 0.00
% 9.19/3.17  Index Matching       : 0.00
% 9.19/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
