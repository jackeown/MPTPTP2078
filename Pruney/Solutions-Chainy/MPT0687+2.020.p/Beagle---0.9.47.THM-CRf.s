%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:35 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 174 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 282 expanded)
%              Number of equality atoms :   71 ( 129 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_145,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_137,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_110,axiom,(
    ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_72,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_115,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_116,plain,(
    ! [A_48] :
      ( k7_relat_1(A_48,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k7_relat_1(A_22,B_23))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_128,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_132,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_128])).

tff(c_60,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    ! [A_35] : k8_relat_1(A_35,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_492,plain,(
    ! [B_93,A_94] :
      ( k3_xboole_0(k2_relat_1(B_93),A_94) = k2_relat_1(k8_relat_1(A_94,B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_509,plain,(
    ! [A_94] :
      ( k2_relat_1(k8_relat_1(A_94,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,A_94)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_492])).

tff(c_513,plain,(
    ! [A_94] : k3_xboole_0(k1_xboole_0,A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_60,c_48,c_509])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_184,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_59,B_60)),A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_193,plain,(
    ! [A_35] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),A_35)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_184])).

tff(c_205,plain,(
    ! [A_63] : r1_tarski(k1_xboole_0,A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_60,c_193])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_209,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(resolution,[status(thm)],[c_205,c_12])).

tff(c_377,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(k2_xboole_0(A_81,B_82),B_82) = A_81
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_404,plain,(
    ! [A_83] :
      ( k4_xboole_0(A_83,A_83) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_377])).

tff(c_408,plain,(
    ! [B_2] :
      ( k4_xboole_0(B_2,B_2) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_404])).

tff(c_517,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_408])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,k1_tarski(B_21)) = A_20
      | r2_hidden(B_21,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_230,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_245,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,k1_tarski(B_21))
      | r2_hidden(B_21,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_230])).

tff(c_1336,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,k1_tarski(B_21)) = k1_xboole_0
      | r2_hidden(B_21,A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_245])).

tff(c_576,plain,(
    ! [B_98,A_99] :
      ( k10_relat_1(B_98,A_99) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_98),A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2017,plain,(
    ! [B_160,B_161] :
      ( k10_relat_1(B_160,B_161) = k1_xboole_0
      | ~ v1_relat_1(B_160)
      | k3_xboole_0(k2_relat_1(B_160),B_161) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_576])).

tff(c_2427,plain,(
    ! [B_174,B_175] :
      ( k10_relat_1(B_174,k1_tarski(B_175)) = k1_xboole_0
      | ~ v1_relat_1(B_174)
      | r2_hidden(B_175,k2_relat_1(B_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_2017])).

tff(c_66,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_163,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_66])).

tff(c_2443,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2427,c_163])).

tff(c_2459,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2443])).

tff(c_2461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_2459])).

tff(c_2463,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2462,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2468,plain,(
    ! [A_176] :
      ( k7_relat_1(A_176,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2476,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_2468])).

tff(c_2480,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2476,c_30])).

tff(c_2484,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2480])).

tff(c_2845,plain,(
    ! [B_221,A_222] :
      ( k3_xboole_0(k2_relat_1(B_221),A_222) = k2_relat_1(k8_relat_1(A_222,B_221))
      | ~ v1_relat_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2862,plain,(
    ! [A_222] :
      ( k2_relat_1(k8_relat_1(A_222,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,A_222)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2845])).

tff(c_2866,plain,(
    ! [A_222] : k3_xboole_0(k1_xboole_0,A_222) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2484,c_60,c_48,c_2862])).

tff(c_2540,plain,(
    ! [A_192,B_193] :
      ( k4_xboole_0(A_192,k1_tarski(B_193)) = A_192
      | r2_hidden(B_193,A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2559,plain,(
    ! [B_193] : r2_hidden(B_193,k1_tarski(B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2540,c_22])).

tff(c_2562,plain,(
    ! [A_195,B_196] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_195,B_196)),A_195)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2571,plain,(
    ! [A_35] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),A_35)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2562])).

tff(c_2582,plain,(
    ! [A_197] : r1_tarski(k1_xboole_0,A_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2484,c_60,c_2571])).

tff(c_2586,plain,(
    ! [A_197] : k2_xboole_0(k1_xboole_0,A_197) = A_197 ),
    inference(resolution,[status(thm)],[c_2582,c_12])).

tff(c_2754,plain,(
    ! [A_211,B_212] :
      ( k4_xboole_0(k2_xboole_0(A_211,B_212),B_212) = A_211
      | ~ r1_xboole_0(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2781,plain,(
    ! [A_213] :
      ( k4_xboole_0(A_213,A_213) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2586,c_2754])).

tff(c_2786,plain,(
    ! [B_214] :
      ( k4_xboole_0(B_214,B_214) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_214) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2781])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( ~ r2_hidden(B_21,A_20)
      | k4_xboole_0(A_20,k1_tarski(B_21)) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2801,plain,(
    ! [B_21] :
      ( ~ r2_hidden(B_21,k1_tarski(B_21))
      | k1_tarski(B_21) != k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_tarski(B_21)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2786,c_26])).

tff(c_2823,plain,(
    ! [B_21] :
      ( k1_tarski(B_21) != k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_tarski(B_21)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2801])).

tff(c_2868,plain,(
    ! [B_21] : k1_tarski(B_21) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2866,c_2823])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(B_15,k1_tarski(A_14)) = k1_tarski(A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2998,plain,(
    ! [B_232,A_233] :
      ( r1_xboole_0(k2_relat_1(B_232),A_233)
      | k10_relat_1(B_232,A_233) != k1_xboole_0
      | ~ v1_relat_1(B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4373,plain,(
    ! [B_292,A_293] :
      ( k3_xboole_0(k2_relat_1(B_292),A_293) = k1_xboole_0
      | k10_relat_1(B_292,A_293) != k1_xboole_0
      | ~ v1_relat_1(B_292) ) ),
    inference(resolution,[status(thm)],[c_2998,c_2])).

tff(c_4466,plain,(
    ! [A_14,B_292] :
      ( k1_tarski(A_14) = k1_xboole_0
      | k10_relat_1(B_292,k1_tarski(A_14)) != k1_xboole_0
      | ~ v1_relat_1(B_292)
      | ~ r2_hidden(A_14,k2_relat_1(B_292)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4373])).

tff(c_4662,plain,(
    ! [B_301,A_302] :
      ( k10_relat_1(B_301,k1_tarski(A_302)) != k1_xboole_0
      | ~ v1_relat_1(B_301)
      | ~ r2_hidden(A_302,k2_relat_1(B_301)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2868,c_4466])).

tff(c_4679,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2462,c_4662])).

tff(c_4689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2463,c_4679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:02:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.94  
% 4.90/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.90/1.94  
% 4.90/1.94  %Foreground sorts:
% 4.90/1.94  
% 4.90/1.94  
% 4.90/1.94  %Background operators:
% 4.90/1.94  
% 4.90/1.94  
% 4.90/1.94  %Foreground operators:
% 4.90/1.94  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.90/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.90/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.90/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.90/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.90/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.90/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.90/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.90/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.90/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.90/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.90/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.90/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.90/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.90/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.90/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.90/1.94  
% 4.90/1.96  tff(f_145, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 4.90/1.96  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 4.90/1.96  tff(f_80, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.90/1.96  tff(f_137, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.90/1.96  tff(f_110, axiom, (![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 4.90/1.96  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 4.90/1.96  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.90/1.96  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 4.90/1.96  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.90/1.96  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.90/1.96  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.90/1.96  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.90/1.96  tff(f_124, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 4.90/1.96  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.90/1.96  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 4.90/1.96  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.90/1.96  tff(c_72, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.90/1.96  tff(c_115, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 4.90/1.96  tff(c_116, plain, (![A_48]: (k7_relat_1(A_48, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.90/1.96  tff(c_124, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_116])).
% 4.90/1.96  tff(c_30, plain, (![A_22, B_23]: (v1_relat_1(k7_relat_1(A_22, B_23)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.90/1.96  tff(c_128, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_30])).
% 4.90/1.96  tff(c_132, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_128])).
% 4.90/1.96  tff(c_60, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.90/1.96  tff(c_48, plain, (![A_35]: (k8_relat_1(A_35, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.90/1.96  tff(c_492, plain, (![B_93, A_94]: (k3_xboole_0(k2_relat_1(B_93), A_94)=k2_relat_1(k8_relat_1(A_94, B_93)) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.90/1.96  tff(c_509, plain, (![A_94]: (k2_relat_1(k8_relat_1(A_94, k1_xboole_0))=k3_xboole_0(k1_xboole_0, A_94) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_492])).
% 4.90/1.96  tff(c_513, plain, (![A_94]: (k3_xboole_0(k1_xboole_0, A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_60, c_48, c_509])).
% 4.90/1.96  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.90/1.96  tff(c_184, plain, (![A_59, B_60]: (r1_tarski(k2_relat_1(k8_relat_1(A_59, B_60)), A_59) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.90/1.96  tff(c_193, plain, (![A_35]: (r1_tarski(k2_relat_1(k1_xboole_0), A_35) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_184])).
% 4.90/1.96  tff(c_205, plain, (![A_63]: (r1_tarski(k1_xboole_0, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_60, c_193])).
% 4.90/1.96  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.90/1.96  tff(c_209, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(resolution, [status(thm)], [c_205, c_12])).
% 4.90/1.96  tff(c_377, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), B_82)=A_81 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.96  tff(c_404, plain, (![A_83]: (k4_xboole_0(A_83, A_83)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_83))), inference(superposition, [status(thm), theory('equality')], [c_209, c_377])).
% 4.90/1.96  tff(c_408, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_404])).
% 4.90/1.96  tff(c_517, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_513, c_408])).
% 4.90/1.96  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k1_tarski(B_21))=A_20 | r2_hidden(B_21, A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.90/1.96  tff(c_230, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.90/1.96  tff(c_245, plain, (![A_20, B_21]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, k1_tarski(B_21)) | r2_hidden(B_21, A_20))), inference(superposition, [status(thm), theory('equality')], [c_28, c_230])).
% 4.90/1.96  tff(c_1336, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k1_tarski(B_21))=k1_xboole_0 | r2_hidden(B_21, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_245])).
% 4.90/1.96  tff(c_576, plain, (![B_98, A_99]: (k10_relat_1(B_98, A_99)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_98), A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.90/1.96  tff(c_2017, plain, (![B_160, B_161]: (k10_relat_1(B_160, B_161)=k1_xboole_0 | ~v1_relat_1(B_160) | k3_xboole_0(k2_relat_1(B_160), B_161)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_576])).
% 4.90/1.96  tff(c_2427, plain, (![B_174, B_175]: (k10_relat_1(B_174, k1_tarski(B_175))=k1_xboole_0 | ~v1_relat_1(B_174) | r2_hidden(B_175, k2_relat_1(B_174)))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_2017])).
% 4.90/1.96  tff(c_66, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.90/1.96  tff(c_163, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_115, c_66])).
% 4.90/1.96  tff(c_2443, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2427, c_163])).
% 4.90/1.96  tff(c_2459, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2443])).
% 4.90/1.96  tff(c_2461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_2459])).
% 4.90/1.96  tff(c_2463, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 4.90/1.96  tff(c_2462, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 4.90/1.96  tff(c_2468, plain, (![A_176]: (k7_relat_1(A_176, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.90/1.96  tff(c_2476, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_2468])).
% 4.90/1.96  tff(c_2480, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2476, c_30])).
% 4.90/1.96  tff(c_2484, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2480])).
% 4.90/1.96  tff(c_2845, plain, (![B_221, A_222]: (k3_xboole_0(k2_relat_1(B_221), A_222)=k2_relat_1(k8_relat_1(A_222, B_221)) | ~v1_relat_1(B_221))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.90/1.96  tff(c_2862, plain, (![A_222]: (k2_relat_1(k8_relat_1(A_222, k1_xboole_0))=k3_xboole_0(k1_xboole_0, A_222) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_2845])).
% 4.90/1.96  tff(c_2866, plain, (![A_222]: (k3_xboole_0(k1_xboole_0, A_222)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2484, c_60, c_48, c_2862])).
% 4.90/1.96  tff(c_2540, plain, (![A_192, B_193]: (k4_xboole_0(A_192, k1_tarski(B_193))=A_192 | r2_hidden(B_193, A_192))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.90/1.96  tff(c_22, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.90/1.96  tff(c_2559, plain, (![B_193]: (r2_hidden(B_193, k1_tarski(B_193)))), inference(superposition, [status(thm), theory('equality')], [c_2540, c_22])).
% 4.90/1.96  tff(c_2562, plain, (![A_195, B_196]: (r1_tarski(k2_relat_1(k8_relat_1(A_195, B_196)), A_195) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.90/1.96  tff(c_2571, plain, (![A_35]: (r1_tarski(k2_relat_1(k1_xboole_0), A_35) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2562])).
% 4.90/1.96  tff(c_2582, plain, (![A_197]: (r1_tarski(k1_xboole_0, A_197))), inference(demodulation, [status(thm), theory('equality')], [c_2484, c_60, c_2571])).
% 4.90/1.96  tff(c_2586, plain, (![A_197]: (k2_xboole_0(k1_xboole_0, A_197)=A_197)), inference(resolution, [status(thm)], [c_2582, c_12])).
% 4.90/1.96  tff(c_2754, plain, (![A_211, B_212]: (k4_xboole_0(k2_xboole_0(A_211, B_212), B_212)=A_211 | ~r1_xboole_0(A_211, B_212))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.90/1.96  tff(c_2781, plain, (![A_213]: (k4_xboole_0(A_213, A_213)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_213))), inference(superposition, [status(thm), theory('equality')], [c_2586, c_2754])).
% 4.90/1.96  tff(c_2786, plain, (![B_214]: (k4_xboole_0(B_214, B_214)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_214)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2781])).
% 4.90/1.96  tff(c_26, plain, (![B_21, A_20]: (~r2_hidden(B_21, A_20) | k4_xboole_0(A_20, k1_tarski(B_21))!=A_20)), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.90/1.96  tff(c_2801, plain, (![B_21]: (~r2_hidden(B_21, k1_tarski(B_21)) | k1_tarski(B_21)!=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_tarski(B_21))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2786, c_26])).
% 4.90/1.96  tff(c_2823, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_tarski(B_21))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2801])).
% 4.90/1.96  tff(c_2868, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2866, c_2823])).
% 4.90/1.96  tff(c_18, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k1_tarski(A_14))=k1_tarski(A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.90/1.96  tff(c_2998, plain, (![B_232, A_233]: (r1_xboole_0(k2_relat_1(B_232), A_233) | k10_relat_1(B_232, A_233)!=k1_xboole_0 | ~v1_relat_1(B_232))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.90/1.96  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.90/1.96  tff(c_4373, plain, (![B_292, A_293]: (k3_xboole_0(k2_relat_1(B_292), A_293)=k1_xboole_0 | k10_relat_1(B_292, A_293)!=k1_xboole_0 | ~v1_relat_1(B_292))), inference(resolution, [status(thm)], [c_2998, c_2])).
% 4.90/1.96  tff(c_4466, plain, (![A_14, B_292]: (k1_tarski(A_14)=k1_xboole_0 | k10_relat_1(B_292, k1_tarski(A_14))!=k1_xboole_0 | ~v1_relat_1(B_292) | ~r2_hidden(A_14, k2_relat_1(B_292)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4373])).
% 4.90/1.96  tff(c_4662, plain, (![B_301, A_302]: (k10_relat_1(B_301, k1_tarski(A_302))!=k1_xboole_0 | ~v1_relat_1(B_301) | ~r2_hidden(A_302, k2_relat_1(B_301)))), inference(negUnitSimplification, [status(thm)], [c_2868, c_4466])).
% 4.90/1.96  tff(c_4679, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2462, c_4662])).
% 4.90/1.96  tff(c_4689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2463, c_4679])).
% 4.90/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.96  
% 4.90/1.96  Inference rules
% 4.90/1.96  ----------------------
% 4.90/1.96  #Ref     : 0
% 4.90/1.96  #Sup     : 1012
% 4.90/1.96  #Fact    : 0
% 4.90/1.96  #Define  : 0
% 4.90/1.96  #Split   : 2
% 4.90/1.96  #Chain   : 0
% 4.90/1.96  #Close   : 0
% 4.90/1.96  
% 4.90/1.96  Ordering : KBO
% 4.90/1.96  
% 4.90/1.96  Simplification rules
% 4.90/1.96  ----------------------
% 4.90/1.96  #Subsume      : 88
% 4.90/1.96  #Demod        : 652
% 4.90/1.96  #Tautology    : 599
% 4.90/1.96  #SimpNegUnit  : 98
% 4.90/1.96  #BackRed      : 8
% 4.90/1.96  
% 4.90/1.96  #Partial instantiations: 0
% 4.90/1.96  #Strategies tried      : 1
% 4.90/1.96  
% 4.90/1.96  Timing (in seconds)
% 4.90/1.96  ----------------------
% 4.90/1.97  Preprocessing        : 0.34
% 4.90/1.97  Parsing              : 0.18
% 4.90/1.97  CNF conversion       : 0.02
% 4.90/1.97  Main loop            : 0.85
% 4.90/1.97  Inferencing          : 0.31
% 4.90/1.97  Reduction            : 0.29
% 4.90/1.97  Demodulation         : 0.20
% 4.90/1.97  BG Simplification    : 0.04
% 4.90/1.97  Subsumption          : 0.15
% 4.90/1.97  Abstraction          : 0.04
% 4.90/1.97  MUC search           : 0.00
% 4.90/1.97  Cooper               : 0.00
% 4.90/1.97  Total                : 1.23
% 4.90/1.97  Index Insertion      : 0.00
% 4.90/1.97  Index Deletion       : 0.00
% 4.90/1.97  Index Matching       : 0.00
% 4.90/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
