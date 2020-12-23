%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:03 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 195 expanded)
%              Number of leaves         :   41 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  155 ( 306 expanded)
%              Number of equality atoms :   56 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_56,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_83,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_78,plain,(
    ! [A_46] :
      ( v1_relat_1(A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_78])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k5_relat_1(A_30,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [B_23] : k2_zfmisc_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_252,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_76,B_77)),k1_relat_1(A_76))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_257,plain,(
    ! [B_77] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_77)),k1_xboole_0)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_252])).

tff(c_270,plain,(
    ! [B_83] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_83)),k1_xboole_0)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_257])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_180,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_280,plain,(
    ! [B_84] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_84)) = k1_xboole_0
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_270,c_189])).

tff(c_44,plain,(
    ! [A_33] :
      ( k3_xboole_0(A_33,k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_295,plain,(
    ! [B_84] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_84),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_84)))) = k5_relat_1(k1_xboole_0,B_84)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_44])).

tff(c_305,plain,(
    ! [B_85] :
      ( k5_relat_1(k1_xboole_0,B_85) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30,c_295])).

tff(c_309,plain,(
    ! [B_31] :
      ( k5_relat_1(k1_xboole_0,B_31) = k1_xboole_0
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_305])).

tff(c_313,plain,(
    ! [B_86] :
      ( k5_relat_1(k1_xboole_0,B_86) = k1_xboole_0
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_309])).

tff(c_325,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_313])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_325])).

tff(c_333,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_38,plain,(
    ! [A_29] :
      ( v1_relat_1(k4_relat_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_400,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k2_xboole_0(A_94,B_95)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_407,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_400])).

tff(c_32,plain,(
    ! [A_24,B_25] : k6_subset_1(A_24,B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_34,B_36] :
      ( k6_subset_1(k4_relat_1(A_34),k4_relat_1(B_36)) = k4_relat_1(k6_subset_1(A_34,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_741,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(k4_relat_1(A_132),k4_relat_1(B_133)) = k4_relat_1(k4_xboole_0(A_132,B_133))
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_46])).

tff(c_748,plain,(
    ! [B_133] :
      ( k4_relat_1(k4_xboole_0(B_133,B_133)) = k1_xboole_0
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_407])).

tff(c_763,plain,(
    ! [B_133] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_748])).

tff(c_767,plain,(
    ! [B_134] :
      ( ~ v1_relat_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_773,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_82,c_767])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_773])).

tff(c_782,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_512,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_116,B_117)),k1_relat_1(A_116))
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_520,plain,(
    ! [B_117] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_117)),k1_xboole_0)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_512])).

tff(c_547,plain,(
    ! [B_120] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_120)),k1_xboole_0)
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_520])).

tff(c_435,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_444,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_435])).

tff(c_562,plain,(
    ! [B_121] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_121)) = k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_547,c_444])).

tff(c_577,plain,(
    ! [B_121] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_121),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_121)))) = k5_relat_1(k1_xboole_0,B_121)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_44])).

tff(c_601,plain,(
    ! [B_127] :
      ( k5_relat_1(k1_xboole_0,B_127) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_127))
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30,c_577])).

tff(c_605,plain,(
    ! [B_31] :
      ( k5_relat_1(k1_xboole_0,B_31) = k1_xboole_0
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_601])).

tff(c_614,plain,(
    ! [B_128] :
      ( k5_relat_1(k1_xboole_0,B_128) = k1_xboole_0
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_605])).

tff(c_628,plain,(
    ! [A_29] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_29)) = k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_38,c_614])).

tff(c_42,plain,(
    ! [A_32] :
      ( k4_relat_1(k4_relat_1(A_32)) = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_526,plain,(
    ! [B_118,A_119] :
      ( k5_relat_1(k4_relat_1(B_118),k4_relat_1(A_119)) = k4_relat_1(k5_relat_1(A_119,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1412,plain,(
    ! [A_150,A_151] :
      ( k4_relat_1(k5_relat_1(A_150,k4_relat_1(A_151))) = k5_relat_1(A_151,k4_relat_1(A_150))
      | ~ v1_relat_1(k4_relat_1(A_151))
      | ~ v1_relat_1(A_150)
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_526])).

tff(c_1499,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_29))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_1412])).

tff(c_1518,plain,(
    ! [A_152] :
      ( k5_relat_1(A_152,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_152))
      | ~ v1_relat_1(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_782,c_782,c_1499])).

tff(c_1557,plain,(
    ! [A_153] :
      ( k5_relat_1(A_153,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_38,c_1518])).

tff(c_1578,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_1557])).

tff(c_1589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_1578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.58  
% 3.36/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.58  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.36/1.58  
% 3.36/1.58  %Foreground sorts:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Background operators:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Foreground operators:
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.36/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.36/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.58  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.36/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.36/1.58  
% 3.36/1.60  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.36/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.36/1.60  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.36/1.60  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.36/1.60  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.36/1.60  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.36/1.60  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.36/1.60  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.36/1.60  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.60  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.60  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.36/1.60  tff(f_66, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.36/1.60  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.36/1.60  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.36/1.60  tff(f_56, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.36/1.60  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_relat_1)).
% 3.36/1.60  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.36/1.60  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 3.36/1.60  tff(c_56, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.36/1.60  tff(c_83, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 3.36/1.60  tff(c_58, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.36/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.36/1.60  tff(c_78, plain, (![A_46]: (v1_relat_1(A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.60  tff(c_82, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_78])).
% 3.36/1.60  tff(c_40, plain, (![A_30, B_31]: (v1_relat_1(k5_relat_1(A_30, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.60  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.60  tff(c_30, plain, (![B_23]: (k2_zfmisc_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.36/1.60  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.36/1.60  tff(c_252, plain, (![A_76, B_77]: (r1_tarski(k1_relat_1(k5_relat_1(A_76, B_77)), k1_relat_1(A_76)) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.60  tff(c_257, plain, (![B_77]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_77)), k1_xboole_0) | ~v1_relat_1(B_77) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_252])).
% 3.36/1.60  tff(c_270, plain, (![B_83]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_83)), k1_xboole_0) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_257])).
% 3.36/1.60  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.36/1.60  tff(c_180, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.60  tff(c_189, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_180])).
% 3.36/1.60  tff(c_280, plain, (![B_84]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_84))=k1_xboole_0 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_270, c_189])).
% 3.36/1.60  tff(c_44, plain, (![A_33]: (k3_xboole_0(A_33, k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.36/1.60  tff(c_295, plain, (![B_84]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_84), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_84))))=k5_relat_1(k1_xboole_0, B_84) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_84)) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_280, c_44])).
% 3.36/1.60  tff(c_305, plain, (![B_85]: (k5_relat_1(k1_xboole_0, B_85)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_85)) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30, c_295])).
% 3.36/1.60  tff(c_309, plain, (![B_31]: (k5_relat_1(k1_xboole_0, B_31)=k1_xboole_0 | ~v1_relat_1(B_31) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_305])).
% 3.36/1.60  tff(c_313, plain, (![B_86]: (k5_relat_1(k1_xboole_0, B_86)=k1_xboole_0 | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_309])).
% 3.36/1.60  tff(c_325, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_313])).
% 3.36/1.60  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_325])).
% 3.36/1.60  tff(c_333, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.36/1.60  tff(c_38, plain, (![A_29]: (v1_relat_1(k4_relat_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.36/1.60  tff(c_10, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.60  tff(c_400, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k2_xboole_0(A_94, B_95))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.36/1.60  tff(c_407, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_400])).
% 3.36/1.60  tff(c_32, plain, (![A_24, B_25]: (k6_subset_1(A_24, B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.60  tff(c_46, plain, (![A_34, B_36]: (k6_subset_1(k4_relat_1(A_34), k4_relat_1(B_36))=k4_relat_1(k6_subset_1(A_34, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.60  tff(c_741, plain, (![A_132, B_133]: (k4_xboole_0(k4_relat_1(A_132), k4_relat_1(B_133))=k4_relat_1(k4_xboole_0(A_132, B_133)) | ~v1_relat_1(B_133) | ~v1_relat_1(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_46])).
% 3.36/1.60  tff(c_748, plain, (![B_133]: (k4_relat_1(k4_xboole_0(B_133, B_133))=k1_xboole_0 | ~v1_relat_1(B_133) | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_741, c_407])).
% 3.36/1.60  tff(c_763, plain, (![B_133]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_133) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_748])).
% 3.36/1.60  tff(c_767, plain, (![B_134]: (~v1_relat_1(B_134) | ~v1_relat_1(B_134))), inference(splitLeft, [status(thm)], [c_763])).
% 3.36/1.60  tff(c_773, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_767])).
% 3.36/1.60  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_773])).
% 3.36/1.60  tff(c_782, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_763])).
% 3.36/1.60  tff(c_512, plain, (![A_116, B_117]: (r1_tarski(k1_relat_1(k5_relat_1(A_116, B_117)), k1_relat_1(A_116)) | ~v1_relat_1(B_117) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.60  tff(c_520, plain, (![B_117]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_117)), k1_xboole_0) | ~v1_relat_1(B_117) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_512])).
% 3.36/1.60  tff(c_547, plain, (![B_120]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_120)), k1_xboole_0) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_520])).
% 3.36/1.60  tff(c_435, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.60  tff(c_444, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_435])).
% 3.36/1.60  tff(c_562, plain, (![B_121]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_121))=k1_xboole_0 | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_547, c_444])).
% 3.36/1.60  tff(c_577, plain, (![B_121]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_121), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_121))))=k5_relat_1(k1_xboole_0, B_121) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_121)) | ~v1_relat_1(B_121))), inference(superposition, [status(thm), theory('equality')], [c_562, c_44])).
% 3.36/1.60  tff(c_601, plain, (![B_127]: (k5_relat_1(k1_xboole_0, B_127)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_127)) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30, c_577])).
% 3.36/1.60  tff(c_605, plain, (![B_31]: (k5_relat_1(k1_xboole_0, B_31)=k1_xboole_0 | ~v1_relat_1(B_31) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_601])).
% 3.36/1.60  tff(c_614, plain, (![B_128]: (k5_relat_1(k1_xboole_0, B_128)=k1_xboole_0 | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_605])).
% 3.36/1.60  tff(c_628, plain, (![A_29]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_29))=k1_xboole_0 | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_38, c_614])).
% 3.36/1.60  tff(c_42, plain, (![A_32]: (k4_relat_1(k4_relat_1(A_32))=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.36/1.60  tff(c_526, plain, (![B_118, A_119]: (k5_relat_1(k4_relat_1(B_118), k4_relat_1(A_119))=k4_relat_1(k5_relat_1(A_119, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.36/1.60  tff(c_1412, plain, (![A_150, A_151]: (k4_relat_1(k5_relat_1(A_150, k4_relat_1(A_151)))=k5_relat_1(A_151, k4_relat_1(A_150)) | ~v1_relat_1(k4_relat_1(A_151)) | ~v1_relat_1(A_150) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_42, c_526])).
% 3.36/1.60  tff(c_1499, plain, (![A_29]: (k5_relat_1(A_29, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_29)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_628, c_1412])).
% 3.36/1.60  tff(c_1518, plain, (![A_152]: (k5_relat_1(A_152, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_152)) | ~v1_relat_1(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_782, c_782, c_1499])).
% 3.36/1.60  tff(c_1557, plain, (![A_153]: (k5_relat_1(A_153, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_38, c_1518])).
% 3.36/1.60  tff(c_1578, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_1557])).
% 3.36/1.60  tff(c_1589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_1578])).
% 3.36/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.60  
% 3.36/1.60  Inference rules
% 3.36/1.60  ----------------------
% 3.36/1.60  #Ref     : 0
% 3.36/1.60  #Sup     : 368
% 3.36/1.60  #Fact    : 0
% 3.36/1.60  #Define  : 0
% 3.36/1.60  #Split   : 2
% 3.36/1.60  #Chain   : 0
% 3.36/1.60  #Close   : 0
% 3.36/1.60  
% 3.36/1.60  Ordering : KBO
% 3.36/1.60  
% 3.36/1.60  Simplification rules
% 3.36/1.60  ----------------------
% 3.36/1.60  #Subsume      : 27
% 3.36/1.60  #Demod        : 294
% 3.36/1.60  #Tautology    : 192
% 3.36/1.60  #SimpNegUnit  : 2
% 3.36/1.60  #BackRed      : 0
% 3.36/1.60  
% 3.36/1.60  #Partial instantiations: 0
% 3.36/1.60  #Strategies tried      : 1
% 3.36/1.60  
% 3.36/1.60  Timing (in seconds)
% 3.36/1.60  ----------------------
% 3.36/1.60  Preprocessing        : 0.33
% 3.36/1.60  Parsing              : 0.17
% 3.36/1.60  CNF conversion       : 0.02
% 3.36/1.60  Main loop            : 0.44
% 3.36/1.60  Inferencing          : 0.16
% 3.36/1.60  Reduction            : 0.14
% 3.36/1.60  Demodulation         : 0.10
% 3.36/1.60  BG Simplification    : 0.03
% 3.36/1.60  Subsumption          : 0.08
% 3.36/1.60  Abstraction          : 0.03
% 3.36/1.60  MUC search           : 0.00
% 3.36/1.60  Cooper               : 0.00
% 3.36/1.60  Total                : 0.80
% 3.36/1.60  Index Insertion      : 0.00
% 3.36/1.60  Index Deletion       : 0.00
% 3.36/1.60  Index Matching       : 0.00
% 3.36/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
