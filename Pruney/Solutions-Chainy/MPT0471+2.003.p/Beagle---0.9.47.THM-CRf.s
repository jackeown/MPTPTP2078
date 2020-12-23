%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:21 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 393 expanded)
%              Number of leaves         :   51 ( 155 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 613 expanded)
%              Number of equality atoms :   47 ( 201 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_42,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_139,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_14,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_86,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_121,plain,(
    k3_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109,c_86])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [A_15] : k4_xboole_0(A_15,'#skF_2') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_22])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_292,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_66,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_3'(A_56),A_56)
      | v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_873,plain,(
    ! [C_156,B_157,A_158] :
      ( r2_hidden(C_156,B_157)
      | ~ r2_hidden(C_156,A_158)
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_915,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_3'(A_163),B_164)
      | ~ r1_tarski(A_163,B_164)
      | v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_66,c_873])).

tff(c_421,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_1'(A_127,B_128),A_127)
      | r1_tarski(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_427,plain,(
    ! [A_129] : r1_tarski(A_129,A_129) ),
    inference(resolution,[status(thm)],[c_421,c_4])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_280,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_2'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_18])).

tff(c_432,plain,(
    ! [A_130] : k4_xboole_0(A_130,A_130) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_427,c_280])).

tff(c_52,plain,(
    ! [C_51,B_50] : ~ r2_hidden(C_51,k4_xboole_0(B_50,k1_tarski(C_51))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_440,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_52])).

tff(c_989,plain,(
    ! [A_167] :
      ( ~ r1_tarski(A_167,'#skF_2')
      | v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_915,c_440])).

tff(c_1001,plain,(
    ! [A_11] :
      ( v1_relat_1(A_11)
      | k4_xboole_0(A_11,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_292,c_989])).

tff(c_1008,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1001])).

tff(c_167,plain,(
    ! [A_92] :
      ( v1_xboole_0(k1_relat_1(A_92))
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_119,plain,(
    ! [A_10] :
      ( A_10 = '#skF_2'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_177,plain,(
    ! [A_94] :
      ( k1_relat_1(A_94) = '#skF_2'
      | ~ v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_167,c_119])).

tff(c_185,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_177])).

tff(c_70,plain,(
    ! [A_75] :
      ( v1_relat_1(k4_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_431,plain,(
    ! [A_129] : k4_xboole_0(A_129,A_129) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_427,c_280])).

tff(c_1422,plain,(
    ! [C_192,A_193,B_194] : k4_xboole_0(k2_zfmisc_1(C_192,A_193),k2_zfmisc_1(C_192,B_194)) = k2_zfmisc_1(C_192,k4_xboole_0(A_193,B_194)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1444,plain,(
    ! [C_192,B_194] : k2_zfmisc_1(C_192,k4_xboole_0(B_194,B_194)) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_431])).

tff(c_1460,plain,(
    ! [C_192] : k2_zfmisc_1(C_192,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_1444])).

tff(c_76,plain,(
    ! [A_78] :
      ( k2_relat_1(k4_relat_1(A_78)) = k1_relat_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_760,plain,(
    ! [A_151] :
      ( r1_tarski(A_151,k2_zfmisc_1(k1_relat_1(A_151),k2_relat_1(A_151)))
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2836,plain,(
    ! [A_274] :
      ( r1_tarski(k4_relat_1(A_274),k2_zfmisc_1(k1_relat_1(k4_relat_1(A_274)),k1_relat_1(A_274)))
      | ~ v1_relat_1(k4_relat_1(A_274))
      | ~ v1_relat_1(A_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_760])).

tff(c_2863,plain,
    ( r1_tarski(k4_relat_1('#skF_2'),k2_zfmisc_1(k1_relat_1(k4_relat_1('#skF_2')),'#skF_2'))
    | ~ v1_relat_1(k4_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_2836])).

tff(c_2871,plain,
    ( r1_tarski(k4_relat_1('#skF_2'),'#skF_2')
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1460,c_2863])).

tff(c_2872,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2871])).

tff(c_2878,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_2872])).

tff(c_2883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2878])).

tff(c_2884,plain,(
    r1_tarski(k4_relat_1('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2871])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_235,plain,(
    ! [A_13,B_14] :
      ( A_13 = '#skF_2'
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_20])).

tff(c_437,plain,(
    ! [A_130] :
      ( A_130 = '#skF_2'
      | ~ r1_tarski(A_130,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_235])).

tff(c_2927,plain,(
    k4_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2884,c_437])).

tff(c_78,plain,(
    ! [A_78] :
      ( k1_relat_1(k4_relat_1(A_78)) = k2_relat_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2966,plain,
    ( k2_relat_1('#skF_2') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2927,c_78])).

tff(c_2996,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_185,c_2966])).

tff(c_142,plain,(
    ! [A_88] :
      ( v1_relat_1(A_88)
      | ~ v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_146,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_521,plain,(
    ! [A_136] :
      ( k2_xboole_0(k1_relat_1(A_136),k2_relat_1(A_136)) = k3_relat_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_539,plain,
    ( k2_xboole_0('#skF_2',k2_relat_1('#skF_2')) = k3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_521])).

tff(c_543,plain,(
    k2_xboole_0('#skF_2',k2_relat_1('#skF_2')) = k3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_539])).

tff(c_3028,plain,(
    k2_xboole_0('#skF_2','#skF_2') = k3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2996,c_543])).

tff(c_3031,plain,(
    k3_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3028])).

tff(c_3033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_3031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.76  
% 4.43/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.77  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.43/1.77  
% 4.43/1.77  %Foreground sorts:
% 4.43/1.77  
% 4.43/1.77  
% 4.43/1.77  %Background operators:
% 4.43/1.77  
% 4.43/1.77  
% 4.43/1.77  %Foreground operators:
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.43/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.43/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.43/1.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.43/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.43/1.77  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.43/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.43/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.43/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.43/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.43/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.43/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.43/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.43/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.43/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.43/1.77  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.43/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.43/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.43/1.77  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.43/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.43/1.77  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.43/1.77  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.43/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.43/1.77  
% 4.51/1.78  tff(f_42, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.51/1.78  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.51/1.78  tff(f_139, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 4.51/1.78  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.51/1.78  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.51/1.78  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.51/1.78  tff(f_102, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 4.51/1.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.51/1.78  tff(f_84, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.51/1.78  tff(f_114, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.51/1.78  tff(f_110, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.51/1.78  tff(f_76, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 4.51/1.78  tff(f_124, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.51/1.78  tff(f_118, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 4.51/1.78  tff(f_50, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.51/1.78  tff(f_92, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.51/1.78  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 4.51/1.78  tff(c_14, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.78  tff(c_105, plain, (![A_85]: (k1_xboole_0=A_85 | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.51/1.78  tff(c_109, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_14, c_105])).
% 4.51/1.78  tff(c_86, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.51/1.78  tff(c_121, plain, (k3_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109, c_86])).
% 4.51/1.78  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.78  tff(c_22, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.51/1.78  tff(c_120, plain, (![A_15]: (k4_xboole_0(A_15, '#skF_2')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_22])).
% 4.51/1.78  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_292, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_16])).
% 4.51/1.78  tff(c_66, plain, (![A_56]: (r2_hidden('#skF_3'(A_56), A_56) | v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.78  tff(c_873, plain, (![C_156, B_157, A_158]: (r2_hidden(C_156, B_157) | ~r2_hidden(C_156, A_158) | ~r1_tarski(A_158, B_157))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.78  tff(c_915, plain, (![A_163, B_164]: (r2_hidden('#skF_3'(A_163), B_164) | ~r1_tarski(A_163, B_164) | v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_66, c_873])).
% 4.51/1.78  tff(c_421, plain, (![A_127, B_128]: (r2_hidden('#skF_1'(A_127, B_128), A_127) | r1_tarski(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.78  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.78  tff(c_427, plain, (![A_129]: (r1_tarski(A_129, A_129))), inference(resolution, [status(thm)], [c_421, c_4])).
% 4.51/1.78  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_280, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_2' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_18])).
% 4.51/1.78  tff(c_432, plain, (![A_130]: (k4_xboole_0(A_130, A_130)='#skF_2')), inference(resolution, [status(thm)], [c_427, c_280])).
% 4.51/1.78  tff(c_52, plain, (![C_51, B_50]: (~r2_hidden(C_51, k4_xboole_0(B_50, k1_tarski(C_51))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.51/1.78  tff(c_440, plain, (![C_51]: (~r2_hidden(C_51, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_52])).
% 4.51/1.78  tff(c_989, plain, (![A_167]: (~r1_tarski(A_167, '#skF_2') | v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_915, c_440])).
% 4.51/1.78  tff(c_1001, plain, (![A_11]: (v1_relat_1(A_11) | k4_xboole_0(A_11, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_292, c_989])).
% 4.51/1.78  tff(c_1008, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_1001])).
% 4.51/1.78  tff(c_167, plain, (![A_92]: (v1_xboole_0(k1_relat_1(A_92)) | ~v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.51/1.78  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.51/1.78  tff(c_119, plain, (![A_10]: (A_10='#skF_2' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_12])).
% 4.51/1.78  tff(c_177, plain, (![A_94]: (k1_relat_1(A_94)='#skF_2' | ~v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_167, c_119])).
% 4.51/1.78  tff(c_185, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_177])).
% 4.51/1.78  tff(c_70, plain, (![A_75]: (v1_relat_1(k4_relat_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.51/1.78  tff(c_431, plain, (![A_129]: (k4_xboole_0(A_129, A_129)='#skF_2')), inference(resolution, [status(thm)], [c_427, c_280])).
% 4.51/1.78  tff(c_1422, plain, (![C_192, A_193, B_194]: (k4_xboole_0(k2_zfmisc_1(C_192, A_193), k2_zfmisc_1(C_192, B_194))=k2_zfmisc_1(C_192, k4_xboole_0(A_193, B_194)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.51/1.78  tff(c_1444, plain, (![C_192, B_194]: (k2_zfmisc_1(C_192, k4_xboole_0(B_194, B_194))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_431])).
% 4.51/1.78  tff(c_1460, plain, (![C_192]: (k2_zfmisc_1(C_192, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_1444])).
% 4.51/1.78  tff(c_76, plain, (![A_78]: (k2_relat_1(k4_relat_1(A_78))=k1_relat_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.51/1.78  tff(c_760, plain, (![A_151]: (r1_tarski(A_151, k2_zfmisc_1(k1_relat_1(A_151), k2_relat_1(A_151))) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.51/1.78  tff(c_2836, plain, (![A_274]: (r1_tarski(k4_relat_1(A_274), k2_zfmisc_1(k1_relat_1(k4_relat_1(A_274)), k1_relat_1(A_274))) | ~v1_relat_1(k4_relat_1(A_274)) | ~v1_relat_1(A_274))), inference(superposition, [status(thm), theory('equality')], [c_76, c_760])).
% 4.51/1.78  tff(c_2863, plain, (r1_tarski(k4_relat_1('#skF_2'), k2_zfmisc_1(k1_relat_1(k4_relat_1('#skF_2')), '#skF_2')) | ~v1_relat_1(k4_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_185, c_2836])).
% 4.51/1.78  tff(c_2871, plain, (r1_tarski(k4_relat_1('#skF_2'), '#skF_2') | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1460, c_2863])).
% 4.51/1.78  tff(c_2872, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2871])).
% 4.51/1.78  tff(c_2878, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_2872])).
% 4.51/1.78  tff(c_2883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2878])).
% 4.51/1.78  tff(c_2884, plain, (r1_tarski(k4_relat_1('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_2871])).
% 4.51/1.78  tff(c_20, plain, (![A_13, B_14]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k4_xboole_0(B_14, A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.78  tff(c_235, plain, (![A_13, B_14]: (A_13='#skF_2' | ~r1_tarski(A_13, k4_xboole_0(B_14, A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_20])).
% 4.51/1.78  tff(c_437, plain, (![A_130]: (A_130='#skF_2' | ~r1_tarski(A_130, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_235])).
% 4.51/1.78  tff(c_2927, plain, (k4_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_2884, c_437])).
% 4.51/1.78  tff(c_78, plain, (![A_78]: (k1_relat_1(k4_relat_1(A_78))=k2_relat_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.51/1.78  tff(c_2966, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2927, c_78])).
% 4.51/1.78  tff(c_2996, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_185, c_2966])).
% 4.51/1.78  tff(c_142, plain, (![A_88]: (v1_relat_1(A_88) | ~v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.51/1.78  tff(c_146, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_142])).
% 4.51/1.78  tff(c_521, plain, (![A_136]: (k2_xboole_0(k1_relat_1(A_136), k2_relat_1(A_136))=k3_relat_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.78  tff(c_539, plain, (k2_xboole_0('#skF_2', k2_relat_1('#skF_2'))=k3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_185, c_521])).
% 4.51/1.78  tff(c_543, plain, (k2_xboole_0('#skF_2', k2_relat_1('#skF_2'))=k3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_539])).
% 4.51/1.78  tff(c_3028, plain, (k2_xboole_0('#skF_2', '#skF_2')=k3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2996, c_543])).
% 4.51/1.78  tff(c_3031, plain, (k3_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3028])).
% 4.51/1.78  tff(c_3033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_3031])).
% 4.51/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.78  
% 4.51/1.78  Inference rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Ref     : 1
% 4.51/1.78  #Sup     : 680
% 4.51/1.78  #Fact    : 0
% 4.51/1.78  #Define  : 0
% 4.51/1.78  #Split   : 1
% 4.51/1.78  #Chain   : 0
% 4.51/1.78  #Close   : 0
% 4.51/1.78  
% 4.51/1.78  Ordering : KBO
% 4.51/1.78  
% 4.51/1.78  Simplification rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Subsume      : 94
% 4.51/1.78  #Demod        : 407
% 4.51/1.78  #Tautology    : 387
% 4.51/1.78  #SimpNegUnit  : 5
% 4.51/1.78  #BackRed      : 8
% 4.51/1.78  
% 4.51/1.78  #Partial instantiations: 0
% 4.51/1.78  #Strategies tried      : 1
% 4.51/1.78  
% 4.51/1.78  Timing (in seconds)
% 4.51/1.78  ----------------------
% 4.51/1.79  Preprocessing        : 0.37
% 4.51/1.79  Parsing              : 0.19
% 4.51/1.79  CNF conversion       : 0.03
% 4.51/1.79  Main loop            : 0.66
% 4.51/1.79  Inferencing          : 0.23
% 4.51/1.79  Reduction            : 0.23
% 4.51/1.79  Demodulation         : 0.17
% 4.51/1.79  BG Simplification    : 0.03
% 4.51/1.79  Subsumption          : 0.12
% 4.51/1.79  Abstraction          : 0.03
% 4.51/1.79  MUC search           : 0.00
% 4.51/1.79  Cooper               : 0.00
% 4.51/1.79  Total                : 1.06
% 4.51/1.79  Index Insertion      : 0.00
% 4.51/1.79  Index Deletion       : 0.00
% 4.51/1.79  Index Matching       : 0.00
% 4.51/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
