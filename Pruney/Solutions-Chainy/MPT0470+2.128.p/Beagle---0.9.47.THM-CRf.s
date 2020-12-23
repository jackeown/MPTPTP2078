%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 202 expanded)
%              Number of leaves         :   44 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 330 expanded)
%              Number of equality atoms :   65 ( 142 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_870,plain,(
    ! [A_205,B_206] : k5_xboole_0(A_205,k3_xboole_0(A_205,B_206)) = k4_xboole_0(A_205,B_206) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_882,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_870])).

tff(c_885,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_882])).

tff(c_510,plain,(
    ! [A_147,B_148] : k5_xboole_0(A_147,k3_xboole_0(A_147,B_148)) = k4_xboole_0(A_147,B_148) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_522,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_510])).

tff(c_525,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_522])).

tff(c_62,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_129,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_147,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k1_tarski(A_81),B_82)
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    ! [A_85] :
      ( k1_tarski(A_85) = k1_xboole_0
      | ~ r2_hidden(A_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_147,c_10])).

tff(c_163,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_158])).

tff(c_164,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_50,plain,(
    ! [A_63,B_64] :
      ( v1_relat_1(k5_relat_1(A_63,B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_40] : k2_zfmisc_1(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_373,plain,(
    ! [A_128,B_129] :
      ( k1_relat_1(k5_relat_1(A_128,B_129)) = k1_relat_1(A_128)
      | ~ r1_tarski(k2_relat_1(A_128),k1_relat_1(B_129))
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_379,plain,(
    ! [B_129] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_129)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_129))
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_373])).

tff(c_384,plain,(
    ! [B_130] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_130)) = k1_xboole_0
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_8,c_60,c_379])).

tff(c_52,plain,(
    ! [A_65] :
      ( k3_xboole_0(A_65,k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65))) = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_396,plain,(
    ! [B_130] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_130),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_130)))) = k5_relat_1(k1_xboole_0,B_130)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_130))
      | ~ v1_relat_1(B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_52])).

tff(c_404,plain,(
    ! [B_131] :
      ( k5_relat_1(k1_xboole_0,B_131) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_131))
      | ~ v1_relat_1(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36,c_396])).

tff(c_408,plain,(
    ! [B_64] :
      ( k5_relat_1(k1_xboole_0,B_64) = k1_xboole_0
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_404])).

tff(c_412,plain,(
    ! [B_132] :
      ( k5_relat_1(k1_xboole_0,B_132) = k1_xboole_0
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_408])).

tff(c_421,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_412])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_421])).

tff(c_428,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_464,plain,(
    ! [B_139] : k4_xboole_0(k1_tarski(B_139),k1_tarski(B_139)) != k1_tarski(B_139) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_467,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_464])).

tff(c_471,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_428,c_467])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_471])).

tff(c_530,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_586,plain,(
    ! [A_162,B_163] :
      ( r1_tarski(k1_tarski(A_162),B_163)
      | ~ r2_hidden(A_162,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_596,plain,(
    ! [A_164] :
      ( k1_tarski(A_164) = k1_xboole_0
      | ~ r2_hidden(A_164,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_586,c_10])).

tff(c_601,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_596])).

tff(c_602,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_34,plain,(
    ! [A_39] : k2_zfmisc_1(A_39,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_784,plain,(
    ! [B_199,A_200] :
      ( k2_relat_1(k5_relat_1(B_199,A_200)) = k2_relat_1(A_200)
      | ~ r1_tarski(k1_relat_1(A_200),k2_relat_1(B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_787,plain,(
    ! [B_199] :
      ( k2_relat_1(k5_relat_1(B_199,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_784])).

tff(c_795,plain,(
    ! [B_201] :
      ( k2_relat_1(k5_relat_1(B_201,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_8,c_58,c_787])).

tff(c_807,plain,(
    ! [B_201] :
      ( k3_xboole_0(k5_relat_1(B_201,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_201,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_201,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_201,k1_xboole_0))
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_52])).

tff(c_815,plain,(
    ! [B_202] :
      ( k5_relat_1(B_202,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_202,k1_xboole_0))
      | ~ v1_relat_1(B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34,c_807])).

tff(c_819,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_50,c_815])).

tff(c_823,plain,(
    ! [A_203] :
      ( k5_relat_1(A_203,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_819])).

tff(c_832,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_823])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_832])).

tff(c_839,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_38,plain,(
    ! [B_42] : k4_xboole_0(k1_tarski(B_42),k1_tarski(B_42)) != k1_tarski(B_42) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_845,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_38])).

tff(c_860,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_839,c_845])).

tff(c_889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_860])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:19:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  
% 2.70/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.70/1.35  
% 2.70/1.35  %Foreground sorts:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Background operators:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Foreground operators:
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.70/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.70/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.70/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.70/1.35  
% 2.70/1.37  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.70/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.70/1.37  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.70/1.37  tff(f_118, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.70/1.37  tff(f_80, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.70/1.37  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.70/1.37  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.70/1.37  tff(f_86, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.70/1.37  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.70/1.37  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.70/1.37  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.70/1.37  tff(f_111, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.70/1.37  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.70/1.37  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.70/1.37  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.70/1.37  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.70/1.37  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.37  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.37  tff(c_870, plain, (![A_205, B_206]: (k5_xboole_0(A_205, k3_xboole_0(A_205, B_206))=k4_xboole_0(A_205, B_206))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.37  tff(c_882, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_870])).
% 2.70/1.37  tff(c_885, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_882])).
% 2.70/1.37  tff(c_510, plain, (![A_147, B_148]: (k5_xboole_0(A_147, k3_xboole_0(A_147, B_148))=k4_xboole_0(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.37  tff(c_522, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_510])).
% 2.70/1.37  tff(c_525, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_522])).
% 2.70/1.37  tff(c_62, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.37  tff(c_129, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 2.70/1.37  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.37  tff(c_48, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.37  tff(c_147, plain, (![A_81, B_82]: (r1_tarski(k1_tarski(A_81), B_82) | ~r2_hidden(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.70/1.37  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.37  tff(c_158, plain, (![A_85]: (k1_tarski(A_85)=k1_xboole_0 | ~r2_hidden(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_147, c_10])).
% 2.70/1.37  tff(c_163, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_158])).
% 2.70/1.37  tff(c_164, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_163])).
% 2.70/1.37  tff(c_50, plain, (![A_63, B_64]: (v1_relat_1(k5_relat_1(A_63, B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.37  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.37  tff(c_36, plain, (![B_40]: (k2_zfmisc_1(k1_xboole_0, B_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.37  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.37  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.37  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.37  tff(c_373, plain, (![A_128, B_129]: (k1_relat_1(k5_relat_1(A_128, B_129))=k1_relat_1(A_128) | ~r1_tarski(k2_relat_1(A_128), k1_relat_1(B_129)) | ~v1_relat_1(B_129) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.70/1.37  tff(c_379, plain, (![B_129]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_129))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_129)) | ~v1_relat_1(B_129) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_373])).
% 2.70/1.37  tff(c_384, plain, (![B_130]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_130))=k1_xboole_0 | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_8, c_60, c_379])).
% 2.70/1.37  tff(c_52, plain, (![A_65]: (k3_xboole_0(A_65, k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65)))=A_65 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.37  tff(c_396, plain, (![B_130]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_130), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_130))))=k5_relat_1(k1_xboole_0, B_130) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_130)) | ~v1_relat_1(B_130))), inference(superposition, [status(thm), theory('equality')], [c_384, c_52])).
% 2.70/1.37  tff(c_404, plain, (![B_131]: (k5_relat_1(k1_xboole_0, B_131)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_131)) | ~v1_relat_1(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_36, c_396])).
% 2.70/1.37  tff(c_408, plain, (![B_64]: (k5_relat_1(k1_xboole_0, B_64)=k1_xboole_0 | ~v1_relat_1(B_64) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_404])).
% 2.70/1.37  tff(c_412, plain, (![B_132]: (k5_relat_1(k1_xboole_0, B_132)=k1_xboole_0 | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_408])).
% 2.70/1.37  tff(c_421, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_412])).
% 2.70/1.37  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_421])).
% 2.70/1.37  tff(c_428, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_163])).
% 2.70/1.37  tff(c_464, plain, (![B_139]: (k4_xboole_0(k1_tarski(B_139), k1_tarski(B_139))!=k1_tarski(B_139))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.37  tff(c_467, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_428, c_464])).
% 2.70/1.37  tff(c_471, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_428, c_428, c_467])).
% 2.70/1.37  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_525, c_471])).
% 2.70/1.37  tff(c_530, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 2.70/1.37  tff(c_586, plain, (![A_162, B_163]: (r1_tarski(k1_tarski(A_162), B_163) | ~r2_hidden(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.70/1.37  tff(c_596, plain, (![A_164]: (k1_tarski(A_164)=k1_xboole_0 | ~r2_hidden(A_164, k1_xboole_0))), inference(resolution, [status(thm)], [c_586, c_10])).
% 2.70/1.37  tff(c_601, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_596])).
% 2.70/1.37  tff(c_602, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_601])).
% 2.70/1.37  tff(c_34, plain, (![A_39]: (k2_zfmisc_1(A_39, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.37  tff(c_784, plain, (![B_199, A_200]: (k2_relat_1(k5_relat_1(B_199, A_200))=k2_relat_1(A_200) | ~r1_tarski(k1_relat_1(A_200), k2_relat_1(B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.70/1.37  tff(c_787, plain, (![B_199]: (k2_relat_1(k5_relat_1(B_199, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_784])).
% 2.70/1.37  tff(c_795, plain, (![B_201]: (k2_relat_1(k5_relat_1(B_201, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_8, c_58, c_787])).
% 2.70/1.37  tff(c_807, plain, (![B_201]: (k3_xboole_0(k5_relat_1(B_201, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_201, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_201, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_201, k1_xboole_0)) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_795, c_52])).
% 2.70/1.37  tff(c_815, plain, (![B_202]: (k5_relat_1(B_202, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_202, k1_xboole_0)) | ~v1_relat_1(B_202))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34, c_807])).
% 2.70/1.37  tff(c_819, plain, (![A_63]: (k5_relat_1(A_63, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_50, c_815])).
% 2.70/1.37  tff(c_823, plain, (![A_203]: (k5_relat_1(A_203, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_203))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_819])).
% 2.70/1.37  tff(c_832, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_823])).
% 2.70/1.37  tff(c_838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_832])).
% 2.70/1.37  tff(c_839, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_601])).
% 2.70/1.37  tff(c_38, plain, (![B_42]: (k4_xboole_0(k1_tarski(B_42), k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.37  tff(c_845, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_839, c_38])).
% 2.70/1.37  tff(c_860, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_839, c_839, c_845])).
% 2.70/1.37  tff(c_889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_885, c_860])).
% 2.70/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.37  
% 2.70/1.37  Inference rules
% 2.70/1.37  ----------------------
% 2.70/1.37  #Ref     : 2
% 2.70/1.37  #Sup     : 177
% 2.70/1.37  #Fact    : 0
% 2.70/1.37  #Define  : 0
% 2.70/1.37  #Split   : 3
% 2.70/1.37  #Chain   : 0
% 2.70/1.37  #Close   : 0
% 2.70/1.37  
% 2.70/1.37  Ordering : KBO
% 2.70/1.37  
% 2.70/1.37  Simplification rules
% 2.70/1.37  ----------------------
% 2.70/1.37  #Subsume      : 3
% 2.70/1.37  #Demod        : 81
% 2.70/1.37  #Tautology    : 132
% 2.70/1.37  #SimpNegUnit  : 8
% 2.70/1.37  #BackRed      : 8
% 2.70/1.37  
% 2.70/1.37  #Partial instantiations: 0
% 2.70/1.37  #Strategies tried      : 1
% 2.70/1.37  
% 2.70/1.37  Timing (in seconds)
% 2.70/1.37  ----------------------
% 2.70/1.37  Preprocessing        : 0.33
% 2.70/1.37  Parsing              : 0.18
% 2.70/1.37  CNF conversion       : 0.02
% 2.70/1.37  Main loop            : 0.30
% 2.70/1.37  Inferencing          : 0.12
% 2.70/1.37  Reduction            : 0.09
% 2.70/1.37  Demodulation         : 0.06
% 2.70/1.37  BG Simplification    : 0.02
% 2.70/1.37  Subsumption          : 0.04
% 2.70/1.37  Abstraction          : 0.02
% 2.70/1.37  MUC search           : 0.00
% 2.70/1.37  Cooper               : 0.00
% 2.70/1.37  Total                : 0.67
% 2.70/1.37  Index Insertion      : 0.00
% 2.70/1.37  Index Deletion       : 0.00
% 2.70/1.37  Index Matching       : 0.00
% 2.70/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
