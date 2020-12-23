%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 48.79s
% Output     : CNFRefutation 48.89s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 274 expanded)
%              Number of leaves         :   43 ( 112 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 534 expanded)
%              Number of equality atoms :   33 (  92 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_307,plain,(
    ! [A_109,B_110] :
      ( ~ r2_hidden('#skF_1'(A_109,B_110),B_110)
      | r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_312,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_307])).

tff(c_70,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_531,plain,(
    ! [C_128,B_129,A_130] :
      ( r2_hidden(C_128,B_129)
      | ~ r2_hidden(C_128,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1326,plain,(
    ! [A_172,B_173,B_174] :
      ( r2_hidden('#skF_1'(A_172,B_173),B_174)
      | ~ r1_tarski(A_172,B_174)
      | r1_tarski(A_172,B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_531])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21346,plain,(
    ! [A_750,B_751,B_752,B_753] :
      ( r2_hidden('#skF_1'(A_750,B_751),B_752)
      | ~ r1_tarski(B_753,B_752)
      | ~ r1_tarski(A_750,B_753)
      | r1_tarski(A_750,B_751) ) ),
    inference(resolution,[status(thm)],[c_1326,c_2])).

tff(c_22295,plain,(
    ! [A_760,B_761] :
      ( r2_hidden('#skF_1'(A_760,B_761),k2_relat_1('#skF_5'))
      | ~ r1_tarski(A_760,'#skF_4')
      | r1_tarski(A_760,B_761) ) ),
    inference(resolution,[status(thm)],[c_70,c_21346])).

tff(c_22314,plain,(
    ! [A_760,B_761,B_2] :
      ( r2_hidden('#skF_1'(A_760,B_761),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_2)
      | ~ r1_tarski(A_760,'#skF_4')
      | r1_tarski(A_760,B_761) ) ),
    inference(resolution,[status(thm)],[c_22295,c_2])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    ! [A_58] :
      ( k9_relat_1(A_58,k1_relat_1(A_58)) = k2_relat_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [A_46] : k2_zfmisc_1(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,(
    ! [A_72,B_73] : ~ r2_hidden(A_72,k2_zfmisc_1(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_120,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_117])).

tff(c_68,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden(k4_tarski('#skF_2'(A_52,B_53,C_54),A_52),C_54)
      | ~ r2_hidden(A_52,k9_relat_1(C_54,B_53))
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3684,plain,(
    ! [A_299,C_300,B_301,D_302] :
      ( r2_hidden(A_299,k10_relat_1(C_300,B_301))
      | ~ r2_hidden(D_302,B_301)
      | ~ r2_hidden(k4_tarski(A_299,D_302),C_300)
      | ~ r2_hidden(D_302,k2_relat_1(C_300))
      | ~ v1_relat_1(C_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7690,plain,(
    ! [A_448,C_449,A_450,B_451] :
      ( r2_hidden(A_448,k10_relat_1(C_449,A_450))
      | ~ r2_hidden(k4_tarski(A_448,'#skF_1'(A_450,B_451)),C_449)
      | ~ r2_hidden('#skF_1'(A_450,B_451),k2_relat_1(C_449))
      | ~ v1_relat_1(C_449)
      | r1_tarski(A_450,B_451) ) ),
    inference(resolution,[status(thm)],[c_6,c_3684])).

tff(c_102104,plain,(
    ! [A_1653,B_1654,B_1655,C_1656] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1653,B_1654),B_1655,C_1656),k10_relat_1(C_1656,A_1653))
      | ~ r2_hidden('#skF_1'(A_1653,B_1654),k2_relat_1(C_1656))
      | r1_tarski(A_1653,B_1654)
      | ~ r2_hidden('#skF_1'(A_1653,B_1654),k9_relat_1(C_1656,B_1655))
      | ~ v1_relat_1(C_1656) ) ),
    inference(resolution,[status(thm)],[c_50,c_7690])).

tff(c_102158,plain,(
    ! [B_1654,B_1655] :
      ( r2_hidden('#skF_2'('#skF_1'('#skF_4',B_1654),B_1655,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_4',B_1654),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_1654)
      | ~ r2_hidden('#skF_1'('#skF_4',B_1654),k9_relat_1('#skF_5',B_1655))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_102104])).

tff(c_102180,plain,(
    ! [B_1654,B_1655] :
      ( r2_hidden('#skF_2'('#skF_1'('#skF_4',B_1654),B_1655,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_4',B_1654),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_1654)
      | ~ r2_hidden('#skF_1'('#skF_4',B_1654),k9_relat_1('#skF_5',B_1655)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102158])).

tff(c_248256,plain,(
    ! [B_3056,B_3057] :
      ( ~ r2_hidden('#skF_1'('#skF_4',B_3056),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_3056)
      | ~ r2_hidden('#skF_1'('#skF_4',B_3056),k9_relat_1('#skF_5',B_3057)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_102180])).

tff(c_248326,plain,(
    ! [B_3056] :
      ( ~ r2_hidden('#skF_1'('#skF_4',B_3056),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_3056)
      | ~ r2_hidden('#skF_1'('#skF_4',B_3056),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_248256])).

tff(c_248345,plain,(
    ! [B_3058] :
      ( r1_tarski('#skF_4',B_3058)
      | ~ r2_hidden('#skF_1'('#skF_4',B_3058),k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_248326])).

tff(c_248349,plain,(
    ! [B_761] :
      ( ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | r1_tarski('#skF_4',B_761) ) ),
    inference(resolution,[status(thm)],[c_22314,c_248345])).

tff(c_248360,plain,(
    ! [B_761] : r1_tarski('#skF_4',B_761) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_312,c_248349])).

tff(c_313,plain,(
    ! [A_111] : r1_tarski(A_111,A_111) ),
    inference(resolution,[status(thm)],[c_6,c_307])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(A_10,B_11)
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_413,plain,(
    ! [B_118,C_119] : r1_tarski(k4_xboole_0(B_118,C_119),B_118) ),
    inference(resolution,[status(thm)],[c_313,c_14])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_463,plain,(
    ! [B_122,C_123,C_124] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_122,C_123),C_124),C_123) ),
    inference(resolution,[status(thm)],[c_413,c_12])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_483,plain,(
    ! [B_122,C_123,C_124] : k4_xboole_0(k4_xboole_0(k4_xboole_0(B_122,C_123),C_124),C_123) = k4_xboole_0(k4_xboole_0(B_122,C_123),C_124) ),
    inference(resolution,[status(thm)],[c_463,c_16])).

tff(c_54094,plain,(
    ! [B_1253,C_1254,C_1255] : k4_xboole_0(k4_xboole_0(k4_xboole_0(B_1253,C_1254),C_1255),C_1254) = k4_xboole_0(k4_xboole_0(B_1253,C_1254),C_1255) ),
    inference(resolution,[status(thm)],[c_463,c_16])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_443,plain,(
    ! [B_11,C_12,C_119] : r1_tarski(k4_xboole_0(k4_xboole_0(B_11,C_12),C_119),B_11) ),
    inference(resolution,[status(thm)],[c_413,c_14])).

tff(c_149,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_xboole_0(A_83,k4_xboole_0(C_84,B_85))
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_616,plain,(
    ! [A_136,C_137,B_138] :
      ( k4_xboole_0(A_136,k4_xboole_0(C_137,B_138)) = A_136
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(resolution,[status(thm)],[c_149,c_16])).

tff(c_4317,plain,(
    ! [A_321,C_322,B_323,A_324] :
      ( r1_xboole_0(A_321,k4_xboole_0(C_322,B_323))
      | ~ r1_tarski(A_321,A_324)
      | ~ r1_tarski(A_324,B_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_12])).

tff(c_4349,plain,(
    ! [C_325,B_326] :
      ( r1_xboole_0('#skF_4',k4_xboole_0(C_325,B_326))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_326) ) ),
    inference(resolution,[status(thm)],[c_70,c_4317])).

tff(c_4414,plain,(
    ! [C_327,B_328] :
      ( k4_xboole_0('#skF_4',k4_xboole_0(C_327,B_328)) = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_328) ) ),
    inference(resolution,[status(thm)],[c_4349,c_16])).

tff(c_4418,plain,(
    ! [C_327] : k4_xboole_0('#skF_4',k4_xboole_0(C_327,k2_relat_1('#skF_5'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_312,c_4414])).

tff(c_20,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1355,plain,(
    ! [A_178,A_179,C_180,B_181] :
      ( r1_xboole_0(A_178,A_179)
      | ~ r1_tarski(A_178,k4_xboole_0(C_180,B_181))
      | ~ r1_tarski(A_179,B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_20])).

tff(c_1391,plain,(
    ! [C_182,B_183,A_184] :
      ( r1_xboole_0(k4_xboole_0(C_182,B_183),A_184)
      | ~ r1_tarski(A_184,B_183) ) ),
    inference(resolution,[status(thm)],[c_312,c_1355])).

tff(c_12151,plain,(
    ! [C_597,B_598,A_599] :
      ( k4_xboole_0(k4_xboole_0(C_597,B_598),A_599) = k4_xboole_0(C_597,B_598)
      | ~ r1_tarski(A_599,B_598) ) ),
    inference(resolution,[status(thm)],[c_1391,c_16])).

tff(c_12503,plain,(
    ! [C_327,A_599] :
      ( k4_xboole_0('#skF_4',k4_xboole_0(C_327,k2_relat_1('#skF_5'))) = k4_xboole_0('#skF_4',A_599)
      | ~ r1_tarski(A_599,k4_xboole_0(C_327,k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4418,c_12151])).

tff(c_14325,plain,(
    ! [A_621,C_622] :
      ( k4_xboole_0('#skF_4',A_621) = '#skF_4'
      | ~ r1_tarski(A_621,k4_xboole_0(C_622,k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_12503])).

tff(c_14489,plain,(
    ! [C_622,C_12,C_119] : k4_xboole_0('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(C_622,k2_relat_1('#skF_5')),C_12),C_119)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_443,c_14325])).

tff(c_32133,plain,(
    ! [C_903,C_904,C_905] : k4_xboole_0('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903,k2_relat_1('#skF_5')),C_904),C_905)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_443,c_14325])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_164,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_155])).

tff(c_167,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_164])).

tff(c_660,plain,(
    ! [C_137,B_138] :
      ( k4_xboole_0(C_137,B_138) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_137,B_138),B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_167])).

tff(c_32289,plain,(
    ! [C_903,C_904,C_905] :
      ( k4_xboole_0('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903,k2_relat_1('#skF_5')),C_904),C_905)) = k1_xboole_0
      | ~ r1_tarski('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903,k2_relat_1('#skF_5')),C_904),C_905)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32133,c_660])).

tff(c_32657,plain,(
    ! [C_903,C_904,C_905] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r1_tarski('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903,k2_relat_1('#skF_5')),C_904),C_905)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14489,c_32289])).

tff(c_32658,plain,(
    ! [C_903,C_904,C_905] : ~ r1_tarski('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903,k2_relat_1('#skF_5')),C_904),C_905)) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_32657])).

tff(c_55356,plain,(
    ! [B_1256,C_1257,C_1258,C_1259] : ~ r1_tarski('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(B_1256,k2_relat_1('#skF_5')),C_1257),C_1258),C_1259)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54094,c_32658])).

tff(c_55360,plain,(
    ! [C_1258,B_122,C_1259,C_1257,C_124] : ~ r1_tarski('#skF_4',k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(B_122,k2_relat_1('#skF_5')),C_124),C_1257),C_1258),C_1259)) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_55356])).

tff(c_248459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248360,c_55360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.79/39.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.89/39.10  
% 48.89/39.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.89/39.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 48.89/39.10  
% 48.89/39.10  %Foreground sorts:
% 48.89/39.10  
% 48.89/39.10  
% 48.89/39.10  %Background operators:
% 48.89/39.10  
% 48.89/39.10  
% 48.89/39.10  %Foreground operators:
% 48.89/39.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.89/39.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.89/39.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 48.89/39.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 48.89/39.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.89/39.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 48.89/39.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 48.89/39.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.89/39.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 48.89/39.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.89/39.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 48.89/39.10  tff('#skF_5', type, '#skF_5': $i).
% 48.89/39.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 48.89/39.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 48.89/39.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 48.89/39.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 48.89/39.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 48.89/39.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 48.89/39.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.89/39.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 48.89/39.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.89/39.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.89/39.10  tff('#skF_4', type, '#skF_4': $i).
% 48.89/39.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 48.89/39.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.89/39.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 48.89/39.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 48.89/39.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 48.89/39.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.89/39.10  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 48.89/39.10  
% 48.89/39.12  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 48.89/39.12  tff(f_120, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 48.89/39.12  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 48.89/39.12  tff(f_70, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 48.89/39.12  tff(f_73, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 48.89/39.12  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 48.89/39.12  tff(f_101, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 48.89/39.12  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 48.89/39.12  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 48.89/39.12  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 48.89/39.12  tff(f_52, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 48.89/39.12  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 48.89/39.12  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 48.89/39.12  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.89/39.12  tff(c_307, plain, (![A_109, B_110]: (~r2_hidden('#skF_1'(A_109, B_110), B_110) | r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.89/39.12  tff(c_312, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_307])).
% 48.89/39.12  tff(c_70, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 48.89/39.12  tff(c_531, plain, (![C_128, B_129, A_130]: (r2_hidden(C_128, B_129) | ~r2_hidden(C_128, A_130) | ~r1_tarski(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.89/39.12  tff(c_1326, plain, (![A_172, B_173, B_174]: (r2_hidden('#skF_1'(A_172, B_173), B_174) | ~r1_tarski(A_172, B_174) | r1_tarski(A_172, B_173))), inference(resolution, [status(thm)], [c_6, c_531])).
% 48.89/39.12  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.89/39.12  tff(c_21346, plain, (![A_750, B_751, B_752, B_753]: (r2_hidden('#skF_1'(A_750, B_751), B_752) | ~r1_tarski(B_753, B_752) | ~r1_tarski(A_750, B_753) | r1_tarski(A_750, B_751))), inference(resolution, [status(thm)], [c_1326, c_2])).
% 48.89/39.12  tff(c_22295, plain, (![A_760, B_761]: (r2_hidden('#skF_1'(A_760, B_761), k2_relat_1('#skF_5')) | ~r1_tarski(A_760, '#skF_4') | r1_tarski(A_760, B_761))), inference(resolution, [status(thm)], [c_70, c_21346])).
% 48.89/39.12  tff(c_22314, plain, (![A_760, B_761, B_2]: (r2_hidden('#skF_1'(A_760, B_761), B_2) | ~r1_tarski(k2_relat_1('#skF_5'), B_2) | ~r1_tarski(A_760, '#skF_4') | r1_tarski(A_760, B_761))), inference(resolution, [status(thm)], [c_22295, c_2])).
% 48.89/39.12  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 48.89/39.12  tff(c_54, plain, (![A_58]: (k9_relat_1(A_58, k1_relat_1(A_58))=k2_relat_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_90])).
% 48.89/39.12  tff(c_38, plain, (![A_46]: (k2_zfmisc_1(A_46, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 48.89/39.12  tff(c_117, plain, (![A_72, B_73]: (~r2_hidden(A_72, k2_zfmisc_1(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 48.89/39.12  tff(c_120, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_117])).
% 48.89/39.12  tff(c_68, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 48.89/39.12  tff(c_50, plain, (![A_52, B_53, C_54]: (r2_hidden(k4_tarski('#skF_2'(A_52, B_53, C_54), A_52), C_54) | ~r2_hidden(A_52, k9_relat_1(C_54, B_53)) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 48.89/39.12  tff(c_3684, plain, (![A_299, C_300, B_301, D_302]: (r2_hidden(A_299, k10_relat_1(C_300, B_301)) | ~r2_hidden(D_302, B_301) | ~r2_hidden(k4_tarski(A_299, D_302), C_300) | ~r2_hidden(D_302, k2_relat_1(C_300)) | ~v1_relat_1(C_300))), inference(cnfTransformation, [status(thm)], [f_101])).
% 48.89/39.12  tff(c_7690, plain, (![A_448, C_449, A_450, B_451]: (r2_hidden(A_448, k10_relat_1(C_449, A_450)) | ~r2_hidden(k4_tarski(A_448, '#skF_1'(A_450, B_451)), C_449) | ~r2_hidden('#skF_1'(A_450, B_451), k2_relat_1(C_449)) | ~v1_relat_1(C_449) | r1_tarski(A_450, B_451))), inference(resolution, [status(thm)], [c_6, c_3684])).
% 48.89/39.12  tff(c_102104, plain, (![A_1653, B_1654, B_1655, C_1656]: (r2_hidden('#skF_2'('#skF_1'(A_1653, B_1654), B_1655, C_1656), k10_relat_1(C_1656, A_1653)) | ~r2_hidden('#skF_1'(A_1653, B_1654), k2_relat_1(C_1656)) | r1_tarski(A_1653, B_1654) | ~r2_hidden('#skF_1'(A_1653, B_1654), k9_relat_1(C_1656, B_1655)) | ~v1_relat_1(C_1656))), inference(resolution, [status(thm)], [c_50, c_7690])).
% 48.89/39.12  tff(c_102158, plain, (![B_1654, B_1655]: (r2_hidden('#skF_2'('#skF_1'('#skF_4', B_1654), B_1655, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_4', B_1654), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_1654) | ~r2_hidden('#skF_1'('#skF_4', B_1654), k9_relat_1('#skF_5', B_1655)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_102104])).
% 48.89/39.12  tff(c_102180, plain, (![B_1654, B_1655]: (r2_hidden('#skF_2'('#skF_1'('#skF_4', B_1654), B_1655, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_4', B_1654), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_1654) | ~r2_hidden('#skF_1'('#skF_4', B_1654), k9_relat_1('#skF_5', B_1655)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102158])).
% 48.89/39.12  tff(c_248256, plain, (![B_3056, B_3057]: (~r2_hidden('#skF_1'('#skF_4', B_3056), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_3056) | ~r2_hidden('#skF_1'('#skF_4', B_3056), k9_relat_1('#skF_5', B_3057)))), inference(negUnitSimplification, [status(thm)], [c_120, c_102180])).
% 48.89/39.12  tff(c_248326, plain, (![B_3056]: (~r2_hidden('#skF_1'('#skF_4', B_3056), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_3056) | ~r2_hidden('#skF_1'('#skF_4', B_3056), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_248256])).
% 48.89/39.12  tff(c_248345, plain, (![B_3058]: (r1_tarski('#skF_4', B_3058) | ~r2_hidden('#skF_1'('#skF_4', B_3058), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_248326])).
% 48.89/39.12  tff(c_248349, plain, (![B_761]: (~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', B_761))), inference(resolution, [status(thm)], [c_22314, c_248345])).
% 48.89/39.12  tff(c_248360, plain, (![B_761]: (r1_tarski('#skF_4', B_761))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_312, c_248349])).
% 48.89/39.12  tff(c_313, plain, (![A_111]: (r1_tarski(A_111, A_111))), inference(resolution, [status(thm)], [c_6, c_307])).
% 48.89/39.12  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(A_10, B_11) | ~r1_tarski(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 48.89/39.12  tff(c_413, plain, (![B_118, C_119]: (r1_tarski(k4_xboole_0(B_118, C_119), B_118))), inference(resolution, [status(thm)], [c_313, c_14])).
% 48.89/39.12  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_tarski(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 48.89/39.12  tff(c_463, plain, (![B_122, C_123, C_124]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_122, C_123), C_124), C_123))), inference(resolution, [status(thm)], [c_413, c_12])).
% 48.89/39.12  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 48.89/39.12  tff(c_483, plain, (![B_122, C_123, C_124]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(B_122, C_123), C_124), C_123)=k4_xboole_0(k4_xboole_0(B_122, C_123), C_124))), inference(resolution, [status(thm)], [c_463, c_16])).
% 48.89/39.12  tff(c_54094, plain, (![B_1253, C_1254, C_1255]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(B_1253, C_1254), C_1255), C_1254)=k4_xboole_0(k4_xboole_0(B_1253, C_1254), C_1255))), inference(resolution, [status(thm)], [c_463, c_16])).
% 48.89/39.12  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 48.89/39.12  tff(c_443, plain, (![B_11, C_12, C_119]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_11, C_12), C_119), B_11))), inference(resolution, [status(thm)], [c_413, c_14])).
% 48.89/39.12  tff(c_149, plain, (![A_83, C_84, B_85]: (r1_xboole_0(A_83, k4_xboole_0(C_84, B_85)) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_50])).
% 48.89/39.12  tff(c_616, plain, (![A_136, C_137, B_138]: (k4_xboole_0(A_136, k4_xboole_0(C_137, B_138))=A_136 | ~r1_tarski(A_136, B_138))), inference(resolution, [status(thm)], [c_149, c_16])).
% 48.89/39.12  tff(c_4317, plain, (![A_321, C_322, B_323, A_324]: (r1_xboole_0(A_321, k4_xboole_0(C_322, B_323)) | ~r1_tarski(A_321, A_324) | ~r1_tarski(A_324, B_323))), inference(superposition, [status(thm), theory('equality')], [c_616, c_12])).
% 48.89/39.12  tff(c_4349, plain, (![C_325, B_326]: (r1_xboole_0('#skF_4', k4_xboole_0(C_325, B_326)) | ~r1_tarski(k2_relat_1('#skF_5'), B_326))), inference(resolution, [status(thm)], [c_70, c_4317])).
% 48.89/39.12  tff(c_4414, plain, (![C_327, B_328]: (k4_xboole_0('#skF_4', k4_xboole_0(C_327, B_328))='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), B_328))), inference(resolution, [status(thm)], [c_4349, c_16])).
% 48.89/39.12  tff(c_4418, plain, (![C_327]: (k4_xboole_0('#skF_4', k4_xboole_0(C_327, k2_relat_1('#skF_5')))='#skF_4')), inference(resolution, [status(thm)], [c_312, c_4414])).
% 48.89/39.12  tff(c_20, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 48.89/39.12  tff(c_1355, plain, (![A_178, A_179, C_180, B_181]: (r1_xboole_0(A_178, A_179) | ~r1_tarski(A_178, k4_xboole_0(C_180, B_181)) | ~r1_tarski(A_179, B_181))), inference(superposition, [status(thm), theory('equality')], [c_616, c_20])).
% 48.89/39.12  tff(c_1391, plain, (![C_182, B_183, A_184]: (r1_xboole_0(k4_xboole_0(C_182, B_183), A_184) | ~r1_tarski(A_184, B_183))), inference(resolution, [status(thm)], [c_312, c_1355])).
% 48.89/39.12  tff(c_12151, plain, (![C_597, B_598, A_599]: (k4_xboole_0(k4_xboole_0(C_597, B_598), A_599)=k4_xboole_0(C_597, B_598) | ~r1_tarski(A_599, B_598))), inference(resolution, [status(thm)], [c_1391, c_16])).
% 48.89/39.12  tff(c_12503, plain, (![C_327, A_599]: (k4_xboole_0('#skF_4', k4_xboole_0(C_327, k2_relat_1('#skF_5')))=k4_xboole_0('#skF_4', A_599) | ~r1_tarski(A_599, k4_xboole_0(C_327, k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_4418, c_12151])).
% 48.89/39.12  tff(c_14325, plain, (![A_621, C_622]: (k4_xboole_0('#skF_4', A_621)='#skF_4' | ~r1_tarski(A_621, k4_xboole_0(C_622, k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_4418, c_12503])).
% 48.89/39.12  tff(c_14489, plain, (![C_622, C_12, C_119]: (k4_xboole_0('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(C_622, k2_relat_1('#skF_5')), C_12), C_119))='#skF_4')), inference(resolution, [status(thm)], [c_443, c_14325])).
% 48.89/39.12  tff(c_32133, plain, (![C_903, C_904, C_905]: (k4_xboole_0('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903, k2_relat_1('#skF_5')), C_904), C_905))='#skF_4')), inference(resolution, [status(thm)], [c_443, c_14325])).
% 48.89/39.12  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 48.89/39.12  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 48.89/39.12  tff(c_155, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_36])).
% 48.89/39.12  tff(c_164, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_155])).
% 48.89/39.12  tff(c_167, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_164])).
% 48.89/39.12  tff(c_660, plain, (![C_137, B_138]: (k4_xboole_0(C_137, B_138)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_137, B_138), B_138))), inference(superposition, [status(thm), theory('equality')], [c_616, c_167])).
% 48.89/39.12  tff(c_32289, plain, (![C_903, C_904, C_905]: (k4_xboole_0('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903, k2_relat_1('#skF_5')), C_904), C_905))=k1_xboole_0 | ~r1_tarski('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903, k2_relat_1('#skF_5')), C_904), C_905)))), inference(superposition, [status(thm), theory('equality')], [c_32133, c_660])).
% 48.89/39.12  tff(c_32657, plain, (![C_903, C_904, C_905]: (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903, k2_relat_1('#skF_5')), C_904), C_905)))), inference(demodulation, [status(thm), theory('equality')], [c_14489, c_32289])).
% 48.89/39.12  tff(c_32658, plain, (![C_903, C_904, C_905]: (~r1_tarski('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(C_903, k2_relat_1('#skF_5')), C_904), C_905)))), inference(negUnitSimplification, [status(thm)], [c_72, c_32657])).
% 48.89/39.12  tff(c_55356, plain, (![B_1256, C_1257, C_1258, C_1259]: (~r1_tarski('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(B_1256, k2_relat_1('#skF_5')), C_1257), C_1258), C_1259)))), inference(superposition, [status(thm), theory('equality')], [c_54094, c_32658])).
% 48.89/39.12  tff(c_55360, plain, (![C_1258, B_122, C_1259, C_1257, C_124]: (~r1_tarski('#skF_4', k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(B_122, k2_relat_1('#skF_5')), C_124), C_1257), C_1258), C_1259)))), inference(superposition, [status(thm), theory('equality')], [c_483, c_55356])).
% 48.89/39.12  tff(c_248459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248360, c_55360])).
% 48.89/39.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.89/39.12  
% 48.89/39.12  Inference rules
% 48.89/39.12  ----------------------
% 48.89/39.12  #Ref     : 0
% 48.89/39.12  #Sup     : 63671
% 48.89/39.12  #Fact    : 0
% 48.89/39.12  #Define  : 0
% 48.89/39.12  #Split   : 33
% 48.89/39.12  #Chain   : 0
% 48.89/39.12  #Close   : 0
% 48.89/39.12  
% 48.89/39.12  Ordering : KBO
% 48.89/39.12  
% 48.89/39.12  Simplification rules
% 48.89/39.12  ----------------------
% 48.89/39.12  #Subsume      : 31003
% 48.89/39.12  #Demod        : 35827
% 48.89/39.12  #Tautology    : 19455
% 48.89/39.12  #SimpNegUnit  : 324
% 48.89/39.12  #BackRed      : 46
% 48.89/39.12  
% 48.89/39.12  #Partial instantiations: 0
% 48.89/39.12  #Strategies tried      : 1
% 48.89/39.12  
% 48.89/39.12  Timing (in seconds)
% 48.89/39.12  ----------------------
% 48.89/39.12  Preprocessing        : 0.37
% 48.89/39.12  Parsing              : 0.20
% 48.89/39.12  CNF conversion       : 0.03
% 48.89/39.12  Main loop            : 37.94
% 48.89/39.12  Inferencing          : 4.74
% 48.89/39.12  Reduction            : 12.91
% 48.89/39.12  Demodulation         : 10.19
% 48.89/39.12  BG Simplification    : 0.35
% 48.89/39.12  Subsumption          : 18.53
% 48.89/39.12  Abstraction          : 0.71
% 48.89/39.12  MUC search           : 0.00
% 48.89/39.12  Cooper               : 0.00
% 48.89/39.12  Total                : 38.35
% 48.89/39.12  Index Insertion      : 0.00
% 48.89/39.12  Index Deletion       : 0.00
% 48.89/39.12  Index Matching       : 0.00
% 48.89/39.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
