%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 230 expanded)
%              Number of leaves         :   40 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 280 expanded)
%              Number of equality atoms :   68 ( 190 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_48,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_88,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_83,plain,(
    ! [A_54] :
      ( v1_relat_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_83])).

tff(c_36,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(k5_relat_1(A_41,B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [A_37] : k1_setfam_1(k1_tarski(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_107,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = k1_setfam_1(k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_119,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_116])).

tff(c_140,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_149,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_140])).

tff(c_155,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_149])).

tff(c_255,plain,(
    ! [C_76,A_77,B_78] : k4_xboole_0(k2_zfmisc_1(C_76,A_77),k2_zfmisc_1(C_76,B_78)) = k2_zfmisc_1(C_76,k4_xboole_0(A_77,B_78)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_262,plain,(
    ! [C_76,B_78] : k2_zfmisc_1(C_76,k4_xboole_0(B_78,B_78)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_155])).

tff(c_271,plain,(
    ! [C_76] : k2_zfmisc_1(C_76,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_262])).

tff(c_291,plain,(
    ! [A_80,C_81,B_82] : k4_xboole_0(k2_zfmisc_1(A_80,C_81),k2_zfmisc_1(B_82,C_81)) = k2_zfmisc_1(k4_xboole_0(A_80,B_82),C_81) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [C_36,A_34,B_35] : k4_xboole_0(k2_zfmisc_1(C_36,A_34),k2_zfmisc_1(C_36,B_35)) = k2_zfmisc_1(C_36,k4_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_298,plain,(
    ! [B_82,C_81] : k2_zfmisc_1(k4_xboole_0(B_82,B_82),C_81) = k2_zfmisc_1(B_82,k4_xboole_0(C_81,C_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_28])).

tff(c_321,plain,(
    ! [C_81] : k2_zfmisc_1(k1_xboole_0,C_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_155,c_155,c_298])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_472,plain,(
    ! [A_95,B_96] :
      ( k1_relat_1(k5_relat_1(A_95,B_96)) = k1_relat_1(A_95)
      | ~ r1_tarski(k2_relat_1(A_95),k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_478,plain,(
    ! [B_96] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_96)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_472])).

tff(c_483,plain,(
    ! [B_97] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_97)) = k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_8,c_46,c_478])).

tff(c_38,plain,(
    ! [A_43] :
      ( k3_xboole_0(A_43,k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43))) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_495,plain,(
    ! [B_97] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_97),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_97)))) = k5_relat_1(k1_xboole_0,B_97)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_38])).

tff(c_503,plain,(
    ! [B_98] :
      ( k5_relat_1(k1_xboole_0,B_98) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_321,c_495])).

tff(c_507,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_503])).

tff(c_511,plain,(
    ! [B_99] :
      ( k5_relat_1(k1_xboole_0,B_99) = k1_xboole_0
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_507])).

tff(c_520,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_511])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_520])).

tff(c_527,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_542,plain,(
    ! [A_101,B_102] : k1_setfam_1(k2_tarski(A_101,B_102)) = k3_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_551,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = k1_setfam_1(k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_542])).

tff(c_554,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_551])).

tff(c_589,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_598,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_589])).

tff(c_604,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_598])).

tff(c_704,plain,(
    ! [A_121,C_122,B_123] : k4_xboole_0(k2_zfmisc_1(A_121,C_122),k2_zfmisc_1(B_123,C_122)) = k2_zfmisc_1(k4_xboole_0(A_121,B_123),C_122) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_711,plain,(
    ! [B_123,C_122] : k2_zfmisc_1(k4_xboole_0(B_123,B_123),C_122) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_604])).

tff(c_720,plain,(
    ! [C_122] : k2_zfmisc_1(k1_xboole_0,C_122) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_711])).

tff(c_766,plain,(
    ! [C_127,A_128,B_129] : k4_xboole_0(k2_zfmisc_1(C_127,A_128),k2_zfmisc_1(C_127,B_129)) = k2_zfmisc_1(C_127,k4_xboole_0(A_128,B_129)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_34,C_36,B_35] : k4_xboole_0(k2_zfmisc_1(A_34,C_36),k2_zfmisc_1(B_35,C_36)) = k2_zfmisc_1(k4_xboole_0(A_34,B_35),C_36) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_773,plain,(
    ! [C_127,B_129] : k2_zfmisc_1(k4_xboole_0(C_127,C_127),B_129) = k2_zfmisc_1(C_127,k4_xboole_0(B_129,B_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_26])).

tff(c_796,plain,(
    ! [C_127] : k2_zfmisc_1(C_127,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_604,c_604,c_773])).

tff(c_1303,plain,(
    ! [B_162,A_163] :
      ( k2_relat_1(k5_relat_1(B_162,A_163)) = k2_relat_1(A_163)
      | ~ r1_tarski(k1_relat_1(A_163),k2_relat_1(B_162))
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1309,plain,(
    ! [B_162] :
      ( k2_relat_1(k5_relat_1(B_162,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_162))
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1303])).

tff(c_1319,plain,(
    ! [B_164] :
      ( k2_relat_1(k5_relat_1(B_164,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_8,c_44,c_1309])).

tff(c_1334,plain,(
    ! [B_164] :
      ( k3_xboole_0(k5_relat_1(B_164,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_164,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_164,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_164,k1_xboole_0))
      | ~ v1_relat_1(B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_38])).

tff(c_1349,plain,(
    ! [B_165] :
      ( k5_relat_1(B_165,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_165,k1_xboole_0))
      | ~ v1_relat_1(B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_796,c_1334])).

tff(c_1356,plain,(
    ! [A_41] :
      ( k5_relat_1(A_41,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_36,c_1349])).

tff(c_1362,plain,(
    ! [A_166] :
      ( k5_relat_1(A_166,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1356])).

tff(c_1371,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_1362])).

tff(c_1378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_527,c_1371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:04:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.58  
% 3.12/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.59  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.12/1.59  
% 3.12/1.59  %Foreground sorts:
% 3.12/1.59  
% 3.12/1.59  
% 3.12/1.59  %Background operators:
% 3.12/1.59  
% 3.12/1.59  
% 3.12/1.59  %Foreground operators:
% 3.12/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.12/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.12/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.12/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.12/1.59  
% 3.12/1.60  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.12/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.12/1.60  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.12/1.60  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.12/1.60  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.12/1.60  tff(f_34, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.12/1.60  tff(f_54, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.12/1.60  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.60  tff(f_56, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.12/1.60  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.12/1.60  tff(f_52, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.12/1.60  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.12/1.60  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.12/1.60  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.12/1.60  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.12/1.60  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.12/1.60  tff(c_48, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.12/1.60  tff(c_88, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 3.12/1.60  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.12/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.12/1.60  tff(c_83, plain, (![A_54]: (v1_relat_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.12/1.60  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_83])).
% 3.12/1.60  tff(c_36, plain, (![A_41, B_42]: (v1_relat_1(k5_relat_1(A_41, B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.12/1.60  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.12/1.60  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.12/1.60  tff(c_30, plain, (![A_37]: (k1_setfam_1(k1_tarski(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.60  tff(c_12, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.60  tff(c_107, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.60  tff(c_116, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=k1_setfam_1(k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_107])).
% 3.12/1.60  tff(c_119, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_116])).
% 3.12/1.60  tff(c_140, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.12/1.60  tff(c_149, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_119, c_140])).
% 3.12/1.60  tff(c_155, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_149])).
% 3.12/1.60  tff(c_255, plain, (![C_76, A_77, B_78]: (k4_xboole_0(k2_zfmisc_1(C_76, A_77), k2_zfmisc_1(C_76, B_78))=k2_zfmisc_1(C_76, k4_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.60  tff(c_262, plain, (![C_76, B_78]: (k2_zfmisc_1(C_76, k4_xboole_0(B_78, B_78))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_255, c_155])).
% 3.12/1.60  tff(c_271, plain, (![C_76]: (k2_zfmisc_1(C_76, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_262])).
% 3.12/1.60  tff(c_291, plain, (![A_80, C_81, B_82]: (k4_xboole_0(k2_zfmisc_1(A_80, C_81), k2_zfmisc_1(B_82, C_81))=k2_zfmisc_1(k4_xboole_0(A_80, B_82), C_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.60  tff(c_28, plain, (![C_36, A_34, B_35]: (k4_xboole_0(k2_zfmisc_1(C_36, A_34), k2_zfmisc_1(C_36, B_35))=k2_zfmisc_1(C_36, k4_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.60  tff(c_298, plain, (![B_82, C_81]: (k2_zfmisc_1(k4_xboole_0(B_82, B_82), C_81)=k2_zfmisc_1(B_82, k4_xboole_0(C_81, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_291, c_28])).
% 3.12/1.60  tff(c_321, plain, (![C_81]: (k2_zfmisc_1(k1_xboole_0, C_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_271, c_155, c_155, c_298])).
% 3.12/1.60  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.60  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.12/1.60  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.12/1.60  tff(c_472, plain, (![A_95, B_96]: (k1_relat_1(k5_relat_1(A_95, B_96))=k1_relat_1(A_95) | ~r1_tarski(k2_relat_1(A_95), k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.12/1.60  tff(c_478, plain, (![B_96]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_96))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_472])).
% 3.12/1.60  tff(c_483, plain, (![B_97]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_97))=k1_xboole_0 | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_8, c_46, c_478])).
% 3.12/1.60  tff(c_38, plain, (![A_43]: (k3_xboole_0(A_43, k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.12/1.60  tff(c_495, plain, (![B_97]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_97), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_97))))=k5_relat_1(k1_xboole_0, B_97) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_97)) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_483, c_38])).
% 3.12/1.60  tff(c_503, plain, (![B_98]: (k5_relat_1(k1_xboole_0, B_98)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_98)) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_321, c_495])).
% 3.12/1.60  tff(c_507, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_503])).
% 3.12/1.60  tff(c_511, plain, (![B_99]: (k5_relat_1(k1_xboole_0, B_99)=k1_xboole_0 | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_507])).
% 3.12/1.60  tff(c_520, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_511])).
% 3.12/1.60  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_520])).
% 3.12/1.60  tff(c_527, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.12/1.60  tff(c_542, plain, (![A_101, B_102]: (k1_setfam_1(k2_tarski(A_101, B_102))=k3_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.60  tff(c_551, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=k1_setfam_1(k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_542])).
% 3.12/1.60  tff(c_554, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_551])).
% 3.12/1.60  tff(c_589, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.12/1.60  tff(c_598, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_554, c_589])).
% 3.12/1.60  tff(c_604, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_598])).
% 3.12/1.60  tff(c_704, plain, (![A_121, C_122, B_123]: (k4_xboole_0(k2_zfmisc_1(A_121, C_122), k2_zfmisc_1(B_123, C_122))=k2_zfmisc_1(k4_xboole_0(A_121, B_123), C_122))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.60  tff(c_711, plain, (![B_123, C_122]: (k2_zfmisc_1(k4_xboole_0(B_123, B_123), C_122)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_704, c_604])).
% 3.12/1.60  tff(c_720, plain, (![C_122]: (k2_zfmisc_1(k1_xboole_0, C_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_604, c_711])).
% 3.12/1.60  tff(c_766, plain, (![C_127, A_128, B_129]: (k4_xboole_0(k2_zfmisc_1(C_127, A_128), k2_zfmisc_1(C_127, B_129))=k2_zfmisc_1(C_127, k4_xboole_0(A_128, B_129)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.60  tff(c_26, plain, (![A_34, C_36, B_35]: (k4_xboole_0(k2_zfmisc_1(A_34, C_36), k2_zfmisc_1(B_35, C_36))=k2_zfmisc_1(k4_xboole_0(A_34, B_35), C_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.60  tff(c_773, plain, (![C_127, B_129]: (k2_zfmisc_1(k4_xboole_0(C_127, C_127), B_129)=k2_zfmisc_1(C_127, k4_xboole_0(B_129, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_766, c_26])).
% 3.12/1.60  tff(c_796, plain, (![C_127]: (k2_zfmisc_1(C_127, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_720, c_604, c_604, c_773])).
% 3.12/1.60  tff(c_1303, plain, (![B_162, A_163]: (k2_relat_1(k5_relat_1(B_162, A_163))=k2_relat_1(A_163) | ~r1_tarski(k1_relat_1(A_163), k2_relat_1(B_162)) | ~v1_relat_1(B_162) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.12/1.60  tff(c_1309, plain, (![B_162]: (k2_relat_1(k5_relat_1(B_162, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_162)) | ~v1_relat_1(B_162) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1303])).
% 3.12/1.60  tff(c_1319, plain, (![B_164]: (k2_relat_1(k5_relat_1(B_164, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_8, c_44, c_1309])).
% 3.12/1.60  tff(c_1334, plain, (![B_164]: (k3_xboole_0(k5_relat_1(B_164, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_164, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_164, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_164, k1_xboole_0)) | ~v1_relat_1(B_164))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_38])).
% 3.12/1.60  tff(c_1349, plain, (![B_165]: (k5_relat_1(B_165, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_165, k1_xboole_0)) | ~v1_relat_1(B_165))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_796, c_1334])).
% 3.12/1.60  tff(c_1356, plain, (![A_41]: (k5_relat_1(A_41, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_36, c_1349])).
% 3.12/1.60  tff(c_1362, plain, (![A_166]: (k5_relat_1(A_166, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1356])).
% 3.12/1.60  tff(c_1371, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_1362])).
% 3.12/1.60  tff(c_1378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_527, c_1371])).
% 3.12/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.60  
% 3.12/1.60  Inference rules
% 3.12/1.60  ----------------------
% 3.12/1.60  #Ref     : 0
% 3.12/1.60  #Sup     : 300
% 3.12/1.60  #Fact    : 0
% 3.12/1.60  #Define  : 0
% 3.12/1.60  #Split   : 1
% 3.12/1.60  #Chain   : 0
% 3.12/1.60  #Close   : 0
% 3.12/1.60  
% 3.12/1.60  Ordering : KBO
% 3.12/1.60  
% 3.12/1.60  Simplification rules
% 3.12/1.60  ----------------------
% 3.12/1.60  #Subsume      : 3
% 3.12/1.60  #Demod        : 344
% 3.12/1.60  #Tautology    : 218
% 3.12/1.60  #SimpNegUnit  : 2
% 3.12/1.60  #BackRed      : 5
% 3.12/1.60  
% 3.12/1.60  #Partial instantiations: 0
% 3.12/1.60  #Strategies tried      : 1
% 3.12/1.60  
% 3.12/1.60  Timing (in seconds)
% 3.12/1.60  ----------------------
% 3.12/1.60  Preprocessing        : 0.36
% 3.12/1.61  Parsing              : 0.19
% 3.12/1.61  CNF conversion       : 0.02
% 3.12/1.61  Main loop            : 0.42
% 3.12/1.61  Inferencing          : 0.16
% 3.12/1.61  Reduction            : 0.15
% 3.12/1.61  Demodulation         : 0.12
% 3.12/1.61  BG Simplification    : 0.02
% 3.12/1.61  Subsumption          : 0.05
% 3.12/1.61  Abstraction          : 0.03
% 3.12/1.61  MUC search           : 0.00
% 3.12/1.61  Cooper               : 0.00
% 3.12/1.61  Total                : 0.81
% 3.12/1.61  Index Insertion      : 0.00
% 3.12/1.61  Index Deletion       : 0.00
% 3.12/1.61  Index Matching       : 0.00
% 3.12/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
