%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:07 EST 2020

% Result     : Theorem 41.75s
% Output     : CNFRefutation 41.91s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 208 expanded)
%              Number of leaves         :   36 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :   88 ( 254 expanded)
%              Number of equality atoms :   86 ( 252 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_34,plain,(
    ! [B_49] : k2_zfmisc_1(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_253,plain,(
    ! [A_74,B_75,C_76] : k5_xboole_0(k5_xboole_0(A_74,B_75),C_76) = k5_xboole_0(A_74,k5_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_737,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_253])).

tff(c_845,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_881,plain,(
    ! [A_92] : k5_xboole_0(k1_xboole_0,A_92) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_845])).

tff(c_407,plain,(
    ! [A_80,B_81] : k5_xboole_0(k5_xboole_0(A_80,B_81),k2_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_453,plain,(
    ! [A_3] : k5_xboole_0(A_3,k2_xboole_0(A_3,k1_xboole_0)) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_407])).

tff(c_888,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_453])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_909,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_2])).

tff(c_40,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_122,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_144,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 = B_63
      | k1_xboole_0 = A_64
      | k2_zfmisc_1(A_64,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_144])).

tff(c_156,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_147])).

tff(c_36,plain,(
    ! [B_51] : k4_xboole_0(k1_tarski(B_51),k1_tarski(B_51)) != k1_tarski(B_51) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_36])).

tff(c_175,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_169])).

tff(c_1056,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_175])).

tff(c_1077,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_1056])).

tff(c_873,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_845])).

tff(c_456,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_7,A_7)) = k3_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_407])).

tff(c_1818,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k2_xboole_0(A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_456])).

tff(c_14,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26,D_27] : k3_enumset1(A_24,A_24,B_25,C_26,D_27) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,E_32) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,F_38) = k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1776,plain,(
    ! [F_129,A_127,G_123,E_126,H_125,C_130,B_124,D_128] : k2_xboole_0(k1_tarski(A_127),k5_enumset1(B_124,C_130,D_128,E_126,F_129,G_123,H_125)) = k6_enumset1(A_127,B_124,C_130,D_128,E_126,F_129,G_123,H_125) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7081,plain,(
    ! [A_265,E_260,F_262,C_261,B_264,A_259,D_263] : k6_enumset1(A_265,A_259,A_259,B_264,C_261,D_263,E_260,F_262) = k2_xboole_0(k1_tarski(A_265),k4_enumset1(A_259,B_264,C_261,D_263,E_260,F_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1776])).

tff(c_26,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,G_45) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7133,plain,(
    ! [E_260,F_262,C_261,B_264,A_259,D_263] : k2_xboole_0(k1_tarski(A_259),k4_enumset1(A_259,B_264,C_261,D_263,E_260,F_262)) = k5_enumset1(A_259,A_259,B_264,C_261,D_263,E_260,F_262) ),
    inference(superposition,[status(thm),theory(equality)],[c_7081,c_26])).

tff(c_96443,plain,(
    ! [A_670,F_669,E_667,D_672,C_671,B_668] : k2_xboole_0(k1_tarski(A_670),k4_enumset1(A_670,B_668,C_671,D_672,E_667,F_669)) = k4_enumset1(A_670,B_668,C_671,D_672,E_667,F_669) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7133])).

tff(c_98186,plain,(
    ! [B_677,F_678,C_680,E_679,D_681] : k2_xboole_0(k1_xboole_0,k4_enumset1('#skF_2',B_677,C_680,D_681,E_679,F_678)) = k4_enumset1('#skF_2',B_677,C_680,D_681,E_679,F_678) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_96443])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k5_xboole_0(k5_xboole_0(A_4,B_5),C_6) = k5_xboole_0(A_4,k5_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2004,plain,(
    ! [A_148,B_149] : k5_xboole_0(A_148,k5_xboole_0(B_149,k2_xboole_0(A_148,B_149))) = k3_xboole_0(A_148,B_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_407])).

tff(c_294,plain,(
    ! [A_7,C_76] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_76)) = k5_xboole_0(k1_xboole_0,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_253])).

tff(c_874,plain,(
    ! [A_7,C_76] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_76)) = C_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_294])).

tff(c_2019,plain,(
    ! [B_149,A_148] : k5_xboole_0(B_149,k2_xboole_0(A_148,B_149)) = k5_xboole_0(A_148,k3_xboole_0(A_148,B_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2004,c_874])).

tff(c_2084,plain,(
    ! [B_149,A_148] : k5_xboole_0(B_149,k2_xboole_0(A_148,B_149)) = k4_xboole_0(A_148,B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2019])).

tff(c_98252,plain,(
    ! [B_677,F_678,C_680,E_679,D_681] : k5_xboole_0(k4_enumset1('#skF_2',B_677,C_680,D_681,E_679,F_678),k4_enumset1('#skF_2',B_677,C_680,D_681,E_679,F_678)) = k4_xboole_0(k1_xboole_0,k4_enumset1('#skF_2',B_677,C_680,D_681,E_679,F_678)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98186,c_2084])).

tff(c_98297,plain,(
    ! [B_686,F_683,E_684,C_685,D_682] : k3_xboole_0(k1_xboole_0,k4_enumset1('#skF_2',B_686,C_685,D_682,E_684,F_683)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_8,c_98252])).

tff(c_98428,plain,(
    ! [B_687,C_688,D_689,E_690] : k3_xboole_0(k1_xboole_0,k3_enumset1('#skF_2',B_687,C_688,D_689,E_690)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_98297])).

tff(c_98551,plain,(
    ! [B_691,C_692,D_693] : k3_xboole_0(k1_xboole_0,k2_enumset1('#skF_2',B_691,C_692,D_693)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98428])).

tff(c_98672,plain,(
    ! [B_694,C_695] : k3_xboole_0(k1_xboole_0,k1_enumset1('#skF_2',B_694,C_695)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_98551])).

tff(c_98793,plain,(
    ! [B_696] : k3_xboole_0(k1_xboole_0,k2_tarski('#skF_2',B_696)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_98672])).

tff(c_98885,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_98793])).

tff(c_98914,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_156,c_98885])).

tff(c_98916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1077,c_98914])).

tff(c_98917,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_98940,plain,(
    ! [B_698,A_699] :
      ( k1_xboole_0 = B_698
      | k1_xboole_0 = A_699
      | k2_zfmisc_1(A_699,B_698) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98943,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_98917,c_98940])).

tff(c_98952,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_98943])).

tff(c_98918,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_98957,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98952,c_98918])).

tff(c_98961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.75/32.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.75/32.39  
% 41.75/32.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.75/32.40  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 41.75/32.40  
% 41.75/32.40  %Foreground sorts:
% 41.75/32.40  
% 41.75/32.40  
% 41.75/32.40  %Background operators:
% 41.75/32.40  
% 41.75/32.40  
% 41.75/32.40  %Foreground operators:
% 41.75/32.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.75/32.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 41.75/32.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 41.75/32.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 41.75/32.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 41.75/32.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 41.75/32.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 41.75/32.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 41.75/32.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 41.75/32.40  tff('#skF_2', type, '#skF_2': $i).
% 41.75/32.40  tff('#skF_1', type, '#skF_1': $i).
% 41.75/32.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 41.75/32.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 41.75/32.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.75/32.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 41.75/32.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 41.75/32.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.75/32.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 41.75/32.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.75/32.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 41.75/32.40  
% 41.91/32.41  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 41.91/32.41  tff(f_74, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 41.91/32.41  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 41.91/32.41  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 41.91/32.41  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 41.91/32.41  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 41.91/32.41  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 41.91/32.41  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 41.91/32.41  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 41.91/32.41  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 41.91/32.41  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 41.91/32.41  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 41.91/32.41  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 41.91/32.41  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 41.91/32.41  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 41.91/32.41  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 41.91/32.41  tff(c_34, plain, (![B_49]: (k2_zfmisc_1(k1_xboole_0, B_49)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.91/32.41  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 41.91/32.41  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 41.91/32.41  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 41.91/32.41  tff(c_253, plain, (![A_74, B_75, C_76]: (k5_xboole_0(k5_xboole_0(A_74, B_75), C_76)=k5_xboole_0(A_74, k5_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.91/32.41  tff(c_737, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_8, c_253])).
% 41.91/32.41  tff(c_845, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 41.91/32.41  tff(c_881, plain, (![A_92]: (k5_xboole_0(k1_xboole_0, A_92)=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_845])).
% 41.91/32.41  tff(c_407, plain, (![A_80, B_81]: (k5_xboole_0(k5_xboole_0(A_80, B_81), k2_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 41.91/32.41  tff(c_453, plain, (![A_3]: (k5_xboole_0(A_3, k2_xboole_0(A_3, k1_xboole_0))=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_407])).
% 41.91/32.41  tff(c_888, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_881, c_453])).
% 41.91/32.41  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.91/32.41  tff(c_909, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_881, c_2])).
% 41.91/32.41  tff(c_40, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 41.91/32.41  tff(c_122, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 41.91/32.41  tff(c_144, plain, (![B_63, A_64]: (k1_xboole_0=B_63 | k1_xboole_0=A_64 | k2_zfmisc_1(A_64, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.91/32.41  tff(c_147, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122, c_144])).
% 41.91/32.41  tff(c_156, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_147])).
% 41.91/32.41  tff(c_36, plain, (![B_51]: (k4_xboole_0(k1_tarski(B_51), k1_tarski(B_51))!=k1_tarski(B_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 41.91/32.41  tff(c_169, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_156, c_36])).
% 41.91/32.41  tff(c_175, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_169])).
% 41.91/32.41  tff(c_1056, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_909, c_175])).
% 41.91/32.41  tff(c_1077, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_888, c_1056])).
% 41.91/32.41  tff(c_873, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_845])).
% 41.91/32.41  tff(c_456, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_7, A_7))=k3_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_407])).
% 41.91/32.41  tff(c_1818, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k2_xboole_0(A_7, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_456])).
% 41.91/32.41  tff(c_14, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 41.91/32.41  tff(c_16, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.91/32.41  tff(c_18, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 41.91/32.41  tff(c_20, plain, (![A_24, B_25, C_26, D_27]: (k3_enumset1(A_24, A_24, B_25, C_26, D_27)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 41.91/32.41  tff(c_22, plain, (![C_30, E_32, D_31, B_29, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, E_32)=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 41.91/32.41  tff(c_24, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, F_38)=k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 41.91/32.41  tff(c_1776, plain, (![F_129, A_127, G_123, E_126, H_125, C_130, B_124, D_128]: (k2_xboole_0(k1_tarski(A_127), k5_enumset1(B_124, C_130, D_128, E_126, F_129, G_123, H_125))=k6_enumset1(A_127, B_124, C_130, D_128, E_126, F_129, G_123, H_125))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.91/32.41  tff(c_7081, plain, (![A_265, E_260, F_262, C_261, B_264, A_259, D_263]: (k6_enumset1(A_265, A_259, A_259, B_264, C_261, D_263, E_260, F_262)=k2_xboole_0(k1_tarski(A_265), k4_enumset1(A_259, B_264, C_261, D_263, E_260, F_262)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1776])).
% 41.91/32.41  tff(c_26, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, G_45)=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 41.91/32.41  tff(c_7133, plain, (![E_260, F_262, C_261, B_264, A_259, D_263]: (k2_xboole_0(k1_tarski(A_259), k4_enumset1(A_259, B_264, C_261, D_263, E_260, F_262))=k5_enumset1(A_259, A_259, B_264, C_261, D_263, E_260, F_262))), inference(superposition, [status(thm), theory('equality')], [c_7081, c_26])).
% 41.91/32.41  tff(c_96443, plain, (![A_670, F_669, E_667, D_672, C_671, B_668]: (k2_xboole_0(k1_tarski(A_670), k4_enumset1(A_670, B_668, C_671, D_672, E_667, F_669))=k4_enumset1(A_670, B_668, C_671, D_672, E_667, F_669))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7133])).
% 41.91/32.41  tff(c_98186, plain, (![B_677, F_678, C_680, E_679, D_681]: (k2_xboole_0(k1_xboole_0, k4_enumset1('#skF_2', B_677, C_680, D_681, E_679, F_678))=k4_enumset1('#skF_2', B_677, C_680, D_681, E_679, F_678))), inference(superposition, [status(thm), theory('equality')], [c_156, c_96443])).
% 41.91/32.41  tff(c_6, plain, (![A_4, B_5, C_6]: (k5_xboole_0(k5_xboole_0(A_4, B_5), C_6)=k5_xboole_0(A_4, k5_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.91/32.41  tff(c_2004, plain, (![A_148, B_149]: (k5_xboole_0(A_148, k5_xboole_0(B_149, k2_xboole_0(A_148, B_149)))=k3_xboole_0(A_148, B_149))), inference(superposition, [status(thm), theory('equality')], [c_6, c_407])).
% 41.91/32.41  tff(c_294, plain, (![A_7, C_76]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_76))=k5_xboole_0(k1_xboole_0, C_76))), inference(superposition, [status(thm), theory('equality')], [c_8, c_253])).
% 41.91/32.41  tff(c_874, plain, (![A_7, C_76]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_76))=C_76)), inference(demodulation, [status(thm), theory('equality')], [c_873, c_294])).
% 41.91/32.41  tff(c_2019, plain, (![B_149, A_148]: (k5_xboole_0(B_149, k2_xboole_0(A_148, B_149))=k5_xboole_0(A_148, k3_xboole_0(A_148, B_149)))), inference(superposition, [status(thm), theory('equality')], [c_2004, c_874])).
% 41.91/32.41  tff(c_2084, plain, (![B_149, A_148]: (k5_xboole_0(B_149, k2_xboole_0(A_148, B_149))=k4_xboole_0(A_148, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2019])).
% 41.91/32.41  tff(c_98252, plain, (![B_677, F_678, C_680, E_679, D_681]: (k5_xboole_0(k4_enumset1('#skF_2', B_677, C_680, D_681, E_679, F_678), k4_enumset1('#skF_2', B_677, C_680, D_681, E_679, F_678))=k4_xboole_0(k1_xboole_0, k4_enumset1('#skF_2', B_677, C_680, D_681, E_679, F_678)))), inference(superposition, [status(thm), theory('equality')], [c_98186, c_2084])).
% 41.91/32.41  tff(c_98297, plain, (![B_686, F_683, E_684, C_685, D_682]: (k3_xboole_0(k1_xboole_0, k4_enumset1('#skF_2', B_686, C_685, D_682, E_684, F_683))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_909, c_8, c_98252])).
% 41.91/32.41  tff(c_98428, plain, (![B_687, C_688, D_689, E_690]: (k3_xboole_0(k1_xboole_0, k3_enumset1('#skF_2', B_687, C_688, D_689, E_690))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_98297])).
% 41.91/32.41  tff(c_98551, plain, (![B_691, C_692, D_693]: (k3_xboole_0(k1_xboole_0, k2_enumset1('#skF_2', B_691, C_692, D_693))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_98428])).
% 41.91/32.41  tff(c_98672, plain, (![B_694, C_695]: (k3_xboole_0(k1_xboole_0, k1_enumset1('#skF_2', B_694, C_695))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_98551])).
% 41.91/32.41  tff(c_98793, plain, (![B_696]: (k3_xboole_0(k1_xboole_0, k2_tarski('#skF_2', B_696))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_98672])).
% 41.91/32.41  tff(c_98885, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_98793])).
% 41.91/32.41  tff(c_98914, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1818, c_156, c_98885])).
% 41.91/32.41  tff(c_98916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1077, c_98914])).
% 41.91/32.41  tff(c_98917, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 41.91/32.41  tff(c_98940, plain, (![B_698, A_699]: (k1_xboole_0=B_698 | k1_xboole_0=A_699 | k2_zfmisc_1(A_699, B_698)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.91/32.41  tff(c_98943, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_98917, c_98940])).
% 41.91/32.41  tff(c_98952, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_98943])).
% 41.91/32.41  tff(c_98918, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 41.91/32.41  tff(c_98957, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_98952, c_98918])).
% 41.91/32.41  tff(c_98961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_98957])).
% 41.91/32.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.91/32.41  
% 41.91/32.41  Inference rules
% 41.91/32.41  ----------------------
% 41.91/32.41  #Ref     : 0
% 41.91/32.41  #Sup     : 26050
% 41.91/32.41  #Fact    : 0
% 41.91/32.41  #Define  : 0
% 41.91/32.41  #Split   : 1
% 41.91/32.41  #Chain   : 0
% 41.91/32.41  #Close   : 0
% 41.91/32.41  
% 41.91/32.41  Ordering : KBO
% 41.91/32.41  
% 41.91/32.41  Simplification rules
% 41.91/32.41  ----------------------
% 41.91/32.41  #Subsume      : 2147
% 41.91/32.41  #Demod        : 34175
% 41.91/32.41  #Tautology    : 7722
% 41.91/32.41  #SimpNegUnit  : 13
% 41.91/32.41  #BackRed      : 19
% 41.91/32.41  
% 41.91/32.41  #Partial instantiations: 0
% 41.91/32.41  #Strategies tried      : 1
% 41.91/32.41  
% 41.91/32.41  Timing (in seconds)
% 41.91/32.41  ----------------------
% 41.91/32.42  Preprocessing        : 0.51
% 41.91/32.42  Parsing              : 0.27
% 41.91/32.42  CNF conversion       : 0.03
% 41.91/32.42  Main loop            : 30.98
% 41.91/32.42  Inferencing          : 3.58
% 41.91/32.42  Reduction            : 22.58
% 41.91/32.42  Demodulation         : 21.56
% 41.91/32.42  BG Simplification    : 0.62
% 41.91/32.42  Subsumption          : 3.49
% 41.91/32.42  Abstraction          : 1.16
% 41.91/32.42  MUC search           : 0.00
% 41.91/32.42  Cooper               : 0.00
% 41.91/32.42  Total                : 31.54
% 41.91/32.42  Index Insertion      : 0.00
% 41.91/32.42  Index Deletion       : 0.00
% 41.91/32.42  Index Matching       : 0.00
% 42.00/32.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
