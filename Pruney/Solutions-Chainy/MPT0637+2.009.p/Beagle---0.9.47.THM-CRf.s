%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:25 EST 2020

% Result     : Theorem 13.52s
% Output     : CNFRefutation 13.52s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 430 expanded)
%              Number of leaves         :   33 ( 164 expanded)
%              Depth                    :   15
%              Number of atoms          :  180 ( 689 expanded)
%              Number of equality atoms :   67 ( 295 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_42,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_646,plain,(
    ! [B_89,A_90] :
      ( k7_relat_1(B_89,k3_xboole_0(k1_relat_1(B_89),A_90)) = k7_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_429,plain,(
    ! [A_77,B_78] :
      ( k5_relat_1(k6_relat_1(A_77),B_78) = k7_relat_1(B_78,A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k5_relat_1(B_32,k6_relat_1(A_31)),B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_436,plain,(
    ! [A_31,A_77] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_77),k6_relat_1(A_77))
      | ~ v1_relat_1(k6_relat_1(A_77))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_34])).

tff(c_463,plain,(
    ! [A_31,A_77] : r1_tarski(k7_relat_1(k6_relat_1(A_31),A_77),k6_relat_1(A_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_436])).

tff(c_653,plain,(
    ! [A_31,A_90] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_90),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)),A_90)))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_463])).

tff(c_678,plain,(
    ! [A_31,A_90] : r1_tarski(k7_relat_1(k6_relat_1(A_31),A_90),k6_relat_1(k3_xboole_0(A_31,A_90))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_653])).

tff(c_12,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [B_57,A_58] : k1_setfam_1(k2_tarski(B_57,A_58)) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_18,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,A_58) = k3_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_18])).

tff(c_30,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_35] :
      ( k5_relat_1(A_35,k6_relat_1(k2_relat_1(A_35))) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_447,plain,(
    ! [A_77] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_77))),A_77) = k6_relat_1(A_77)
      | ~ v1_relat_1(k6_relat_1(A_77))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_77)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_38])).

tff(c_467,plain,(
    ! [A_77] : k7_relat_1(k6_relat_1(A_77),A_77) = k6_relat_1(A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_30,c_447])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_675,plain,(
    ! [A_30,A_90] :
      ( k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_90)) = k7_relat_1(k6_relat_1(A_30),A_90)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_646])).

tff(c_1819,plain,(
    ! [A_127,A_128] : k7_relat_1(k6_relat_1(A_127),k3_xboole_0(A_127,A_128)) = k7_relat_1(k6_relat_1(A_127),A_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_675])).

tff(c_1868,plain,(
    ! [A_3,B_4] : k7_relat_1(k6_relat_1(k3_xboole_0(A_3,B_4)),k3_xboole_0(A_3,B_4)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_3,B_4)),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1819])).

tff(c_2335,plain,(
    ! [A_147,B_148] : k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),A_147) = k6_relat_1(k3_xboole_0(A_147,B_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_1868])).

tff(c_2404,plain,(
    ! [B_57,A_58] : k7_relat_1(k6_relat_1(k3_xboole_0(B_57,A_58)),A_58) = k6_relat_1(k3_xboole_0(A_58,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2335])).

tff(c_683,plain,(
    ! [A_30,A_90] : k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_90)) = k7_relat_1(k6_relat_1(A_30),A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_675])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_324,plain,(
    ! [A_73,B_74] : k3_xboole_0(k3_xboole_0(A_73,B_74),A_73) = k3_xboole_0(A_73,B_74) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_327,plain,(
    ! [A_73,B_74] : k3_xboole_0(k3_xboole_0(A_73,B_74),k3_xboole_0(A_73,B_74)) = k3_xboole_0(k3_xboole_0(A_73,B_74),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_135])).

tff(c_379,plain,(
    ! [A_75,B_76] : k3_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_136,c_327])).

tff(c_686,plain,(
    ! [B_91,A_92] : k3_xboole_0(B_91,k3_xboole_0(A_92,B_91)) = k3_xboole_0(B_91,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_379])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,k3_xboole_0(k1_relat_1(B_22),A_21)) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_696,plain,(
    ! [B_22,A_92] :
      ( k7_relat_1(B_22,k3_xboole_0(k1_relat_1(B_22),A_92)) = k7_relat_1(B_22,k3_xboole_0(A_92,k1_relat_1(B_22)))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_24])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_31),B_32),B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1352,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(k7_relat_1(B_112,A_113),B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_32])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1357,plain,(
    ! [B_112,A_113] :
      ( k3_xboole_0(k7_relat_1(B_112,A_113),B_112) = k7_relat_1(B_112,A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_1352,c_10])).

tff(c_2130,plain,(
    ! [B_139,A_140] :
      ( k3_xboole_0(B_139,k7_relat_1(B_139,A_140)) = k7_relat_1(B_139,A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_1357])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2288,plain,(
    ! [B_143,A_144] :
      ( v1_relat_1(k7_relat_1(B_143,A_144))
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2130,c_20])).

tff(c_2291,plain,(
    ! [A_30,A_90] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_30),A_90))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_2288])).

tff(c_2308,plain,(
    ! [A_30,A_90] : v1_relat_1(k7_relat_1(k6_relat_1(A_30),A_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_2291])).

tff(c_2208,plain,(
    ! [A_30,A_90] :
      ( k3_xboole_0(k6_relat_1(A_30),k7_relat_1(k6_relat_1(A_30),A_90)) = k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_90))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_2130])).

tff(c_19340,plain,(
    ! [A_358,A_359] : k3_xboole_0(k6_relat_1(A_358),k7_relat_1(k6_relat_1(A_358),A_359)) = k7_relat_1(k6_relat_1(A_358),A_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_683,c_2208])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_253,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_64),B_65),B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_256,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(k5_relat_1(k6_relat_1(A_64),B_65),B_65) = k5_relat_1(k6_relat_1(A_64),B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_253,c_10])).

tff(c_12423,plain,(
    ! [B_289,A_290] :
      ( k3_xboole_0(B_289,k5_relat_1(k6_relat_1(A_290),B_289)) = k5_relat_1(k6_relat_1(A_290),B_289)
      | ~ v1_relat_1(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_256])).

tff(c_12650,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k3_xboole_0(B_37,k7_relat_1(B_37,A_36))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12423])).

tff(c_19368,plain,(
    ! [A_359,A_358] :
      ( k5_relat_1(k6_relat_1(A_359),k6_relat_1(A_358)) = k7_relat_1(k6_relat_1(A_358),A_359)
      | ~ v1_relat_1(k6_relat_1(A_358))
      | ~ v1_relat_1(k6_relat_1(A_358)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19340,c_12650])).

tff(c_19659,plain,(
    ! [A_359,A_358] : k5_relat_1(k6_relat_1(A_359),k6_relat_1(A_358)) = k7_relat_1(k6_relat_1(A_358),A_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_19368])).

tff(c_5602,plain,(
    ! [A_219,B_220] : k7_relat_1(k6_relat_1(A_219),k3_xboole_0(B_220,A_219)) = k7_relat_1(k6_relat_1(A_219),B_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_1819])).

tff(c_821,plain,(
    ! [C_96,A_97,B_98] :
      ( k7_relat_1(k7_relat_1(C_96,A_97),B_98) = k7_relat_1(C_96,k3_xboole_0(A_97,B_98))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_840,plain,(
    ! [B_22,A_21,B_98] :
      ( k7_relat_1(B_22,k3_xboole_0(k3_xboole_0(k1_relat_1(B_22),A_21),B_98)) = k7_relat_1(k7_relat_1(B_22,A_21),B_98)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_821])).

tff(c_5625,plain,(
    ! [A_219,A_21] :
      ( k7_relat_1(k6_relat_1(A_219),k3_xboole_0(k1_relat_1(k6_relat_1(A_219)),A_21)) = k7_relat_1(k7_relat_1(k6_relat_1(A_219),A_21),A_219)
      | ~ v1_relat_1(k6_relat_1(A_219))
      | ~ v1_relat_1(k6_relat_1(A_219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5602,c_840])).

tff(c_5754,plain,(
    ! [A_219,A_21] : k7_relat_1(k7_relat_1(k6_relat_1(A_219),A_21),A_219) = k7_relat_1(k6_relat_1(A_219),A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_683,c_28,c_5625])).

tff(c_290,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2543,plain,(
    ! [A_153,B_154] :
      ( k5_relat_1(k6_relat_1(A_153),B_154) = B_154
      | ~ r1_tarski(B_154,k5_relat_1(k6_relat_1(A_153),B_154))
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_32,c_290])).

tff(c_21757,plain,(
    ! [A_374,B_375] :
      ( k5_relat_1(k6_relat_1(A_374),B_375) = B_375
      | ~ r1_tarski(B_375,k7_relat_1(B_375,A_374))
      | ~ v1_relat_1(B_375)
      | ~ v1_relat_1(B_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2543])).

tff(c_21778,plain,(
    ! [A_219,A_21] :
      ( k5_relat_1(k6_relat_1(A_219),k7_relat_1(k6_relat_1(A_219),A_21)) = k7_relat_1(k6_relat_1(A_219),A_21)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_219),A_21),k7_relat_1(k6_relat_1(A_219),A_21))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_219),A_21))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_219),A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5754,c_21757])).

tff(c_21827,plain,(
    ! [A_219,A_21] : k5_relat_1(k6_relat_1(A_219),k7_relat_1(k6_relat_1(A_219),A_21)) = k7_relat_1(k6_relat_1(A_219),A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2308,c_6,c_21778])).

tff(c_881,plain,(
    ! [A_101,B_102,C_103] :
      ( k5_relat_1(k5_relat_1(A_101,B_102),C_103) = k5_relat_1(A_101,k5_relat_1(B_102,C_103))
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_891,plain,(
    ! [A_101,B_102,A_31] :
      ( r1_tarski(k5_relat_1(A_101,k5_relat_1(B_102,k6_relat_1(A_31))),k5_relat_1(A_101,B_102))
      | ~ v1_relat_1(k5_relat_1(A_101,B_102))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_34])).

tff(c_4944,plain,(
    ! [A_206,B_207,A_208] :
      ( r1_tarski(k5_relat_1(A_206,k5_relat_1(B_207,k6_relat_1(A_208))),k5_relat_1(A_206,B_207))
      | ~ v1_relat_1(k5_relat_1(A_206,B_207))
      | ~ v1_relat_1(B_207)
      | ~ v1_relat_1(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_891])).

tff(c_4999,plain,(
    ! [A_206,A_208,A_36] :
      ( r1_tarski(k5_relat_1(A_206,k7_relat_1(k6_relat_1(A_208),A_36)),k5_relat_1(A_206,k6_relat_1(A_36)))
      | ~ v1_relat_1(k5_relat_1(A_206,k6_relat_1(A_36)))
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(A_206)
      | ~ v1_relat_1(k6_relat_1(A_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4944])).

tff(c_38525,plain,(
    ! [A_489,A_490,A_491] :
      ( r1_tarski(k5_relat_1(A_489,k7_relat_1(k6_relat_1(A_490),A_491)),k5_relat_1(A_489,k6_relat_1(A_491)))
      | ~ v1_relat_1(k5_relat_1(A_489,k6_relat_1(A_491)))
      | ~ v1_relat_1(A_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_4999])).

tff(c_38575,plain,(
    ! [A_219,A_21] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_219),A_21),k5_relat_1(k6_relat_1(A_219),k6_relat_1(A_21)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_219),k6_relat_1(A_21)))
      | ~ v1_relat_1(k6_relat_1(A_219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21827,c_38525])).

tff(c_38816,plain,(
    ! [A_492,A_493] : r1_tarski(k7_relat_1(k6_relat_1(A_492),A_493),k7_relat_1(k6_relat_1(A_493),A_492)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2308,c_19659,c_19659,c_38575])).

tff(c_38862,plain,(
    ! [A_92,A_493] :
      ( r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_92,k1_relat_1(k6_relat_1(A_493)))),A_493),k7_relat_1(k6_relat_1(A_493),k3_xboole_0(k1_relat_1(k6_relat_1(A_493)),A_92)))
      | ~ v1_relat_1(k6_relat_1(A_493)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_38816])).

tff(c_39807,plain,(
    ! [A_496,A_497] : r1_tarski(k6_relat_1(k3_xboole_0(A_496,A_497)),k7_relat_1(k6_relat_1(A_496),A_497)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2404,c_683,c_28,c_28,c_38862])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39814,plain,(
    ! [A_496,A_497] :
      ( k7_relat_1(k6_relat_1(A_496),A_497) = k6_relat_1(k3_xboole_0(A_496,A_497))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_496),A_497),k6_relat_1(k3_xboole_0(A_496,A_497))) ) ),
    inference(resolution,[status(thm)],[c_39807,c_2])).

tff(c_40046,plain,(
    ! [A_496,A_497] : k7_relat_1(k6_relat_1(A_496),A_497) = k6_relat_1(k3_xboole_0(A_496,A_497)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_39814])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_450,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_46])).

tff(c_469,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_450])).

tff(c_40884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40046,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.52/6.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/6.77  
% 13.52/6.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/6.77  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 13.52/6.77  
% 13.52/6.77  %Foreground sorts:
% 13.52/6.77  
% 13.52/6.77  
% 13.52/6.77  %Background operators:
% 13.52/6.77  
% 13.52/6.77  
% 13.52/6.77  %Foreground operators:
% 13.52/6.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.52/6.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.52/6.77  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.52/6.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.52/6.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.52/6.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.52/6.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.52/6.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.52/6.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.52/6.77  tff('#skF_2', type, '#skF_2': $i).
% 13.52/6.77  tff('#skF_1', type, '#skF_1': $i).
% 13.52/6.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.52/6.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.52/6.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.52/6.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.52/6.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.52/6.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.52/6.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.52/6.77  
% 13.52/6.79  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 13.52/6.79  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.52/6.79  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 13.52/6.79  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 13.52/6.79  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 13.52/6.79  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.52/6.79  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.52/6.79  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 13.52/6.79  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.52/6.79  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.52/6.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.52/6.79  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 13.52/6.79  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 13.52/6.79  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 13.52/6.79  tff(f_98, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 13.52/6.79  tff(c_42, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.52/6.79  tff(c_28, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.52/6.79  tff(c_646, plain, (![B_89, A_90]: (k7_relat_1(B_89, k3_xboole_0(k1_relat_1(B_89), A_90))=k7_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.52/6.79  tff(c_429, plain, (![A_77, B_78]: (k5_relat_1(k6_relat_1(A_77), B_78)=k7_relat_1(B_78, A_77) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.52/6.79  tff(c_34, plain, (![B_32, A_31]: (r1_tarski(k5_relat_1(B_32, k6_relat_1(A_31)), B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.52/6.79  tff(c_436, plain, (![A_31, A_77]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_77), k6_relat_1(A_77)) | ~v1_relat_1(k6_relat_1(A_77)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_429, c_34])).
% 13.52/6.79  tff(c_463, plain, (![A_31, A_77]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_77), k6_relat_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_436])).
% 13.52/6.79  tff(c_653, plain, (![A_31, A_90]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_90), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)), A_90))) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_646, c_463])).
% 13.52/6.79  tff(c_678, plain, (![A_31, A_90]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_90), k6_relat_1(k3_xboole_0(A_31, A_90))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_653])).
% 13.52/6.79  tff(c_12, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.52/6.79  tff(c_113, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.52/6.79  tff(c_153, plain, (![B_57, A_58]: (k1_setfam_1(k2_tarski(B_57, A_58))=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_12, c_113])).
% 13.52/6.79  tff(c_18, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.52/6.79  tff(c_159, plain, (![B_57, A_58]: (k3_xboole_0(B_57, A_58)=k3_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_153, c_18])).
% 13.52/6.79  tff(c_30, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.52/6.79  tff(c_38, plain, (![A_35]: (k5_relat_1(A_35, k6_relat_1(k2_relat_1(A_35)))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.52/6.79  tff(c_447, plain, (![A_77]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_77))), A_77)=k6_relat_1(A_77) | ~v1_relat_1(k6_relat_1(A_77)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_77)))))), inference(superposition, [status(thm), theory('equality')], [c_429, c_38])).
% 13.52/6.79  tff(c_467, plain, (![A_77]: (k7_relat_1(k6_relat_1(A_77), A_77)=k6_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_30, c_447])).
% 13.52/6.79  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.52/6.79  tff(c_128, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.52/6.79  tff(c_135, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_128])).
% 13.52/6.79  tff(c_675, plain, (![A_30, A_90]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_90))=k7_relat_1(k6_relat_1(A_30), A_90) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_646])).
% 13.52/6.79  tff(c_1819, plain, (![A_127, A_128]: (k7_relat_1(k6_relat_1(A_127), k3_xboole_0(A_127, A_128))=k7_relat_1(k6_relat_1(A_127), A_128))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_675])).
% 13.52/6.79  tff(c_1868, plain, (![A_3, B_4]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_3, B_4)), k3_xboole_0(A_3, B_4))=k7_relat_1(k6_relat_1(k3_xboole_0(A_3, B_4)), A_3))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1819])).
% 13.52/6.79  tff(c_2335, plain, (![A_147, B_148]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), A_147)=k6_relat_1(k3_xboole_0(A_147, B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_1868])).
% 13.52/6.79  tff(c_2404, plain, (![B_57, A_58]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_57, A_58)), A_58)=k6_relat_1(k3_xboole_0(A_58, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_2335])).
% 13.52/6.79  tff(c_683, plain, (![A_30, A_90]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_90))=k7_relat_1(k6_relat_1(A_30), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_675])).
% 13.52/6.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/6.79  tff(c_136, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_128])).
% 13.52/6.79  tff(c_324, plain, (![A_73, B_74]: (k3_xboole_0(k3_xboole_0(A_73, B_74), A_73)=k3_xboole_0(A_73, B_74))), inference(resolution, [status(thm)], [c_8, c_128])).
% 13.52/6.79  tff(c_327, plain, (![A_73, B_74]: (k3_xboole_0(k3_xboole_0(A_73, B_74), k3_xboole_0(A_73, B_74))=k3_xboole_0(k3_xboole_0(A_73, B_74), A_73))), inference(superposition, [status(thm), theory('equality')], [c_324, c_135])).
% 13.52/6.79  tff(c_379, plain, (![A_75, B_76]: (k3_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_136, c_327])).
% 13.52/6.79  tff(c_686, plain, (![B_91, A_92]: (k3_xboole_0(B_91, k3_xboole_0(A_92, B_91))=k3_xboole_0(B_91, A_92))), inference(superposition, [status(thm), theory('equality')], [c_159, c_379])).
% 13.52/6.79  tff(c_24, plain, (![B_22, A_21]: (k7_relat_1(B_22, k3_xboole_0(k1_relat_1(B_22), A_21))=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.52/6.79  tff(c_696, plain, (![B_22, A_92]: (k7_relat_1(B_22, k3_xboole_0(k1_relat_1(B_22), A_92))=k7_relat_1(B_22, k3_xboole_0(A_92, k1_relat_1(B_22))) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_686, c_24])).
% 13.52/6.79  tff(c_32, plain, (![A_31, B_32]: (r1_tarski(k5_relat_1(k6_relat_1(A_31), B_32), B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.52/6.79  tff(c_1352, plain, (![B_112, A_113]: (r1_tarski(k7_relat_1(B_112, A_113), B_112) | ~v1_relat_1(B_112) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_429, c_32])).
% 13.52/6.79  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.52/6.79  tff(c_1357, plain, (![B_112, A_113]: (k3_xboole_0(k7_relat_1(B_112, A_113), B_112)=k7_relat_1(B_112, A_113) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_1352, c_10])).
% 13.52/6.79  tff(c_2130, plain, (![B_139, A_140]: (k3_xboole_0(B_139, k7_relat_1(B_139, A_140))=k7_relat_1(B_139, A_140) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_1357])).
% 13.52/6.79  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.52/6.79  tff(c_2288, plain, (![B_143, A_144]: (v1_relat_1(k7_relat_1(B_143, A_144)) | ~v1_relat_1(B_143) | ~v1_relat_1(B_143))), inference(superposition, [status(thm), theory('equality')], [c_2130, c_20])).
% 13.52/6.79  tff(c_2291, plain, (![A_30, A_90]: (v1_relat_1(k7_relat_1(k6_relat_1(A_30), A_90)) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_683, c_2288])).
% 13.52/6.79  tff(c_2308, plain, (![A_30, A_90]: (v1_relat_1(k7_relat_1(k6_relat_1(A_30), A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_2291])).
% 13.52/6.79  tff(c_2208, plain, (![A_30, A_90]: (k3_xboole_0(k6_relat_1(A_30), k7_relat_1(k6_relat_1(A_30), A_90))=k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_90)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_683, c_2130])).
% 13.52/6.79  tff(c_19340, plain, (![A_358, A_359]: (k3_xboole_0(k6_relat_1(A_358), k7_relat_1(k6_relat_1(A_358), A_359))=k7_relat_1(k6_relat_1(A_358), A_359))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_683, c_2208])).
% 13.52/6.79  tff(c_40, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.52/6.79  tff(c_253, plain, (![A_64, B_65]: (r1_tarski(k5_relat_1(k6_relat_1(A_64), B_65), B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.52/6.79  tff(c_256, plain, (![A_64, B_65]: (k3_xboole_0(k5_relat_1(k6_relat_1(A_64), B_65), B_65)=k5_relat_1(k6_relat_1(A_64), B_65) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_253, c_10])).
% 13.52/6.79  tff(c_12423, plain, (![B_289, A_290]: (k3_xboole_0(B_289, k5_relat_1(k6_relat_1(A_290), B_289))=k5_relat_1(k6_relat_1(A_290), B_289) | ~v1_relat_1(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_256])).
% 13.52/6.79  tff(c_12650, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k3_xboole_0(B_37, k7_relat_1(B_37, A_36)) | ~v1_relat_1(B_37) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_40, c_12423])).
% 13.52/6.79  tff(c_19368, plain, (![A_359, A_358]: (k5_relat_1(k6_relat_1(A_359), k6_relat_1(A_358))=k7_relat_1(k6_relat_1(A_358), A_359) | ~v1_relat_1(k6_relat_1(A_358)) | ~v1_relat_1(k6_relat_1(A_358)))), inference(superposition, [status(thm), theory('equality')], [c_19340, c_12650])).
% 13.52/6.79  tff(c_19659, plain, (![A_359, A_358]: (k5_relat_1(k6_relat_1(A_359), k6_relat_1(A_358))=k7_relat_1(k6_relat_1(A_358), A_359))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_19368])).
% 13.52/6.79  tff(c_5602, plain, (![A_219, B_220]: (k7_relat_1(k6_relat_1(A_219), k3_xboole_0(B_220, A_219))=k7_relat_1(k6_relat_1(A_219), B_220))), inference(superposition, [status(thm), theory('equality')], [c_159, c_1819])).
% 13.52/6.79  tff(c_821, plain, (![C_96, A_97, B_98]: (k7_relat_1(k7_relat_1(C_96, A_97), B_98)=k7_relat_1(C_96, k3_xboole_0(A_97, B_98)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.52/6.79  tff(c_840, plain, (![B_22, A_21, B_98]: (k7_relat_1(B_22, k3_xboole_0(k3_xboole_0(k1_relat_1(B_22), A_21), B_98))=k7_relat_1(k7_relat_1(B_22, A_21), B_98) | ~v1_relat_1(B_22) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_821])).
% 13.52/6.79  tff(c_5625, plain, (![A_219, A_21]: (k7_relat_1(k6_relat_1(A_219), k3_xboole_0(k1_relat_1(k6_relat_1(A_219)), A_21))=k7_relat_1(k7_relat_1(k6_relat_1(A_219), A_21), A_219) | ~v1_relat_1(k6_relat_1(A_219)) | ~v1_relat_1(k6_relat_1(A_219)))), inference(superposition, [status(thm), theory('equality')], [c_5602, c_840])).
% 13.52/6.79  tff(c_5754, plain, (![A_219, A_21]: (k7_relat_1(k7_relat_1(k6_relat_1(A_219), A_21), A_219)=k7_relat_1(k6_relat_1(A_219), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_683, c_28, c_5625])).
% 13.52/6.79  tff(c_290, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/6.79  tff(c_2543, plain, (![A_153, B_154]: (k5_relat_1(k6_relat_1(A_153), B_154)=B_154 | ~r1_tarski(B_154, k5_relat_1(k6_relat_1(A_153), B_154)) | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_32, c_290])).
% 13.52/6.79  tff(c_21757, plain, (![A_374, B_375]: (k5_relat_1(k6_relat_1(A_374), B_375)=B_375 | ~r1_tarski(B_375, k7_relat_1(B_375, A_374)) | ~v1_relat_1(B_375) | ~v1_relat_1(B_375))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2543])).
% 13.52/6.79  tff(c_21778, plain, (![A_219, A_21]: (k5_relat_1(k6_relat_1(A_219), k7_relat_1(k6_relat_1(A_219), A_21))=k7_relat_1(k6_relat_1(A_219), A_21) | ~r1_tarski(k7_relat_1(k6_relat_1(A_219), A_21), k7_relat_1(k6_relat_1(A_219), A_21)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_219), A_21)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_219), A_21)))), inference(superposition, [status(thm), theory('equality')], [c_5754, c_21757])).
% 13.52/6.79  tff(c_21827, plain, (![A_219, A_21]: (k5_relat_1(k6_relat_1(A_219), k7_relat_1(k6_relat_1(A_219), A_21))=k7_relat_1(k6_relat_1(A_219), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2308, c_6, c_21778])).
% 13.52/6.79  tff(c_881, plain, (![A_101, B_102, C_103]: (k5_relat_1(k5_relat_1(A_101, B_102), C_103)=k5_relat_1(A_101, k5_relat_1(B_102, C_103)) | ~v1_relat_1(C_103) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.52/6.79  tff(c_891, plain, (![A_101, B_102, A_31]: (r1_tarski(k5_relat_1(A_101, k5_relat_1(B_102, k6_relat_1(A_31))), k5_relat_1(A_101, B_102)) | ~v1_relat_1(k5_relat_1(A_101, B_102)) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_881, c_34])).
% 13.52/6.79  tff(c_4944, plain, (![A_206, B_207, A_208]: (r1_tarski(k5_relat_1(A_206, k5_relat_1(B_207, k6_relat_1(A_208))), k5_relat_1(A_206, B_207)) | ~v1_relat_1(k5_relat_1(A_206, B_207)) | ~v1_relat_1(B_207) | ~v1_relat_1(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_891])).
% 13.52/6.79  tff(c_4999, plain, (![A_206, A_208, A_36]: (r1_tarski(k5_relat_1(A_206, k7_relat_1(k6_relat_1(A_208), A_36)), k5_relat_1(A_206, k6_relat_1(A_36))) | ~v1_relat_1(k5_relat_1(A_206, k6_relat_1(A_36))) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(A_206) | ~v1_relat_1(k6_relat_1(A_208)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4944])).
% 13.52/6.79  tff(c_38525, plain, (![A_489, A_490, A_491]: (r1_tarski(k5_relat_1(A_489, k7_relat_1(k6_relat_1(A_490), A_491)), k5_relat_1(A_489, k6_relat_1(A_491))) | ~v1_relat_1(k5_relat_1(A_489, k6_relat_1(A_491))) | ~v1_relat_1(A_489))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_4999])).
% 13.52/6.79  tff(c_38575, plain, (![A_219, A_21]: (r1_tarski(k7_relat_1(k6_relat_1(A_219), A_21), k5_relat_1(k6_relat_1(A_219), k6_relat_1(A_21))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_219), k6_relat_1(A_21))) | ~v1_relat_1(k6_relat_1(A_219)))), inference(superposition, [status(thm), theory('equality')], [c_21827, c_38525])).
% 13.52/6.79  tff(c_38816, plain, (![A_492, A_493]: (r1_tarski(k7_relat_1(k6_relat_1(A_492), A_493), k7_relat_1(k6_relat_1(A_493), A_492)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2308, c_19659, c_19659, c_38575])).
% 13.52/6.79  tff(c_38862, plain, (![A_92, A_493]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_92, k1_relat_1(k6_relat_1(A_493)))), A_493), k7_relat_1(k6_relat_1(A_493), k3_xboole_0(k1_relat_1(k6_relat_1(A_493)), A_92))) | ~v1_relat_1(k6_relat_1(A_493)))), inference(superposition, [status(thm), theory('equality')], [c_696, c_38816])).
% 13.52/6.79  tff(c_39807, plain, (![A_496, A_497]: (r1_tarski(k6_relat_1(k3_xboole_0(A_496, A_497)), k7_relat_1(k6_relat_1(A_496), A_497)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2404, c_683, c_28, c_28, c_38862])).
% 13.52/6.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.52/6.79  tff(c_39814, plain, (![A_496, A_497]: (k7_relat_1(k6_relat_1(A_496), A_497)=k6_relat_1(k3_xboole_0(A_496, A_497)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_496), A_497), k6_relat_1(k3_xboole_0(A_496, A_497))))), inference(resolution, [status(thm)], [c_39807, c_2])).
% 13.52/6.79  tff(c_40046, plain, (![A_496, A_497]: (k7_relat_1(k6_relat_1(A_496), A_497)=k6_relat_1(k3_xboole_0(A_496, A_497)))), inference(demodulation, [status(thm), theory('equality')], [c_678, c_39814])).
% 13.52/6.79  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.52/6.79  tff(c_450, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_429, c_46])).
% 13.52/6.79  tff(c_469, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_450])).
% 13.52/6.79  tff(c_40884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40046, c_469])).
% 13.52/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.52/6.79  
% 13.52/6.79  Inference rules
% 13.52/6.79  ----------------------
% 13.52/6.79  #Ref     : 0
% 13.52/6.79  #Sup     : 10007
% 13.52/6.79  #Fact    : 0
% 13.52/6.79  #Define  : 0
% 13.52/6.79  #Split   : 1
% 13.52/6.79  #Chain   : 0
% 13.52/6.79  #Close   : 0
% 13.52/6.79  
% 13.52/6.79  Ordering : KBO
% 13.52/6.79  
% 13.52/6.79  Simplification rules
% 13.52/6.79  ----------------------
% 13.52/6.79  #Subsume      : 1160
% 13.52/6.79  #Demod        : 12674
% 13.52/6.79  #Tautology    : 4060
% 13.52/6.79  #SimpNegUnit  : 0
% 13.52/6.79  #BackRed      : 75
% 13.52/6.79  
% 13.52/6.79  #Partial instantiations: 0
% 13.52/6.79  #Strategies tried      : 1
% 13.52/6.79  
% 13.52/6.79  Timing (in seconds)
% 13.52/6.79  ----------------------
% 13.52/6.79  Preprocessing        : 0.32
% 13.52/6.79  Parsing              : 0.17
% 13.52/6.80  CNF conversion       : 0.02
% 13.52/6.80  Main loop            : 5.69
% 13.52/6.80  Inferencing          : 1.00
% 13.52/6.80  Reduction            : 3.12
% 13.52/6.80  Demodulation         : 2.79
% 13.52/6.80  BG Simplification    : 0.15
% 13.52/6.80  Subsumption          : 1.16
% 13.52/6.80  Abstraction          : 0.28
% 13.52/6.80  MUC search           : 0.00
% 13.52/6.80  Cooper               : 0.00
% 13.52/6.80  Total                : 6.05
% 13.52/6.80  Index Insertion      : 0.00
% 13.52/6.80  Index Deletion       : 0.00
% 13.52/6.80  Index Matching       : 0.00
% 13.52/6.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
