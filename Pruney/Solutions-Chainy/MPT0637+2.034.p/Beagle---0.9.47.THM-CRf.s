%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:28 EST 2020

% Result     : Theorem 19.53s
% Output     : CNFRefutation 19.53s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 332 expanded)
%              Number of leaves         :   35 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 595 expanded)
%              Number of equality atoms :   52 ( 198 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_46,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_413,plain,(
    ! [A_80,B_81] :
      ( k5_relat_1(k6_relat_1(A_80),B_81) = k7_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    ! [A_35] :
      ( k5_relat_1(A_35,k6_relat_1(k2_relat_1(A_35))) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_434,plain,(
    ! [A_80] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))),A_80) = k6_relat_1(A_80)
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_38])).

tff(c_456,plain,(
    ! [A_80] : k7_relat_1(k6_relat_1(A_80),A_80) = k6_relat_1(A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_30,c_434])).

tff(c_1440,plain,(
    ! [C_125,A_126,B_127] :
      ( k7_relat_1(k7_relat_1(C_125,A_126),B_127) = k7_relat_1(C_125,k3_xboole_0(A_126,B_127))
      | ~ v1_relat_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1478,plain,(
    ! [A_80,B_127] :
      ( k7_relat_1(k6_relat_1(A_80),k3_xboole_0(A_80,B_127)) = k7_relat_1(k6_relat_1(A_80),B_127)
      | ~ v1_relat_1(k6_relat_1(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_1440])).

tff(c_2519,plain,(
    ! [A_152,B_153] : k7_relat_1(k6_relat_1(A_152),k3_xboole_0(A_152,B_153)) = k7_relat_1(k6_relat_1(A_152),B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1478])).

tff(c_34,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k5_relat_1(B_32,k6_relat_1(A_31)),B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_426,plain,(
    ! [A_31,A_80] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_80),k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_34])).

tff(c_452,plain,(
    ! [A_31,A_80] : r1_tarski(k7_relat_1(k6_relat_1(A_31),A_80),k6_relat_1(A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_426])).

tff(c_2543,plain,(
    ! [A_152,B_153] : r1_tarski(k7_relat_1(k6_relat_1(A_152),B_153),k6_relat_1(k3_xboole_0(A_152,B_153))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_452])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_231,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_237,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,k3_xboole_0(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_14])).

tff(c_248,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_237])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3098,plain,(
    ! [B_170,A_171] : k7_relat_1(k6_relat_1(B_170),k3_xboole_0(A_171,B_170)) = k7_relat_1(k6_relat_1(B_170),A_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2519])).

tff(c_3199,plain,(
    ! [A_70,B_71] : k7_relat_1(k6_relat_1(k3_xboole_0(A_70,B_71)),k3_xboole_0(A_70,B_71)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_70,B_71)),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_3098])).

tff(c_3239,plain,(
    ! [A_70,B_71] : k7_relat_1(k6_relat_1(k3_xboole_0(A_70,B_71)),A_70) = k6_relat_1(k3_xboole_0(A_70,B_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_3199])).

tff(c_1484,plain,(
    ! [A_80,B_127] : k7_relat_1(k6_relat_1(A_80),k3_xboole_0(A_80,B_127)) = k7_relat_1(k6_relat_1(A_80),B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1478])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k5_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_419,plain,(
    ! [B_81,A_80] :
      ( v1_relat_1(k7_relat_1(B_81,A_80))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_22])).

tff(c_450,plain,(
    ! [B_81,A_80] :
      ( v1_relat_1(k7_relat_1(B_81,A_80))
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_419])).

tff(c_2546,plain,(
    ! [A_152,B_153] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_152),B_153))
      | ~ v1_relat_1(k6_relat_1(A_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_450])).

tff(c_2610,plain,(
    ! [A_152,B_153] : v1_relat_1(k7_relat_1(k6_relat_1(A_152),B_153)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2546])).

tff(c_141,plain,(
    ! [A_58] :
      ( k5_relat_1(A_58,k6_relat_1(k2_relat_1(A_58))) = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_150,plain,(
    ! [A_30] :
      ( k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_30)) = k6_relat_1(A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_141])).

tff(c_154,plain,(
    ! [A_30] : k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_30)) = k6_relat_1(A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_150])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_relat_1(A_38),B_39) = k7_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1646,plain,(
    ! [A_130,B_131,C_132] :
      ( k5_relat_1(k5_relat_1(A_130,B_131),C_132) = k5_relat_1(A_130,k5_relat_1(B_131,C_132))
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1675,plain,(
    ! [A_38,B_39,C_132] :
      ( k5_relat_1(k6_relat_1(A_38),k5_relat_1(B_39,C_132)) = k5_relat_1(k7_relat_1(B_39,A_38),C_132)
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1646])).

tff(c_6328,plain,(
    ! [A_213,B_214,C_215] :
      ( k5_relat_1(k6_relat_1(A_213),k5_relat_1(B_214,C_215)) = k5_relat_1(k7_relat_1(B_214,A_213),C_215)
      | ~ v1_relat_1(C_215)
      | ~ v1_relat_1(B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1675])).

tff(c_6403,plain,(
    ! [A_30,A_213] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_30),A_213),k6_relat_1(A_30)) = k5_relat_1(k6_relat_1(A_213),k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_6328])).

tff(c_6428,plain,(
    ! [A_30,A_213] : k5_relat_1(k7_relat_1(k6_relat_1(A_30),A_213),k6_relat_1(A_30)) = k5_relat_1(k6_relat_1(A_213),k6_relat_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_6403])).

tff(c_59604,plain,(
    ! [B_660,C_661,A_662] :
      ( k7_relat_1(k5_relat_1(B_660,C_661),A_662) = k5_relat_1(k7_relat_1(B_660,A_662),C_661)
      | ~ v1_relat_1(k5_relat_1(B_660,C_661))
      | ~ v1_relat_1(C_661)
      | ~ v1_relat_1(B_660) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6328,c_42])).

tff(c_59680,plain,(
    ! [A_30,A_662] :
      ( k7_relat_1(k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_30)),A_662) = k5_relat_1(k7_relat_1(k6_relat_1(A_30),A_662),k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_59604])).

tff(c_59750,plain,(
    ! [A_662,A_30] : k5_relat_1(k6_relat_1(A_662),k6_relat_1(A_30)) = k7_relat_1(k6_relat_1(A_30),A_662) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_46,c_6428,c_154,c_59680])).

tff(c_28,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_653,plain,(
    ! [B_105,A_106] :
      ( k3_xboole_0(k1_relat_1(B_105),A_106) = k1_relat_1(k7_relat_1(B_105,A_106))
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1867,plain,(
    ! [B_135,A_136] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_135,A_136)),k1_relat_1(B_135))
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_10])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( k5_relat_1(k6_relat_1(A_33),B_34) = B_34
      | ~ r1_tarski(k1_relat_1(B_34),A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1900,plain,(
    ! [B_135,A_136] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_135)),k7_relat_1(B_135,A_136)) = k7_relat_1(B_135,A_136)
      | ~ v1_relat_1(k7_relat_1(B_135,A_136))
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_1867,c_36])).

tff(c_1659,plain,(
    ! [A_130,B_131,A_31] :
      ( r1_tarski(k5_relat_1(A_130,k5_relat_1(B_131,k6_relat_1(A_31))),k5_relat_1(A_130,B_131))
      | ~ v1_relat_1(k5_relat_1(A_130,B_131))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_34])).

tff(c_7440,plain,(
    ! [A_233,B_234,A_235] :
      ( r1_tarski(k5_relat_1(A_233,k5_relat_1(B_234,k6_relat_1(A_235))),k5_relat_1(A_233,B_234))
      | ~ v1_relat_1(k5_relat_1(A_233,B_234))
      | ~ v1_relat_1(B_234)
      | ~ v1_relat_1(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1659])).

tff(c_7502,plain,(
    ! [A_233,A_235,A_38] :
      ( r1_tarski(k5_relat_1(A_233,k7_relat_1(k6_relat_1(A_235),A_38)),k5_relat_1(A_233,k6_relat_1(A_38)))
      | ~ v1_relat_1(k5_relat_1(A_233,k6_relat_1(A_38)))
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(A_233)
      | ~ v1_relat_1(k6_relat_1(A_235)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7440])).

tff(c_62678,plain,(
    ! [A_677,A_678,A_679] :
      ( r1_tarski(k5_relat_1(A_677,k7_relat_1(k6_relat_1(A_678),A_679)),k5_relat_1(A_677,k6_relat_1(A_679)))
      | ~ v1_relat_1(k5_relat_1(A_677,k6_relat_1(A_679)))
      | ~ v1_relat_1(A_677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_7502])).

tff(c_62701,plain,(
    ! [A_678,A_136] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_678),A_136),k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_678))),k6_relat_1(A_136)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_678))),k6_relat_1(A_136)))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_678))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_678),A_136))
      | ~ v1_relat_1(k6_relat_1(A_678)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_62678])).

tff(c_62945,plain,(
    ! [A_680,A_681] : r1_tarski(k7_relat_1(k6_relat_1(A_680),A_681),k7_relat_1(k6_relat_1(A_681),A_680)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2610,c_46,c_2610,c_59750,c_28,c_59750,c_28,c_62701])).

tff(c_63095,plain,(
    ! [A_80,B_127] : r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_80,B_127)),A_80),k7_relat_1(k6_relat_1(A_80),B_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1484,c_62945])).

tff(c_65411,plain,(
    ! [A_689,B_690] : r1_tarski(k6_relat_1(k3_xboole_0(A_689,B_690)),k7_relat_1(k6_relat_1(A_689),B_690)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3239,c_63095])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65423,plain,(
    ! [A_689,B_690] :
      ( k7_relat_1(k6_relat_1(A_689),B_690) = k6_relat_1(k3_xboole_0(A_689,B_690))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_689),B_690),k6_relat_1(k3_xboole_0(A_689,B_690))) ) ),
    inference(resolution,[status(thm)],[c_65411,c_4])).

tff(c_65670,plain,(
    ! [A_689,B_690] : k7_relat_1(k6_relat_1(A_689),B_690) = k6_relat_1(k3_xboole_0(A_689,B_690)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2543,c_65423])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_437,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_50])).

tff(c_458,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_437])).

tff(c_65780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65670,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.53/11.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.53/11.64  
% 19.53/11.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.53/11.64  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 19.53/11.64  
% 19.53/11.64  %Foreground sorts:
% 19.53/11.64  
% 19.53/11.64  
% 19.53/11.64  %Background operators:
% 19.53/11.64  
% 19.53/11.64  
% 19.53/11.64  %Foreground operators:
% 19.53/11.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.53/11.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.53/11.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.53/11.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.53/11.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.53/11.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.53/11.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.53/11.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.53/11.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.53/11.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.53/11.64  tff('#skF_2', type, '#skF_2': $i).
% 19.53/11.64  tff('#skF_1', type, '#skF_1': $i).
% 19.53/11.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.53/11.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.53/11.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 19.53/11.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.53/11.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.53/11.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.53/11.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.53/11.64  
% 19.53/11.66  tff(f_103, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 19.53/11.66  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 19.53/11.66  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 19.53/11.66  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 19.53/11.66  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 19.53/11.66  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 19.53/11.66  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.53/11.66  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 19.53/11.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.53/11.66  tff(f_51, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 19.53/11.66  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 19.53/11.66  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 19.53/11.66  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 19.53/11.66  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 19.53/11.66  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.53/11.66  tff(f_106, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 19.53/11.66  tff(c_46, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.53/11.66  tff(c_30, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_69])).
% 19.53/11.66  tff(c_413, plain, (![A_80, B_81]: (k5_relat_1(k6_relat_1(A_80), B_81)=k7_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.53/11.66  tff(c_38, plain, (![A_35]: (k5_relat_1(A_35, k6_relat_1(k2_relat_1(A_35)))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.53/11.66  tff(c_434, plain, (![A_80]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))), A_80)=k6_relat_1(A_80) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))))), inference(superposition, [status(thm), theory('equality')], [c_413, c_38])).
% 19.53/11.66  tff(c_456, plain, (![A_80]: (k7_relat_1(k6_relat_1(A_80), A_80)=k6_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_30, c_434])).
% 19.53/11.66  tff(c_1440, plain, (![C_125, A_126, B_127]: (k7_relat_1(k7_relat_1(C_125, A_126), B_127)=k7_relat_1(C_125, k3_xboole_0(A_126, B_127)) | ~v1_relat_1(C_125))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.53/11.66  tff(c_1478, plain, (![A_80, B_127]: (k7_relat_1(k6_relat_1(A_80), k3_xboole_0(A_80, B_127))=k7_relat_1(k6_relat_1(A_80), B_127) | ~v1_relat_1(k6_relat_1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_456, c_1440])).
% 19.53/11.66  tff(c_2519, plain, (![A_152, B_153]: (k7_relat_1(k6_relat_1(A_152), k3_xboole_0(A_152, B_153))=k7_relat_1(k6_relat_1(A_152), B_153))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1478])).
% 19.53/11.66  tff(c_34, plain, (![B_32, A_31]: (r1_tarski(k5_relat_1(B_32, k6_relat_1(A_31)), B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.53/11.66  tff(c_426, plain, (![A_31, A_80]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_80), k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_413, c_34])).
% 19.53/11.66  tff(c_452, plain, (![A_31, A_80]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_80), k6_relat_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_426])).
% 19.53/11.66  tff(c_2543, plain, (![A_152, B_153]: (r1_tarski(k7_relat_1(k6_relat_1(A_152), B_153), k6_relat_1(k3_xboole_0(A_152, B_153))))), inference(superposition, [status(thm), theory('equality')], [c_2519, c_452])).
% 19.53/11.66  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.53/11.66  tff(c_231, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.53/11.66  tff(c_237, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, k3_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_14])).
% 19.53/11.66  tff(c_248, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_237])).
% 19.53/11.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.53/11.66  tff(c_3098, plain, (![B_170, A_171]: (k7_relat_1(k6_relat_1(B_170), k3_xboole_0(A_171, B_170))=k7_relat_1(k6_relat_1(B_170), A_171))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2519])).
% 19.53/11.66  tff(c_3199, plain, (![A_70, B_71]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_70, B_71)), k3_xboole_0(A_70, B_71))=k7_relat_1(k6_relat_1(k3_xboole_0(A_70, B_71)), A_70))), inference(superposition, [status(thm), theory('equality')], [c_248, c_3098])).
% 19.53/11.66  tff(c_3239, plain, (![A_70, B_71]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_70, B_71)), A_70)=k6_relat_1(k3_xboole_0(A_70, B_71)))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_3199])).
% 19.53/11.66  tff(c_1484, plain, (![A_80, B_127]: (k7_relat_1(k6_relat_1(A_80), k3_xboole_0(A_80, B_127))=k7_relat_1(k6_relat_1(A_80), B_127))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1478])).
% 19.53/11.66  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k5_relat_1(A_18, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.53/11.66  tff(c_419, plain, (![B_81, A_80]: (v1_relat_1(k7_relat_1(B_81, A_80)) | ~v1_relat_1(B_81) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_413, c_22])).
% 19.53/11.66  tff(c_450, plain, (![B_81, A_80]: (v1_relat_1(k7_relat_1(B_81, A_80)) | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_419])).
% 19.53/11.66  tff(c_2546, plain, (![A_152, B_153]: (v1_relat_1(k7_relat_1(k6_relat_1(A_152), B_153)) | ~v1_relat_1(k6_relat_1(A_152)))), inference(superposition, [status(thm), theory('equality')], [c_2519, c_450])).
% 19.53/11.66  tff(c_2610, plain, (![A_152, B_153]: (v1_relat_1(k7_relat_1(k6_relat_1(A_152), B_153)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2546])).
% 19.53/11.66  tff(c_141, plain, (![A_58]: (k5_relat_1(A_58, k6_relat_1(k2_relat_1(A_58)))=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.53/11.66  tff(c_150, plain, (![A_30]: (k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_30))=k6_relat_1(A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_141])).
% 19.53/11.66  tff(c_154, plain, (![A_30]: (k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_30))=k6_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_150])).
% 19.53/11.66  tff(c_42, plain, (![A_38, B_39]: (k5_relat_1(k6_relat_1(A_38), B_39)=k7_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.53/11.66  tff(c_1646, plain, (![A_130, B_131, C_132]: (k5_relat_1(k5_relat_1(A_130, B_131), C_132)=k5_relat_1(A_130, k5_relat_1(B_131, C_132)) | ~v1_relat_1(C_132) | ~v1_relat_1(B_131) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.53/11.66  tff(c_1675, plain, (![A_38, B_39, C_132]: (k5_relat_1(k6_relat_1(A_38), k5_relat_1(B_39, C_132))=k5_relat_1(k7_relat_1(B_39, A_38), C_132) | ~v1_relat_1(C_132) | ~v1_relat_1(B_39) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1646])).
% 19.53/11.66  tff(c_6328, plain, (![A_213, B_214, C_215]: (k5_relat_1(k6_relat_1(A_213), k5_relat_1(B_214, C_215))=k5_relat_1(k7_relat_1(B_214, A_213), C_215) | ~v1_relat_1(C_215) | ~v1_relat_1(B_214))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1675])).
% 19.53/11.66  tff(c_6403, plain, (![A_30, A_213]: (k5_relat_1(k7_relat_1(k6_relat_1(A_30), A_213), k6_relat_1(A_30))=k5_relat_1(k6_relat_1(A_213), k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_6328])).
% 19.53/11.66  tff(c_6428, plain, (![A_30, A_213]: (k5_relat_1(k7_relat_1(k6_relat_1(A_30), A_213), k6_relat_1(A_30))=k5_relat_1(k6_relat_1(A_213), k6_relat_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_6403])).
% 19.53/11.66  tff(c_59604, plain, (![B_660, C_661, A_662]: (k7_relat_1(k5_relat_1(B_660, C_661), A_662)=k5_relat_1(k7_relat_1(B_660, A_662), C_661) | ~v1_relat_1(k5_relat_1(B_660, C_661)) | ~v1_relat_1(C_661) | ~v1_relat_1(B_660))), inference(superposition, [status(thm), theory('equality')], [c_6328, c_42])).
% 19.53/11.66  tff(c_59680, plain, (![A_30, A_662]: (k7_relat_1(k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_30)), A_662)=k5_relat_1(k7_relat_1(k6_relat_1(A_30), A_662), k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_59604])).
% 19.53/11.66  tff(c_59750, plain, (![A_662, A_30]: (k5_relat_1(k6_relat_1(A_662), k6_relat_1(A_30))=k7_relat_1(k6_relat_1(A_30), A_662))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_46, c_6428, c_154, c_59680])).
% 19.53/11.66  tff(c_28, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_69])).
% 19.53/11.66  tff(c_653, plain, (![B_105, A_106]: (k3_xboole_0(k1_relat_1(B_105), A_106)=k1_relat_1(k7_relat_1(B_105, A_106)) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_89])).
% 19.53/11.66  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.53/11.66  tff(c_1867, plain, (![B_135, A_136]: (r1_tarski(k1_relat_1(k7_relat_1(B_135, A_136)), k1_relat_1(B_135)) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_653, c_10])).
% 19.53/11.66  tff(c_36, plain, (![A_33, B_34]: (k5_relat_1(k6_relat_1(A_33), B_34)=B_34 | ~r1_tarski(k1_relat_1(B_34), A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.53/11.66  tff(c_1900, plain, (![B_135, A_136]: (k5_relat_1(k6_relat_1(k1_relat_1(B_135)), k7_relat_1(B_135, A_136))=k7_relat_1(B_135, A_136) | ~v1_relat_1(k7_relat_1(B_135, A_136)) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_1867, c_36])).
% 19.53/11.66  tff(c_1659, plain, (![A_130, B_131, A_31]: (r1_tarski(k5_relat_1(A_130, k5_relat_1(B_131, k6_relat_1(A_31))), k5_relat_1(A_130, B_131)) | ~v1_relat_1(k5_relat_1(A_130, B_131)) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_131) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_34])).
% 19.53/11.66  tff(c_7440, plain, (![A_233, B_234, A_235]: (r1_tarski(k5_relat_1(A_233, k5_relat_1(B_234, k6_relat_1(A_235))), k5_relat_1(A_233, B_234)) | ~v1_relat_1(k5_relat_1(A_233, B_234)) | ~v1_relat_1(B_234) | ~v1_relat_1(A_233))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1659])).
% 19.53/11.66  tff(c_7502, plain, (![A_233, A_235, A_38]: (r1_tarski(k5_relat_1(A_233, k7_relat_1(k6_relat_1(A_235), A_38)), k5_relat_1(A_233, k6_relat_1(A_38))) | ~v1_relat_1(k5_relat_1(A_233, k6_relat_1(A_38))) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(A_233) | ~v1_relat_1(k6_relat_1(A_235)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_7440])).
% 19.53/11.66  tff(c_62678, plain, (![A_677, A_678, A_679]: (r1_tarski(k5_relat_1(A_677, k7_relat_1(k6_relat_1(A_678), A_679)), k5_relat_1(A_677, k6_relat_1(A_679))) | ~v1_relat_1(k5_relat_1(A_677, k6_relat_1(A_679))) | ~v1_relat_1(A_677))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_7502])).
% 19.53/11.66  tff(c_62701, plain, (![A_678, A_136]: (r1_tarski(k7_relat_1(k6_relat_1(A_678), A_136), k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_678))), k6_relat_1(A_136))) | ~v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_678))), k6_relat_1(A_136))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_678)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_678), A_136)) | ~v1_relat_1(k6_relat_1(A_678)))), inference(superposition, [status(thm), theory('equality')], [c_1900, c_62678])).
% 19.53/11.66  tff(c_62945, plain, (![A_680, A_681]: (r1_tarski(k7_relat_1(k6_relat_1(A_680), A_681), k7_relat_1(k6_relat_1(A_681), A_680)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2610, c_46, c_2610, c_59750, c_28, c_59750, c_28, c_62701])).
% 19.53/11.66  tff(c_63095, plain, (![A_80, B_127]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_80, B_127)), A_80), k7_relat_1(k6_relat_1(A_80), B_127)))), inference(superposition, [status(thm), theory('equality')], [c_1484, c_62945])).
% 19.53/11.66  tff(c_65411, plain, (![A_689, B_690]: (r1_tarski(k6_relat_1(k3_xboole_0(A_689, B_690)), k7_relat_1(k6_relat_1(A_689), B_690)))), inference(demodulation, [status(thm), theory('equality')], [c_3239, c_63095])).
% 19.53/11.66  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.53/11.66  tff(c_65423, plain, (![A_689, B_690]: (k7_relat_1(k6_relat_1(A_689), B_690)=k6_relat_1(k3_xboole_0(A_689, B_690)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_689), B_690), k6_relat_1(k3_xboole_0(A_689, B_690))))), inference(resolution, [status(thm)], [c_65411, c_4])).
% 19.53/11.66  tff(c_65670, plain, (![A_689, B_690]: (k7_relat_1(k6_relat_1(A_689), B_690)=k6_relat_1(k3_xboole_0(A_689, B_690)))), inference(demodulation, [status(thm), theory('equality')], [c_2543, c_65423])).
% 19.53/11.66  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 19.53/11.66  tff(c_437, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_413, c_50])).
% 19.53/11.66  tff(c_458, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_437])).
% 19.53/11.66  tff(c_65780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65670, c_458])).
% 19.53/11.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.53/11.66  
% 19.53/11.66  Inference rules
% 19.53/11.66  ----------------------
% 19.53/11.66  #Ref     : 0
% 19.53/11.66  #Sup     : 17113
% 19.53/11.66  #Fact    : 0
% 19.53/11.66  #Define  : 0
% 19.53/11.66  #Split   : 1
% 19.53/11.66  #Chain   : 0
% 19.53/11.66  #Close   : 0
% 19.53/11.66  
% 19.53/11.66  Ordering : KBO
% 19.53/11.66  
% 19.53/11.66  Simplification rules
% 19.53/11.66  ----------------------
% 19.53/11.66  #Subsume      : 1848
% 19.53/11.66  #Demod        : 16408
% 19.53/11.66  #Tautology    : 5888
% 19.53/11.66  #SimpNegUnit  : 0
% 19.53/11.66  #BackRed      : 65
% 19.53/11.66  
% 19.53/11.66  #Partial instantiations: 0
% 19.53/11.66  #Strategies tried      : 1
% 19.53/11.66  
% 19.53/11.66  Timing (in seconds)
% 19.53/11.66  ----------------------
% 19.53/11.66  Preprocessing        : 0.35
% 19.53/11.66  Parsing              : 0.19
% 19.53/11.66  CNF conversion       : 0.02
% 19.53/11.66  Main loop            : 10.49
% 19.53/11.66  Inferencing          : 1.49
% 19.53/11.66  Reduction            : 6.00
% 19.53/11.66  Demodulation         : 5.46
% 19.53/11.66  BG Simplification    : 0.24
% 19.53/11.66  Subsumption          : 2.26
% 19.53/11.66  Abstraction          : 0.39
% 19.53/11.66  MUC search           : 0.00
% 19.53/11.66  Cooper               : 0.00
% 19.53/11.66  Total                : 10.88
% 19.53/11.66  Index Insertion      : 0.00
% 19.53/11.66  Index Deletion       : 0.00
% 19.53/11.66  Index Matching       : 0.00
% 19.53/11.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
