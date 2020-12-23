%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 362 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   17
%              Number of atoms          :  137 ( 655 expanded)
%              Number of equality atoms :   46 ( 224 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

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

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_42,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_432,plain,(
    ! [B_88,A_89] :
      ( k7_relat_1(B_88,k3_xboole_0(k1_relat_1(B_88),A_89)) = k7_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_relat_1(A_66),B_67) = k7_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k5_relat_1(B_32,k6_relat_1(A_31)),B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_220,plain,(
    ! [A_31,A_66] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_66),k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_34])).

tff(c_250,plain,(
    ! [A_31,A_66] : r1_tarski(k7_relat_1(k6_relat_1(A_31),A_66),k6_relat_1(A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_220])).

tff(c_442,plain,(
    ! [A_31,A_89] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_89),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)),A_89)))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_250])).

tff(c_462,plain,(
    ! [A_31,A_89] : r1_tarski(k7_relat_1(k6_relat_1(A_31),A_89),k6_relat_1(k3_xboole_0(A_31,A_89))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_442])).

tff(c_30,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_35] :
      ( k5_relat_1(A_35,k6_relat_1(k2_relat_1(A_35))) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_228,plain,(
    ! [A_66] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66))),A_66) = k6_relat_1(A_66)
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_38])).

tff(c_254,plain,(
    ! [A_66] : k7_relat_1(k6_relat_1(A_66),A_66) = k6_relat_1(A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_30,c_228])).

tff(c_459,plain,(
    ! [A_30,A_89] :
      ( k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_89)) = k7_relat_1(k6_relat_1(A_30),A_89)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_432])).

tff(c_557,plain,(
    ! [A_98,A_99] : k7_relat_1(k6_relat_1(A_98),k3_xboole_0(A_98,A_99)) = k7_relat_1(k6_relat_1(A_98),A_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_459])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k5_relat_1(A_16,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [B_67,A_66] :
      ( v1_relat_1(k7_relat_1(B_67,A_66))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k6_relat_1(A_66))
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_20])).

tff(c_256,plain,(
    ! [B_67,A_66] :
      ( v1_relat_1(k7_relat_1(B_67,A_66))
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_234])).

tff(c_575,plain,(
    ! [A_98,A_99] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_98),A_99))
      | ~ v1_relat_1(k6_relat_1(A_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_256])).

tff(c_593,plain,(
    ! [A_98,A_99] : v1_relat_1(k7_relat_1(k6_relat_1(A_98),A_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_575])).

tff(c_467,plain,(
    ! [A_30,A_89] : k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_89)) = k7_relat_1(k6_relat_1(A_30),A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_459])).

tff(c_508,plain,(
    ! [C_95,A_96,B_97] :
      ( k7_relat_1(k7_relat_1(C_95,A_96),B_97) = k7_relat_1(C_95,k3_xboole_0(A_96,B_97))
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [C_20,A_18,B_19] :
      ( k7_relat_1(k7_relat_1(C_20,A_18),B_19) = k7_relat_1(C_20,k3_xboole_0(A_18,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4126,plain,(
    ! [C_217,A_218,B_219,B_220] :
      ( k7_relat_1(k7_relat_1(C_217,k3_xboole_0(A_218,B_219)),B_220) = k7_relat_1(k7_relat_1(C_217,A_218),k3_xboole_0(B_219,B_220))
      | ~ v1_relat_1(k7_relat_1(C_217,A_218))
      | ~ v1_relat_1(C_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_22])).

tff(c_4267,plain,(
    ! [A_30,A_89,B_220] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_30),A_30),k3_xboole_0(A_89,B_220)) = k7_relat_1(k7_relat_1(k6_relat_1(A_30),A_89),B_220)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_30),A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_4126])).

tff(c_4324,plain,(
    ! [A_30,A_89,B_220] : k7_relat_1(k7_relat_1(k6_relat_1(A_30),A_89),B_220) = k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_89,B_220)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_254,c_254,c_4267])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_105,plain,(
    ! [A_56] :
      ( k5_relat_1(A_56,k6_relat_1(k2_relat_1(A_56))) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_121,plain,(
    ! [A_30] :
      ( k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_30)) = k6_relat_1(A_30)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_129,plain,(
    ! [A_30] : k5_relat_1(k6_relat_1(A_30),k6_relat_1(A_30)) = k6_relat_1(A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_121])).

tff(c_640,plain,(
    ! [A_104,B_105,C_106] :
      ( k5_relat_1(k5_relat_1(A_104,B_105),C_106) = k5_relat_1(A_104,k5_relat_1(B_105,C_106))
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_669,plain,(
    ! [A_36,B_37,C_106] :
      ( k5_relat_1(k6_relat_1(A_36),k5_relat_1(B_37,C_106)) = k5_relat_1(k7_relat_1(B_37,A_36),C_106)
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_640])).

tff(c_2038,plain,(
    ! [A_152,B_153,C_154] :
      ( k5_relat_1(k6_relat_1(A_152),k5_relat_1(B_153,C_154)) = k5_relat_1(k7_relat_1(B_153,A_152),C_154)
      | ~ v1_relat_1(C_154)
      | ~ v1_relat_1(B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_669])).

tff(c_2110,plain,(
    ! [A_30,A_152] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_30),A_152),k6_relat_1(A_30)) = k5_relat_1(k6_relat_1(A_152),k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2038])).

tff(c_2135,plain,(
    ! [A_30,A_152] : k5_relat_1(k7_relat_1(k6_relat_1(A_30),A_152),k6_relat_1(A_30)) = k5_relat_1(k6_relat_1(A_152),k6_relat_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_2110])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,k3_xboole_0(k1_relat_1(B_22),A_21)) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5182,plain,(
    ! [A_238,A_239] : k5_relat_1(k7_relat_1(k6_relat_1(A_238),A_239),k6_relat_1(A_238)) = k5_relat_1(k6_relat_1(A_239),k6_relat_1(A_238)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_2110])).

tff(c_5251,plain,(
    ! [A_238,A_21] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_238)),A_21)),k6_relat_1(A_238)) = k5_relat_1(k7_relat_1(k6_relat_1(A_238),A_21),k6_relat_1(A_238))
      | ~ v1_relat_1(k6_relat_1(A_238)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5182])).

tff(c_6744,plain,(
    ! [A_268,A_269] : k5_relat_1(k6_relat_1(k3_xboole_0(A_268,A_269)),k6_relat_1(A_268)) = k5_relat_1(k6_relat_1(A_269),k6_relat_1(A_268)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2135,c_28,c_5251])).

tff(c_6861,plain,(
    ! [A_268,A_269] :
      ( k7_relat_1(k6_relat_1(A_268),k3_xboole_0(A_268,A_269)) = k5_relat_1(k6_relat_1(A_269),k6_relat_1(A_268))
      | ~ v1_relat_1(k6_relat_1(A_268)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6744])).

tff(c_6911,plain,(
    ! [A_269,A_268] : k5_relat_1(k6_relat_1(A_269),k6_relat_1(A_268)) = k7_relat_1(k6_relat_1(A_268),A_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_467,c_6861])).

tff(c_6997,plain,(
    ! [A_272,A_273] : k5_relat_1(k6_relat_1(A_272),k6_relat_1(A_273)) = k7_relat_1(k6_relat_1(A_273),A_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_467,c_6861])).

tff(c_650,plain,(
    ! [A_104,B_105,A_31] :
      ( r1_tarski(k5_relat_1(A_104,k5_relat_1(B_105,k6_relat_1(A_31))),k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_34])).

tff(c_682,plain,(
    ! [A_104,B_105,A_31] :
      ( r1_tarski(k5_relat_1(A_104,k5_relat_1(B_105,k6_relat_1(A_31))),k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_650])).

tff(c_7027,plain,(
    ! [A_272,A_273,A_31] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_272),k5_relat_1(k6_relat_1(A_273),k6_relat_1(A_31))),k7_relat_1(k6_relat_1(A_273),A_272))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_272),k6_relat_1(A_273)))
      | ~ v1_relat_1(k6_relat_1(A_273))
      | ~ v1_relat_1(k6_relat_1(A_272)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_682])).

tff(c_7933,plain,(
    ! [A_286,A_287,A_288] : r1_tarski(k5_relat_1(k6_relat_1(A_286),k7_relat_1(k6_relat_1(A_287),A_288)),k7_relat_1(k6_relat_1(A_288),A_286)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_593,c_6911,c_6911,c_7027])).

tff(c_8032,plain,(
    ! [A_287,A_288,A_36] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_287),A_288),A_36),k7_relat_1(k6_relat_1(A_288),A_36))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_287),A_288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7933])).

tff(c_8064,plain,(
    ! [A_289,A_290,A_291] : r1_tarski(k7_relat_1(k6_relat_1(A_289),k3_xboole_0(A_290,A_291)),k7_relat_1(k6_relat_1(A_290),A_291)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_4324,c_8032])).

tff(c_8219,plain,(
    ! [A_292,A_293] : r1_tarski(k6_relat_1(k3_xboole_0(A_292,A_293)),k7_relat_1(k6_relat_1(A_292),A_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_8064])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8226,plain,(
    ! [A_292,A_293] :
      ( k7_relat_1(k6_relat_1(A_292),A_293) = k6_relat_1(k3_xboole_0(A_292,A_293))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_292),A_293),k6_relat_1(k3_xboole_0(A_292,A_293))) ) ),
    inference(resolution,[status(thm)],[c_8219,c_2])).

tff(c_8315,plain,(
    ! [A_292,A_293] : k7_relat_1(k6_relat_1(A_292),A_293) = k6_relat_1(k3_xboole_0(A_292,A_293)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_8226])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_237,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_46])).

tff(c_258,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_237])).

tff(c_8612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8315,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.32  
% 6.04/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.04/2.33  
% 6.04/2.33  %Foreground sorts:
% 6.04/2.33  
% 6.04/2.33  
% 6.04/2.33  %Background operators:
% 6.04/2.33  
% 6.04/2.33  
% 6.04/2.33  %Foreground operators:
% 6.04/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.04/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.04/2.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.04/2.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.04/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.04/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.04/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.04/2.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.04/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.04/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.04/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.04/2.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.04/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.04/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.04/2.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.04/2.33  
% 6.04/2.34  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.04/2.34  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.04/2.34  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 6.04/2.34  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.04/2.34  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 6.04/2.34  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.04/2.34  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.04/2.34  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 6.04/2.34  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.04/2.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.04/2.34  tff(f_98, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.04/2.34  tff(c_42, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.04/2.34  tff(c_28, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.04/2.34  tff(c_432, plain, (![B_88, A_89]: (k7_relat_1(B_88, k3_xboole_0(k1_relat_1(B_88), A_89))=k7_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.34  tff(c_213, plain, (![A_66, B_67]: (k5_relat_1(k6_relat_1(A_66), B_67)=k7_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.04/2.34  tff(c_34, plain, (![B_32, A_31]: (r1_tarski(k5_relat_1(B_32, k6_relat_1(A_31)), B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.04/2.34  tff(c_220, plain, (![A_31, A_66]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_66), k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_34])).
% 6.04/2.34  tff(c_250, plain, (![A_31, A_66]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_66), k6_relat_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_220])).
% 6.04/2.34  tff(c_442, plain, (![A_31, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_89), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)), A_89))) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_432, c_250])).
% 6.04/2.34  tff(c_462, plain, (![A_31, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_89), k6_relat_1(k3_xboole_0(A_31, A_89))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_442])).
% 6.04/2.34  tff(c_30, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.04/2.34  tff(c_38, plain, (![A_35]: (k5_relat_1(A_35, k6_relat_1(k2_relat_1(A_35)))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.04/2.34  tff(c_228, plain, (![A_66]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66))), A_66)=k6_relat_1(A_66) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_66)))))), inference(superposition, [status(thm), theory('equality')], [c_213, c_38])).
% 6.04/2.34  tff(c_254, plain, (![A_66]: (k7_relat_1(k6_relat_1(A_66), A_66)=k6_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_30, c_228])).
% 6.04/2.34  tff(c_459, plain, (![A_30, A_89]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_89))=k7_relat_1(k6_relat_1(A_30), A_89) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_432])).
% 6.04/2.34  tff(c_557, plain, (![A_98, A_99]: (k7_relat_1(k6_relat_1(A_98), k3_xboole_0(A_98, A_99))=k7_relat_1(k6_relat_1(A_98), A_99))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_459])).
% 6.04/2.34  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k5_relat_1(A_16, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.04/2.34  tff(c_234, plain, (![B_67, A_66]: (v1_relat_1(k7_relat_1(B_67, A_66)) | ~v1_relat_1(B_67) | ~v1_relat_1(k6_relat_1(A_66)) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_213, c_20])).
% 6.04/2.34  tff(c_256, plain, (![B_67, A_66]: (v1_relat_1(k7_relat_1(B_67, A_66)) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_234])).
% 6.04/2.34  tff(c_575, plain, (![A_98, A_99]: (v1_relat_1(k7_relat_1(k6_relat_1(A_98), A_99)) | ~v1_relat_1(k6_relat_1(A_98)))), inference(superposition, [status(thm), theory('equality')], [c_557, c_256])).
% 6.04/2.34  tff(c_593, plain, (![A_98, A_99]: (v1_relat_1(k7_relat_1(k6_relat_1(A_98), A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_575])).
% 6.04/2.34  tff(c_467, plain, (![A_30, A_89]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_89))=k7_relat_1(k6_relat_1(A_30), A_89))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_459])).
% 6.04/2.34  tff(c_508, plain, (![C_95, A_96, B_97]: (k7_relat_1(k7_relat_1(C_95, A_96), B_97)=k7_relat_1(C_95, k3_xboole_0(A_96, B_97)) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.04/2.34  tff(c_22, plain, (![C_20, A_18, B_19]: (k7_relat_1(k7_relat_1(C_20, A_18), B_19)=k7_relat_1(C_20, k3_xboole_0(A_18, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.04/2.34  tff(c_4126, plain, (![C_217, A_218, B_219, B_220]: (k7_relat_1(k7_relat_1(C_217, k3_xboole_0(A_218, B_219)), B_220)=k7_relat_1(k7_relat_1(C_217, A_218), k3_xboole_0(B_219, B_220)) | ~v1_relat_1(k7_relat_1(C_217, A_218)) | ~v1_relat_1(C_217))), inference(superposition, [status(thm), theory('equality')], [c_508, c_22])).
% 6.04/2.34  tff(c_4267, plain, (![A_30, A_89, B_220]: (k7_relat_1(k7_relat_1(k6_relat_1(A_30), A_30), k3_xboole_0(A_89, B_220))=k7_relat_1(k7_relat_1(k6_relat_1(A_30), A_89), B_220) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_30), A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_467, c_4126])).
% 6.04/2.34  tff(c_4324, plain, (![A_30, A_89, B_220]: (k7_relat_1(k7_relat_1(k6_relat_1(A_30), A_89), B_220)=k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_89, B_220)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_254, c_254, c_4267])).
% 6.04/2.34  tff(c_40, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.04/2.34  tff(c_105, plain, (![A_56]: (k5_relat_1(A_56, k6_relat_1(k2_relat_1(A_56)))=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.04/2.34  tff(c_121, plain, (![A_30]: (k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_30))=k6_relat_1(A_30) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_105])).
% 6.04/2.34  tff(c_129, plain, (![A_30]: (k5_relat_1(k6_relat_1(A_30), k6_relat_1(A_30))=k6_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_121])).
% 6.04/2.34  tff(c_640, plain, (![A_104, B_105, C_106]: (k5_relat_1(k5_relat_1(A_104, B_105), C_106)=k5_relat_1(A_104, k5_relat_1(B_105, C_106)) | ~v1_relat_1(C_106) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.04/2.34  tff(c_669, plain, (![A_36, B_37, C_106]: (k5_relat_1(k6_relat_1(A_36), k5_relat_1(B_37, C_106))=k5_relat_1(k7_relat_1(B_37, A_36), C_106) | ~v1_relat_1(C_106) | ~v1_relat_1(B_37) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_40, c_640])).
% 6.04/2.34  tff(c_2038, plain, (![A_152, B_153, C_154]: (k5_relat_1(k6_relat_1(A_152), k5_relat_1(B_153, C_154))=k5_relat_1(k7_relat_1(B_153, A_152), C_154) | ~v1_relat_1(C_154) | ~v1_relat_1(B_153))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_669])).
% 6.04/2.34  tff(c_2110, plain, (![A_30, A_152]: (k5_relat_1(k7_relat_1(k6_relat_1(A_30), A_152), k6_relat_1(A_30))=k5_relat_1(k6_relat_1(A_152), k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2038])).
% 6.04/2.34  tff(c_2135, plain, (![A_30, A_152]: (k5_relat_1(k7_relat_1(k6_relat_1(A_30), A_152), k6_relat_1(A_30))=k5_relat_1(k6_relat_1(A_152), k6_relat_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_2110])).
% 6.04/2.34  tff(c_24, plain, (![B_22, A_21]: (k7_relat_1(B_22, k3_xboole_0(k1_relat_1(B_22), A_21))=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.04/2.34  tff(c_5182, plain, (![A_238, A_239]: (k5_relat_1(k7_relat_1(k6_relat_1(A_238), A_239), k6_relat_1(A_238))=k5_relat_1(k6_relat_1(A_239), k6_relat_1(A_238)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_2110])).
% 6.04/2.34  tff(c_5251, plain, (![A_238, A_21]: (k5_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_238)), A_21)), k6_relat_1(A_238))=k5_relat_1(k7_relat_1(k6_relat_1(A_238), A_21), k6_relat_1(A_238)) | ~v1_relat_1(k6_relat_1(A_238)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5182])).
% 6.04/2.34  tff(c_6744, plain, (![A_268, A_269]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_268, A_269)), k6_relat_1(A_268))=k5_relat_1(k6_relat_1(A_269), k6_relat_1(A_268)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2135, c_28, c_5251])).
% 6.04/2.34  tff(c_6861, plain, (![A_268, A_269]: (k7_relat_1(k6_relat_1(A_268), k3_xboole_0(A_268, A_269))=k5_relat_1(k6_relat_1(A_269), k6_relat_1(A_268)) | ~v1_relat_1(k6_relat_1(A_268)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6744])).
% 6.04/2.34  tff(c_6911, plain, (![A_269, A_268]: (k5_relat_1(k6_relat_1(A_269), k6_relat_1(A_268))=k7_relat_1(k6_relat_1(A_268), A_269))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_467, c_6861])).
% 6.04/2.34  tff(c_6997, plain, (![A_272, A_273]: (k5_relat_1(k6_relat_1(A_272), k6_relat_1(A_273))=k7_relat_1(k6_relat_1(A_273), A_272))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_467, c_6861])).
% 6.04/2.34  tff(c_650, plain, (![A_104, B_105, A_31]: (r1_tarski(k5_relat_1(A_104, k5_relat_1(B_105, k6_relat_1(A_31))), k5_relat_1(A_104, B_105)) | ~v1_relat_1(k5_relat_1(A_104, B_105)) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_640, c_34])).
% 6.04/2.34  tff(c_682, plain, (![A_104, B_105, A_31]: (r1_tarski(k5_relat_1(A_104, k5_relat_1(B_105, k6_relat_1(A_31))), k5_relat_1(A_104, B_105)) | ~v1_relat_1(k5_relat_1(A_104, B_105)) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_650])).
% 6.04/2.34  tff(c_7027, plain, (![A_272, A_273, A_31]: (r1_tarski(k5_relat_1(k6_relat_1(A_272), k5_relat_1(k6_relat_1(A_273), k6_relat_1(A_31))), k7_relat_1(k6_relat_1(A_273), A_272)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_272), k6_relat_1(A_273))) | ~v1_relat_1(k6_relat_1(A_273)) | ~v1_relat_1(k6_relat_1(A_272)))), inference(superposition, [status(thm), theory('equality')], [c_6997, c_682])).
% 6.04/2.34  tff(c_7933, plain, (![A_286, A_287, A_288]: (r1_tarski(k5_relat_1(k6_relat_1(A_286), k7_relat_1(k6_relat_1(A_287), A_288)), k7_relat_1(k6_relat_1(A_288), A_286)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_593, c_6911, c_6911, c_7027])).
% 6.04/2.34  tff(c_8032, plain, (![A_287, A_288, A_36]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_287), A_288), A_36), k7_relat_1(k6_relat_1(A_288), A_36)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_287), A_288)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_7933])).
% 6.04/2.34  tff(c_8064, plain, (![A_289, A_290, A_291]: (r1_tarski(k7_relat_1(k6_relat_1(A_289), k3_xboole_0(A_290, A_291)), k7_relat_1(k6_relat_1(A_290), A_291)))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_4324, c_8032])).
% 6.04/2.34  tff(c_8219, plain, (![A_292, A_293]: (r1_tarski(k6_relat_1(k3_xboole_0(A_292, A_293)), k7_relat_1(k6_relat_1(A_292), A_293)))), inference(superposition, [status(thm), theory('equality')], [c_254, c_8064])).
% 6.04/2.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.04/2.34  tff(c_8226, plain, (![A_292, A_293]: (k7_relat_1(k6_relat_1(A_292), A_293)=k6_relat_1(k3_xboole_0(A_292, A_293)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_292), A_293), k6_relat_1(k3_xboole_0(A_292, A_293))))), inference(resolution, [status(thm)], [c_8219, c_2])).
% 6.04/2.34  tff(c_8315, plain, (![A_292, A_293]: (k7_relat_1(k6_relat_1(A_292), A_293)=k6_relat_1(k3_xboole_0(A_292, A_293)))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_8226])).
% 6.04/2.34  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.04/2.34  tff(c_237, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_46])).
% 6.04/2.34  tff(c_258, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_237])).
% 6.04/2.34  tff(c_8612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8315, c_258])).
% 6.04/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.34  
% 6.04/2.34  Inference rules
% 6.04/2.34  ----------------------
% 6.04/2.34  #Ref     : 0
% 6.04/2.34  #Sup     : 1975
% 6.04/2.34  #Fact    : 0
% 6.04/2.34  #Define  : 0
% 6.04/2.34  #Split   : 1
% 6.04/2.34  #Chain   : 0
% 6.04/2.34  #Close   : 0
% 6.04/2.34  
% 6.04/2.34  Ordering : KBO
% 6.04/2.34  
% 6.04/2.34  Simplification rules
% 6.04/2.34  ----------------------
% 6.04/2.34  #Subsume      : 165
% 6.04/2.34  #Demod        : 2453
% 6.04/2.34  #Tautology    : 926
% 6.04/2.34  #SimpNegUnit  : 0
% 6.04/2.34  #BackRed      : 45
% 6.04/2.34  
% 6.04/2.34  #Partial instantiations: 0
% 6.04/2.34  #Strategies tried      : 1
% 6.04/2.34  
% 6.04/2.34  Timing (in seconds)
% 6.04/2.34  ----------------------
% 6.04/2.34  Preprocessing        : 0.33
% 6.04/2.34  Parsing              : 0.18
% 6.04/2.34  CNF conversion       : 0.02
% 6.04/2.34  Main loop            : 1.19
% 6.04/2.34  Inferencing          : 0.40
% 6.04/2.34  Reduction            : 0.47
% 6.04/2.34  Demodulation         : 0.37
% 6.04/2.34  BG Simplification    : 0.05
% 6.04/2.34  Subsumption          : 0.20
% 6.04/2.34  Abstraction          : 0.08
% 6.04/2.34  MUC search           : 0.00
% 6.04/2.35  Cooper               : 0.00
% 6.04/2.35  Total                : 1.55
% 6.04/2.35  Index Insertion      : 0.00
% 6.04/2.35  Index Deletion       : 0.00
% 6.04/2.35  Index Matching       : 0.00
% 6.04/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
