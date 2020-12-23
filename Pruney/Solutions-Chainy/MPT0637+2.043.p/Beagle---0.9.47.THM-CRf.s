%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 23.28s
% Output     : CNFRefutation 23.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 194 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  132 ( 345 expanded)
%              Number of equality atoms :   47 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [B_40,A_41] : r1_tarski(k3_xboole_0(B_40,A_41),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_4])).

tff(c_34,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_52] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_52)),A_52) = A_52
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_23)) = k6_relat_1(A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_141])).

tff(c_154,plain,(
    ! [A_23] : k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_23)) = k6_relat_1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_150])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( k5_relat_1(k6_relat_1(A_31),B_32) = k7_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_484,plain,(
    ! [A_86,B_87,C_88] :
      ( k5_relat_1(k5_relat_1(A_86,B_87),C_88) = k5_relat_1(A_86,k5_relat_1(B_87,C_88))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_514,plain,(
    ! [A_31,B_32,C_88] :
      ( k5_relat_1(k6_relat_1(A_31),k5_relat_1(B_32,C_88)) = k5_relat_1(k7_relat_1(B_32,A_31),C_88)
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_484])).

tff(c_1731,plain,(
    ! [A_133,B_134,C_135] :
      ( k5_relat_1(k6_relat_1(A_133),k5_relat_1(B_134,C_135)) = k5_relat_1(k7_relat_1(B_134,A_133),C_135)
      | ~ v1_relat_1(C_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_514])).

tff(c_1791,plain,(
    ! [A_23,A_133] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_23),A_133),k6_relat_1(A_23)) = k5_relat_1(k6_relat_1(A_133),k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_1731])).

tff(c_1818,plain,(
    ! [A_23,A_133] : k5_relat_1(k7_relat_1(k6_relat_1(A_23),A_133),k6_relat_1(A_23)) = k5_relat_1(k6_relat_1(A_133),k6_relat_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_1791])).

tff(c_17631,plain,(
    ! [B_397,C_398,A_399] :
      ( k7_relat_1(k5_relat_1(B_397,C_398),A_399) = k5_relat_1(k7_relat_1(B_397,A_399),C_398)
      | ~ v1_relat_1(k5_relat_1(B_397,C_398))
      | ~ v1_relat_1(C_398)
      | ~ v1_relat_1(B_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1731,c_32])).

tff(c_17675,plain,(
    ! [A_23,A_399] :
      ( k7_relat_1(k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_23)),A_399) = k5_relat_1(k7_relat_1(k6_relat_1(A_23),A_399),k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_17631])).

tff(c_17721,plain,(
    ! [A_399,A_23] : k5_relat_1(k6_relat_1(A_399),k6_relat_1(A_23)) = k7_relat_1(k6_relat_1(A_23),A_399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_34,c_1818,c_154,c_17675])).

tff(c_20,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_377,plain,(
    ! [B_80,A_81] :
      ( k5_relat_1(B_80,k6_relat_1(A_81)) = B_80
      | ~ r1_tarski(k2_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_384,plain,(
    ! [A_23,A_81] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_81)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_81)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_377])).

tff(c_740,plain,(
    ! [A_99,A_100] :
      ( k5_relat_1(k6_relat_1(A_99),k6_relat_1(A_100)) = k6_relat_1(A_99)
      | ~ r1_tarski(A_99,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_384])).

tff(c_753,plain,(
    ! [A_100,A_99] :
      ( k7_relat_1(k6_relat_1(A_100),A_99) = k6_relat_1(A_99)
      | ~ v1_relat_1(k6_relat_1(A_100))
      | ~ r1_tarski(A_99,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_32])).

tff(c_796,plain,(
    ! [A_100,A_99] :
      ( k7_relat_1(k6_relat_1(A_100),A_99) = k6_relat_1(A_99)
      | ~ r1_tarski(A_99,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_753])).

tff(c_1784,plain,(
    ! [A_31,A_133,B_32] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_31),A_133),B_32) = k5_relat_1(k6_relat_1(A_133),k7_relat_1(B_32,A_31))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1731])).

tff(c_8992,plain,(
    ! [A_242,A_243,B_244] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_242),A_243),B_244) = k5_relat_1(k6_relat_1(A_243),k7_relat_1(B_244,A_242))
      | ~ v1_relat_1(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1784])).

tff(c_63443,plain,(
    ! [A_1001,B_1002,A_1003] :
      ( k5_relat_1(k6_relat_1(A_1001),k7_relat_1(B_1002,A_1003)) = k5_relat_1(k6_relat_1(A_1001),B_1002)
      | ~ v1_relat_1(B_1002)
      | ~ r1_tarski(A_1001,A_1003) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_8992])).

tff(c_212,plain,(
    ! [A_65,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),B_66) = k7_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k5_relat_1(B_25,k6_relat_1(A_24)),B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_222,plain,(
    ! [A_24,A_65] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_24),A_65),k6_relat_1(A_65))
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_24])).

tff(c_245,plain,(
    ! [A_24,A_65] : r1_tarski(k7_relat_1(k6_relat_1(A_24),A_65),k6_relat_1(A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_222])).

tff(c_835,plain,(
    ! [A_105,A_106] :
      ( k7_relat_1(k6_relat_1(A_105),A_106) = k6_relat_1(A_106)
      | ~ r1_tarski(A_106,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_753])).

tff(c_262,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(k1_relat_1(B_68),A_69) = k1_relat_1(k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_271,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(k1_relat_1(k7_relat_1(B_68,A_69)))
      | ~ v1_relat_1(k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_14])).

tff(c_841,plain,(
    ! [A_106,A_105] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(A_106)))
      | ~ v1_relat_1(k1_relat_1(k6_relat_1(A_105)))
      | ~ v1_relat_1(k6_relat_1(A_105))
      | ~ r1_tarski(A_106,A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_271])).

tff(c_911,plain,(
    ! [A_107,A_108] :
      ( v1_relat_1(A_107)
      | ~ v1_relat_1(A_108)
      | ~ r1_tarski(A_107,A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18,c_18,c_841])).

tff(c_932,plain,(
    ! [A_24,A_65] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_24),A_65))
      | ~ v1_relat_1(k6_relat_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_245,c_911])).

tff(c_955,plain,(
    ! [A_24,A_65] : v1_relat_1(k7_relat_1(k6_relat_1(A_24),A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_932])).

tff(c_297,plain,(
    ! [A_23,A_69] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_23),A_69)) = k3_xboole_0(A_23,A_69)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_262])).

tff(c_308,plain,(
    ! [A_72,A_73] : k1_relat_1(k7_relat_1(k6_relat_1(A_72),A_73)) = k3_xboole_0(A_72,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_297])).

tff(c_26,plain,(
    ! [A_26] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_26)),A_26) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_317,plain,(
    ! [A_72,A_73] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_72,A_73)),k7_relat_1(k6_relat_1(A_72),A_73)) = k7_relat_1(k6_relat_1(A_72),A_73)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_72),A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_26])).

tff(c_20190,plain,(
    ! [A_72,A_73] : k5_relat_1(k6_relat_1(k3_xboole_0(A_72,A_73)),k7_relat_1(k6_relat_1(A_72),A_73)) = k7_relat_1(k6_relat_1(A_72),A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_317])).

tff(c_63656,plain,(
    ! [A_72,A_1003] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_72,A_1003)),k6_relat_1(A_72)) = k7_relat_1(k6_relat_1(A_72),A_1003)
      | ~ v1_relat_1(k6_relat_1(A_72))
      | ~ r1_tarski(k3_xboole_0(A_72,A_1003),A_1003) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63443,c_20190])).

tff(c_63927,plain,(
    ! [A_1004,A_1005] : k7_relat_1(k6_relat_1(A_1004),k3_xboole_0(A_1004,A_1005)) = k7_relat_1(k6_relat_1(A_1004),A_1005) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_34,c_17721,c_63656])).

tff(c_64133,plain,(
    ! [A_1004,A_1005] :
      ( k7_relat_1(k6_relat_1(A_1004),A_1005) = k6_relat_1(k3_xboole_0(A_1004,A_1005))
      | ~ r1_tarski(k3_xboole_0(A_1004,A_1005),A_1004) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63927,c_796])).

tff(c_64360,plain,(
    ! [A_1004,A_1005] : k7_relat_1(k6_relat_1(A_1004),A_1005) = k6_relat_1(k3_xboole_0(A_1004,A_1005)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64133])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_233,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_38])).

tff(c_249,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_233])).

tff(c_64478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64360,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.28/14.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.37/14.42  
% 23.37/14.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.37/14.42  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 23.37/14.42  
% 23.37/14.42  %Foreground sorts:
% 23.37/14.42  
% 23.37/14.42  
% 23.37/14.42  %Background operators:
% 23.37/14.42  
% 23.37/14.42  
% 23.37/14.42  %Foreground operators:
% 23.37/14.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.37/14.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.37/14.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.37/14.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.37/14.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 23.37/14.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.37/14.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.37/14.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.37/14.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.37/14.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.37/14.42  tff('#skF_2', type, '#skF_2': $i).
% 23.37/14.42  tff('#skF_1', type, '#skF_1': $i).
% 23.37/14.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.37/14.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.37/14.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 23.37/14.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.37/14.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.37/14.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.37/14.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.37/14.42  
% 23.37/14.43  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 23.37/14.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.37/14.43  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 23.37/14.43  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 23.37/14.43  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 23.37/14.43  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 23.37/14.43  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 23.37/14.43  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 23.37/14.43  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 23.37/14.43  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 23.37/14.43  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 23.37/14.43  tff(f_86, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 23.37/14.43  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.37/14.43  tff(c_60, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.37/14.43  tff(c_75, plain, (![B_40, A_41]: (r1_tarski(k3_xboole_0(B_40, A_41), A_41))), inference(superposition, [status(thm), theory('equality')], [c_60, c_4])).
% 23.37/14.43  tff(c_34, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.37/14.43  tff(c_18, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.37/14.43  tff(c_141, plain, (![A_52]: (k5_relat_1(k6_relat_1(k1_relat_1(A_52)), A_52)=A_52 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.37/14.43  tff(c_150, plain, (![A_23]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_23))=k6_relat_1(A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_141])).
% 23.37/14.43  tff(c_154, plain, (![A_23]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_23))=k6_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_150])).
% 23.37/14.43  tff(c_32, plain, (![A_31, B_32]: (k5_relat_1(k6_relat_1(A_31), B_32)=k7_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_79])).
% 23.37/14.43  tff(c_484, plain, (![A_86, B_87, C_88]: (k5_relat_1(k5_relat_1(A_86, B_87), C_88)=k5_relat_1(A_86, k5_relat_1(B_87, C_88)) | ~v1_relat_1(C_88) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.37/14.43  tff(c_514, plain, (![A_31, B_32, C_88]: (k5_relat_1(k6_relat_1(A_31), k5_relat_1(B_32, C_88))=k5_relat_1(k7_relat_1(B_32, A_31), C_88) | ~v1_relat_1(C_88) | ~v1_relat_1(B_32) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_32, c_484])).
% 23.37/14.43  tff(c_1731, plain, (![A_133, B_134, C_135]: (k5_relat_1(k6_relat_1(A_133), k5_relat_1(B_134, C_135))=k5_relat_1(k7_relat_1(B_134, A_133), C_135) | ~v1_relat_1(C_135) | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_514])).
% 23.37/14.43  tff(c_1791, plain, (![A_23, A_133]: (k5_relat_1(k7_relat_1(k6_relat_1(A_23), A_133), k6_relat_1(A_23))=k5_relat_1(k6_relat_1(A_133), k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_1731])).
% 23.37/14.43  tff(c_1818, plain, (![A_23, A_133]: (k5_relat_1(k7_relat_1(k6_relat_1(A_23), A_133), k6_relat_1(A_23))=k5_relat_1(k6_relat_1(A_133), k6_relat_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_1791])).
% 23.37/14.43  tff(c_17631, plain, (![B_397, C_398, A_399]: (k7_relat_1(k5_relat_1(B_397, C_398), A_399)=k5_relat_1(k7_relat_1(B_397, A_399), C_398) | ~v1_relat_1(k5_relat_1(B_397, C_398)) | ~v1_relat_1(C_398) | ~v1_relat_1(B_397))), inference(superposition, [status(thm), theory('equality')], [c_1731, c_32])).
% 23.37/14.43  tff(c_17675, plain, (![A_23, A_399]: (k7_relat_1(k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_23)), A_399)=k5_relat_1(k7_relat_1(k6_relat_1(A_23), A_399), k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_17631])).
% 23.37/14.43  tff(c_17721, plain, (![A_399, A_23]: (k5_relat_1(k6_relat_1(A_399), k6_relat_1(A_23))=k7_relat_1(k6_relat_1(A_23), A_399))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_34, c_1818, c_154, c_17675])).
% 23.37/14.43  tff(c_20, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.37/14.43  tff(c_377, plain, (![B_80, A_81]: (k5_relat_1(B_80, k6_relat_1(A_81))=B_80 | ~r1_tarski(k2_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 23.37/14.43  tff(c_384, plain, (![A_23, A_81]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_81))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_81) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_377])).
% 23.37/14.43  tff(c_740, plain, (![A_99, A_100]: (k5_relat_1(k6_relat_1(A_99), k6_relat_1(A_100))=k6_relat_1(A_99) | ~r1_tarski(A_99, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_384])).
% 23.37/14.43  tff(c_753, plain, (![A_100, A_99]: (k7_relat_1(k6_relat_1(A_100), A_99)=k6_relat_1(A_99) | ~v1_relat_1(k6_relat_1(A_100)) | ~r1_tarski(A_99, A_100))), inference(superposition, [status(thm), theory('equality')], [c_740, c_32])).
% 23.37/14.43  tff(c_796, plain, (![A_100, A_99]: (k7_relat_1(k6_relat_1(A_100), A_99)=k6_relat_1(A_99) | ~r1_tarski(A_99, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_753])).
% 23.37/14.43  tff(c_1784, plain, (![A_31, A_133, B_32]: (k5_relat_1(k7_relat_1(k6_relat_1(A_31), A_133), B_32)=k5_relat_1(k6_relat_1(A_133), k7_relat_1(B_32, A_31)) | ~v1_relat_1(B_32) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1731])).
% 23.37/14.43  tff(c_8992, plain, (![A_242, A_243, B_244]: (k5_relat_1(k7_relat_1(k6_relat_1(A_242), A_243), B_244)=k5_relat_1(k6_relat_1(A_243), k7_relat_1(B_244, A_242)) | ~v1_relat_1(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1784])).
% 23.37/14.43  tff(c_63443, plain, (![A_1001, B_1002, A_1003]: (k5_relat_1(k6_relat_1(A_1001), k7_relat_1(B_1002, A_1003))=k5_relat_1(k6_relat_1(A_1001), B_1002) | ~v1_relat_1(B_1002) | ~r1_tarski(A_1001, A_1003))), inference(superposition, [status(thm), theory('equality')], [c_796, c_8992])).
% 23.37/14.43  tff(c_212, plain, (![A_65, B_66]: (k5_relat_1(k6_relat_1(A_65), B_66)=k7_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 23.37/14.43  tff(c_24, plain, (![B_25, A_24]: (r1_tarski(k5_relat_1(B_25, k6_relat_1(A_24)), B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.37/14.43  tff(c_222, plain, (![A_24, A_65]: (r1_tarski(k7_relat_1(k6_relat_1(A_24), A_65), k6_relat_1(A_65)) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_24])).
% 23.37/14.43  tff(c_245, plain, (![A_24, A_65]: (r1_tarski(k7_relat_1(k6_relat_1(A_24), A_65), k6_relat_1(A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_222])).
% 23.37/14.43  tff(c_835, plain, (![A_105, A_106]: (k7_relat_1(k6_relat_1(A_105), A_106)=k6_relat_1(A_106) | ~r1_tarski(A_106, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_753])).
% 23.37/14.43  tff(c_262, plain, (![B_68, A_69]: (k3_xboole_0(k1_relat_1(B_68), A_69)=k1_relat_1(k7_relat_1(B_68, A_69)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.37/14.43  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k3_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.37/14.43  tff(c_271, plain, (![B_68, A_69]: (v1_relat_1(k1_relat_1(k7_relat_1(B_68, A_69))) | ~v1_relat_1(k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_262, c_14])).
% 23.37/14.43  tff(c_841, plain, (![A_106, A_105]: (v1_relat_1(k1_relat_1(k6_relat_1(A_106))) | ~v1_relat_1(k1_relat_1(k6_relat_1(A_105))) | ~v1_relat_1(k6_relat_1(A_105)) | ~r1_tarski(A_106, A_105))), inference(superposition, [status(thm), theory('equality')], [c_835, c_271])).
% 23.37/14.43  tff(c_911, plain, (![A_107, A_108]: (v1_relat_1(A_107) | ~v1_relat_1(A_108) | ~r1_tarski(A_107, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18, c_18, c_841])).
% 23.37/14.43  tff(c_932, plain, (![A_24, A_65]: (v1_relat_1(k7_relat_1(k6_relat_1(A_24), A_65)) | ~v1_relat_1(k6_relat_1(A_65)))), inference(resolution, [status(thm)], [c_245, c_911])).
% 23.37/14.43  tff(c_955, plain, (![A_24, A_65]: (v1_relat_1(k7_relat_1(k6_relat_1(A_24), A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_932])).
% 23.37/14.43  tff(c_297, plain, (![A_23, A_69]: (k1_relat_1(k7_relat_1(k6_relat_1(A_23), A_69))=k3_xboole_0(A_23, A_69) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_262])).
% 23.37/14.43  tff(c_308, plain, (![A_72, A_73]: (k1_relat_1(k7_relat_1(k6_relat_1(A_72), A_73))=k3_xboole_0(A_72, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_297])).
% 23.37/14.43  tff(c_26, plain, (![A_26]: (k5_relat_1(k6_relat_1(k1_relat_1(A_26)), A_26)=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.37/14.43  tff(c_317, plain, (![A_72, A_73]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_72, A_73)), k7_relat_1(k6_relat_1(A_72), A_73))=k7_relat_1(k6_relat_1(A_72), A_73) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_72), A_73)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_26])).
% 23.37/14.43  tff(c_20190, plain, (![A_72, A_73]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_72, A_73)), k7_relat_1(k6_relat_1(A_72), A_73))=k7_relat_1(k6_relat_1(A_72), A_73))), inference(demodulation, [status(thm), theory('equality')], [c_955, c_317])).
% 23.37/14.43  tff(c_63656, plain, (![A_72, A_1003]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_72, A_1003)), k6_relat_1(A_72))=k7_relat_1(k6_relat_1(A_72), A_1003) | ~v1_relat_1(k6_relat_1(A_72)) | ~r1_tarski(k3_xboole_0(A_72, A_1003), A_1003))), inference(superposition, [status(thm), theory('equality')], [c_63443, c_20190])).
% 23.37/14.44  tff(c_63927, plain, (![A_1004, A_1005]: (k7_relat_1(k6_relat_1(A_1004), k3_xboole_0(A_1004, A_1005))=k7_relat_1(k6_relat_1(A_1004), A_1005))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_34, c_17721, c_63656])).
% 23.37/14.44  tff(c_64133, plain, (![A_1004, A_1005]: (k7_relat_1(k6_relat_1(A_1004), A_1005)=k6_relat_1(k3_xboole_0(A_1004, A_1005)) | ~r1_tarski(k3_xboole_0(A_1004, A_1005), A_1004))), inference(superposition, [status(thm), theory('equality')], [c_63927, c_796])).
% 23.37/14.44  tff(c_64360, plain, (![A_1004, A_1005]: (k7_relat_1(k6_relat_1(A_1004), A_1005)=k6_relat_1(k3_xboole_0(A_1004, A_1005)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64133])).
% 23.37/14.44  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.37/14.44  tff(c_233, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_38])).
% 23.37/14.44  tff(c_249, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_233])).
% 23.37/14.44  tff(c_64478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64360, c_249])).
% 23.37/14.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.37/14.44  
% 23.37/14.44  Inference rules
% 23.37/14.44  ----------------------
% 23.37/14.44  #Ref     : 0
% 23.37/14.44  #Sup     : 15580
% 23.37/14.44  #Fact    : 0
% 23.37/14.44  #Define  : 0
% 23.37/14.44  #Split   : 1
% 23.37/14.44  #Chain   : 0
% 23.37/14.44  #Close   : 0
% 23.37/14.44  
% 23.37/14.44  Ordering : KBO
% 23.37/14.44  
% 23.37/14.44  Simplification rules
% 23.37/14.44  ----------------------
% 23.37/14.44  #Subsume      : 1902
% 23.37/14.44  #Demod        : 14866
% 23.37/14.44  #Tautology    : 5071
% 23.37/14.44  #SimpNegUnit  : 0
% 23.37/14.44  #BackRed      : 81
% 23.37/14.44  
% 23.37/14.44  #Partial instantiations: 0
% 23.37/14.44  #Strategies tried      : 1
% 23.37/14.44  
% 23.37/14.44  Timing (in seconds)
% 23.37/14.44  ----------------------
% 23.37/14.44  Preprocessing        : 0.32
% 23.37/14.44  Parsing              : 0.18
% 23.37/14.44  CNF conversion       : 0.02
% 23.37/14.44  Main loop            : 13.29
% 23.37/14.44  Inferencing          : 1.98
% 23.37/14.44  Reduction            : 7.79
% 23.37/14.44  Demodulation         : 7.17
% 23.37/14.44  BG Simplification    : 0.32
% 23.37/14.44  Subsumption          : 2.70
% 23.37/14.44  Abstraction          : 0.54
% 23.37/14.44  MUC search           : 0.00
% 23.37/14.44  Cooper               : 0.00
% 23.37/14.44  Total                : 13.65
% 23.37/14.44  Index Insertion      : 0.00
% 23.37/14.44  Index Deletion       : 0.00
% 23.37/14.44  Index Matching       : 0.00
% 23.37/14.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
