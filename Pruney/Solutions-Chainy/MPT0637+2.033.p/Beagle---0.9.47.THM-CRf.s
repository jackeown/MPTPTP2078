%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:28 EST 2020

% Result     : Theorem 15.29s
% Output     : CNFRefutation 15.33s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 275 expanded)
%              Number of leaves         :   30 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          :  172 ( 454 expanded)
%              Number of equality atoms :   58 ( 159 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

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

tff(f_85,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_411,plain,(
    ! [B_84,A_85] :
      ( k7_relat_1(B_84,k3_xboole_0(k1_relat_1(B_84),A_85)) = k7_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_207,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(k6_relat_1(A_61),B_62) = k7_relat_1(B_62,A_61)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k5_relat_1(B_31,k6_relat_1(A_30)),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_217,plain,(
    ! [A_30,A_61] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_30),A_61),k6_relat_1(A_61))
      | ~ v1_relat_1(k6_relat_1(A_61))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_34])).

tff(c_246,plain,(
    ! [A_30,A_61] : r1_tarski(k7_relat_1(k6_relat_1(A_30),A_61),k6_relat_1(A_61)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_217])).

tff(c_425,plain,(
    ! [A_30,A_85] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_30),A_85),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)),A_85)))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_246])).

tff(c_464,plain,(
    ! [A_88,A_89] : r1_tarski(k7_relat_1(k6_relat_1(A_88),A_89),k6_relat_1(k3_xboole_0(A_88,A_89))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28,c_425])).

tff(c_486,plain,(
    ! [B_2,A_1] : r1_tarski(k7_relat_1(k6_relat_1(B_2),A_1),k6_relat_1(k3_xboole_0(A_1,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_464])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_10])).

tff(c_30,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_316,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_319,plain,(
    ! [A_29,A_78] :
      ( k7_relat_1(k6_relat_1(A_29),A_78) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_78)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_316])).

tff(c_325,plain,(
    ! [A_29,A_78] :
      ( k7_relat_1(k6_relat_1(A_29),A_78) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_319])).

tff(c_473,plain,(
    ! [A_29,A_78] :
      ( r1_tarski(k6_relat_1(A_29),k6_relat_1(k3_xboole_0(A_29,A_78)))
      | ~ r1_tarski(A_29,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_464])).

tff(c_354,plain,(
    ! [A_80,A_81] :
      ( k7_relat_1(k6_relat_1(A_80),A_81) = k6_relat_1(A_80)
      | ~ r1_tarski(A_80,A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_319])).

tff(c_406,plain,(
    ! [A_82,A_83] :
      ( r1_tarski(k6_relat_1(A_82),k6_relat_1(A_83))
      | ~ r1_tarski(A_82,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_246])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1209,plain,(
    ! [A_133,A_132] :
      ( k6_relat_1(A_133) = k6_relat_1(A_132)
      | ~ r1_tarski(k6_relat_1(A_132),k6_relat_1(A_133))
      | ~ r1_tarski(A_133,A_132) ) ),
    inference(resolution,[status(thm)],[c_406,c_4])).

tff(c_1218,plain,(
    ! [A_29,A_78] :
      ( k6_relat_1(k3_xboole_0(A_29,A_78)) = k6_relat_1(A_29)
      | ~ r1_tarski(k3_xboole_0(A_29,A_78),A_29)
      | ~ r1_tarski(A_29,A_78) ) ),
    inference(resolution,[status(thm)],[c_473,c_1209])).

tff(c_1475,plain,(
    ! [A_136,A_137] :
      ( k6_relat_1(k3_xboole_0(A_136,A_137)) = k6_relat_1(A_136)
      | ~ r1_tarski(A_136,A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1218])).

tff(c_1575,plain,(
    ! [A_136,A_137] :
      ( k3_xboole_0(A_136,A_137) = k2_relat_1(k6_relat_1(A_136))
      | ~ r1_tarski(A_136,A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1475,c_30])).

tff(c_1609,plain,(
    ! [A_138,A_139] :
      ( k3_xboole_0(A_138,A_139) = A_138
      | ~ r1_tarski(A_138,A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1575])).

tff(c_1874,plain,(
    ! [B_145,A_146] : k3_xboole_0(k3_xboole_0(B_145,A_146),A_146) = k3_xboole_0(B_145,A_146) ),
    inference(resolution,[status(thm)],[c_80,c_1609])).

tff(c_418,plain,(
    ! [A_29,A_85] :
      ( k7_relat_1(k6_relat_1(A_29),A_85) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,k3_xboole_0(k1_relat_1(k6_relat_1(A_29)),A_85))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_325])).

tff(c_449,plain,(
    ! [A_29,A_85] :
      ( k7_relat_1(k6_relat_1(A_29),A_85) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,k3_xboole_0(A_29,A_85)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28,c_418])).

tff(c_1899,plain,(
    ! [B_145,A_146] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(B_145,A_146)),A_146) = k6_relat_1(k3_xboole_0(B_145,A_146))
      | ~ r1_tarski(k3_xboole_0(B_145,A_146),k3_xboole_0(B_145,A_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_449])).

tff(c_1989,plain,(
    ! [B_145,A_146] : k7_relat_1(k6_relat_1(k3_xboole_0(B_145,A_146)),A_146) = k6_relat_1(k3_xboole_0(B_145,A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1899])).

tff(c_443,plain,(
    ! [B_84,A_1] :
      ( k7_relat_1(B_84,k3_xboole_0(A_1,k1_relat_1(B_84))) = k7_relat_1(B_84,A_1)
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_411])).

tff(c_446,plain,(
    ! [A_29,A_85] :
      ( k7_relat_1(k6_relat_1(A_29),k3_xboole_0(A_29,A_85)) = k7_relat_1(k6_relat_1(A_29),A_85)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_411])).

tff(c_640,plain,(
    ! [A_101,A_102] : k7_relat_1(k6_relat_1(A_101),k3_xboole_0(A_101,A_102)) = k7_relat_1(k6_relat_1(A_101),A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_446])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k5_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_213,plain,(
    ! [B_62,A_61] :
      ( v1_relat_1(k7_relat_1(B_62,A_61))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k6_relat_1(A_61))
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_18])).

tff(c_244,plain,(
    ! [B_62,A_61] :
      ( v1_relat_1(k7_relat_1(B_62,A_61))
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_213])).

tff(c_664,plain,(
    ! [A_101,A_102] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_101),A_102))
      | ~ v1_relat_1(k6_relat_1(A_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_244])).

tff(c_686,plain,(
    ! [A_101,A_102] : v1_relat_1(k7_relat_1(k6_relat_1(A_101),A_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_664])).

tff(c_456,plain,(
    ! [A_29,A_85] : k7_relat_1(k6_relat_1(A_29),k3_xboole_0(A_29,A_85)) = k7_relat_1(k6_relat_1(A_29),A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_446])).

tff(c_674,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),k3_xboole_0(B_2,A_1)) = k7_relat_1(k6_relat_1(A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_640])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,k3_xboole_0(k1_relat_1(B_21),A_20)) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_492,plain,(
    ! [C_90,A_91,B_92] :
      ( k7_relat_1(k7_relat_1(C_90,A_91),B_92) = k7_relat_1(C_90,k3_xboole_0(A_91,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2489,plain,(
    ! [B_155,A_156,B_157] :
      ( k7_relat_1(B_155,k3_xboole_0(k3_xboole_0(k1_relat_1(B_155),A_156),B_157)) = k7_relat_1(k7_relat_1(B_155,A_156),B_157)
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_492])).

tff(c_2587,plain,(
    ! [A_1,A_156] :
      ( k7_relat_1(k6_relat_1(A_1),k3_xboole_0(k1_relat_1(k6_relat_1(A_1)),A_156)) = k7_relat_1(k7_relat_1(k6_relat_1(A_1),A_156),A_1)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_2489])).

tff(c_2632,plain,(
    ! [A_1,A_156] : k7_relat_1(k7_relat_1(k6_relat_1(A_1),A_156),A_1) = k7_relat_1(k6_relat_1(A_1),A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_456,c_28,c_2587])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( k5_relat_1(k6_relat_1(A_33),B_34) = k7_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_30),B_31),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_177,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_992,plain,(
    ! [A_121,B_122] :
      ( k5_relat_1(k6_relat_1(A_121),B_122) = B_122
      | ~ r1_tarski(B_122,k5_relat_1(k6_relat_1(A_121),B_122))
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_17770,plain,(
    ! [A_346,B_347] :
      ( k5_relat_1(k6_relat_1(A_346),B_347) = B_347
      | ~ r1_tarski(B_347,k7_relat_1(B_347,A_346))
      | ~ v1_relat_1(B_347)
      | ~ v1_relat_1(B_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_992])).

tff(c_17806,plain,(
    ! [A_1,A_156] :
      ( k5_relat_1(k6_relat_1(A_1),k7_relat_1(k6_relat_1(A_1),A_156)) = k7_relat_1(k6_relat_1(A_1),A_156)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_1),A_156),k7_relat_1(k6_relat_1(A_1),A_156))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_1),A_156))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_1),A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2632,c_17770])).

tff(c_17859,plain,(
    ! [A_1,A_156] : k5_relat_1(k6_relat_1(A_1),k7_relat_1(k6_relat_1(A_1),A_156)) = k7_relat_1(k6_relat_1(A_1),A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_686,c_8,c_17806])).

tff(c_589,plain,(
    ! [A_98,B_99,C_100] :
      ( k5_relat_1(k5_relat_1(A_98,B_99),C_100) = k5_relat_1(A_98,k5_relat_1(B_99,C_100))
      | ~ v1_relat_1(C_100)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_615,plain,(
    ! [A_33,B_34,C_100] :
      ( k5_relat_1(k6_relat_1(A_33),k5_relat_1(B_34,C_100)) = k5_relat_1(k7_relat_1(B_34,A_33),C_100)
      | ~ v1_relat_1(C_100)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_589])).

tff(c_1674,plain,(
    ! [A_140,B_141,C_142] :
      ( k5_relat_1(k6_relat_1(A_140),k5_relat_1(B_141,C_142)) = k5_relat_1(k7_relat_1(B_141,A_140),C_142)
      | ~ v1_relat_1(C_142)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_615])).

tff(c_1725,plain,(
    ! [A_33,A_140,B_34] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_33),A_140),B_34) = k5_relat_1(k6_relat_1(A_140),k7_relat_1(B_34,A_33))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1674])).

tff(c_15053,plain,(
    ! [A_322,A_323,B_324] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_322),A_323),B_324) = k5_relat_1(k6_relat_1(A_323),k7_relat_1(B_324,A_322))
      | ~ v1_relat_1(B_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1725])).

tff(c_15124,plain,(
    ! [A_323,A_30,A_322] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_323),k7_relat_1(k6_relat_1(A_30),A_322)),k7_relat_1(k6_relat_1(A_322),A_323))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_322),A_323))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15053,c_34])).

tff(c_38055,plain,(
    ! [A_498,A_499,A_500] : r1_tarski(k5_relat_1(k6_relat_1(A_498),k7_relat_1(k6_relat_1(A_499),A_500)),k7_relat_1(k6_relat_1(A_500),A_498)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_686,c_15124])).

tff(c_38505,plain,(
    ! [A_504,A_505] : r1_tarski(k7_relat_1(k6_relat_1(A_504),A_505),k7_relat_1(k6_relat_1(A_505),A_504)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17859,c_38055])).

tff(c_38689,plain,(
    ! [A_1,A_505] :
      ( r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_1,k1_relat_1(k6_relat_1(A_505)))),A_505),k7_relat_1(k6_relat_1(A_505),A_1))
      | ~ v1_relat_1(k6_relat_1(A_505)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_38505])).

tff(c_39594,plain,(
    ! [A_508,A_509] : r1_tarski(k6_relat_1(k3_xboole_0(A_508,A_509)),k7_relat_1(k6_relat_1(A_509),A_508)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1989,c_28,c_38689])).

tff(c_39604,plain,(
    ! [A_509,A_508] :
      ( k7_relat_1(k6_relat_1(A_509),A_508) = k6_relat_1(k3_xboole_0(A_508,A_509))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_509),A_508),k6_relat_1(k3_xboole_0(A_508,A_509))) ) ),
    inference(resolution,[status(thm)],[c_39594,c_4])).

tff(c_39830,plain,(
    ! [A_509,A_508] : k7_relat_1(k6_relat_1(A_509),A_508) = k6_relat_1(k3_xboole_0(A_508,A_509)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_39604])).

tff(c_42,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_231,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_42])).

tff(c_252,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_231])).

tff(c_40227,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39830,c_252])).

tff(c_40255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.29/7.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.33/7.30  
% 15.33/7.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.33/7.30  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 15.33/7.30  
% 15.33/7.30  %Foreground sorts:
% 15.33/7.30  
% 15.33/7.30  
% 15.33/7.30  %Background operators:
% 15.33/7.30  
% 15.33/7.30  
% 15.33/7.30  %Foreground operators:
% 15.33/7.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.33/7.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.33/7.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.33/7.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.33/7.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.33/7.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.33/7.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.33/7.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.33/7.30  tff('#skF_2', type, '#skF_2': $i).
% 15.33/7.30  tff('#skF_1', type, '#skF_1': $i).
% 15.33/7.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.33/7.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.33/7.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.33/7.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.33/7.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.33/7.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.33/7.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.33/7.30  
% 15.33/7.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.33/7.32  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 15.33/7.32  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.33/7.32  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 15.33/7.32  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 15.33/7.32  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 15.33/7.32  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.33/7.32  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.33/7.32  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 15.33/7.32  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 15.33/7.32  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 15.33/7.32  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 15.33/7.32  tff(f_94, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 15.33/7.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.33/7.32  tff(c_20, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.33/7.32  tff(c_28, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.33/7.32  tff(c_411, plain, (![B_84, A_85]: (k7_relat_1(B_84, k3_xboole_0(k1_relat_1(B_84), A_85))=k7_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.33/7.32  tff(c_207, plain, (![A_61, B_62]: (k5_relat_1(k6_relat_1(A_61), B_62)=k7_relat_1(B_62, A_61) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.33/7.32  tff(c_34, plain, (![B_31, A_30]: (r1_tarski(k5_relat_1(B_31, k6_relat_1(A_30)), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.33/7.32  tff(c_217, plain, (![A_30, A_61]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_61), k6_relat_1(A_61)) | ~v1_relat_1(k6_relat_1(A_61)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_34])).
% 15.33/7.32  tff(c_246, plain, (![A_30, A_61]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_61), k6_relat_1(A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_217])).
% 15.33/7.32  tff(c_425, plain, (![A_30, A_85]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_85), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)), A_85))) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_411, c_246])).
% 15.33/7.32  tff(c_464, plain, (![A_88, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_88), A_89), k6_relat_1(k3_xboole_0(A_88, A_89))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28, c_425])).
% 15.33/7.32  tff(c_486, plain, (![B_2, A_1]: (r1_tarski(k7_relat_1(k6_relat_1(B_2), A_1), k6_relat_1(k3_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_464])).
% 15.33/7.32  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.33/7.32  tff(c_65, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.33/7.32  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.33/7.32  tff(c_80, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_65, c_10])).
% 15.33/7.32  tff(c_30, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.33/7.32  tff(c_316, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~r1_tarski(k1_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.33/7.32  tff(c_319, plain, (![A_29, A_78]: (k7_relat_1(k6_relat_1(A_29), A_78)=k6_relat_1(A_29) | ~r1_tarski(A_29, A_78) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_316])).
% 15.33/7.32  tff(c_325, plain, (![A_29, A_78]: (k7_relat_1(k6_relat_1(A_29), A_78)=k6_relat_1(A_29) | ~r1_tarski(A_29, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_319])).
% 15.33/7.32  tff(c_473, plain, (![A_29, A_78]: (r1_tarski(k6_relat_1(A_29), k6_relat_1(k3_xboole_0(A_29, A_78))) | ~r1_tarski(A_29, A_78))), inference(superposition, [status(thm), theory('equality')], [c_325, c_464])).
% 15.33/7.32  tff(c_354, plain, (![A_80, A_81]: (k7_relat_1(k6_relat_1(A_80), A_81)=k6_relat_1(A_80) | ~r1_tarski(A_80, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_319])).
% 15.33/7.32  tff(c_406, plain, (![A_82, A_83]: (r1_tarski(k6_relat_1(A_82), k6_relat_1(A_83)) | ~r1_tarski(A_82, A_83))), inference(superposition, [status(thm), theory('equality')], [c_354, c_246])).
% 15.33/7.32  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.33/7.32  tff(c_1209, plain, (![A_133, A_132]: (k6_relat_1(A_133)=k6_relat_1(A_132) | ~r1_tarski(k6_relat_1(A_132), k6_relat_1(A_133)) | ~r1_tarski(A_133, A_132))), inference(resolution, [status(thm)], [c_406, c_4])).
% 15.33/7.32  tff(c_1218, plain, (![A_29, A_78]: (k6_relat_1(k3_xboole_0(A_29, A_78))=k6_relat_1(A_29) | ~r1_tarski(k3_xboole_0(A_29, A_78), A_29) | ~r1_tarski(A_29, A_78))), inference(resolution, [status(thm)], [c_473, c_1209])).
% 15.33/7.32  tff(c_1475, plain, (![A_136, A_137]: (k6_relat_1(k3_xboole_0(A_136, A_137))=k6_relat_1(A_136) | ~r1_tarski(A_136, A_137))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1218])).
% 15.33/7.32  tff(c_1575, plain, (![A_136, A_137]: (k3_xboole_0(A_136, A_137)=k2_relat_1(k6_relat_1(A_136)) | ~r1_tarski(A_136, A_137))), inference(superposition, [status(thm), theory('equality')], [c_1475, c_30])).
% 15.33/7.32  tff(c_1609, plain, (![A_138, A_139]: (k3_xboole_0(A_138, A_139)=A_138 | ~r1_tarski(A_138, A_139))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1575])).
% 15.33/7.32  tff(c_1874, plain, (![B_145, A_146]: (k3_xboole_0(k3_xboole_0(B_145, A_146), A_146)=k3_xboole_0(B_145, A_146))), inference(resolution, [status(thm)], [c_80, c_1609])).
% 15.33/7.32  tff(c_418, plain, (![A_29, A_85]: (k7_relat_1(k6_relat_1(A_29), A_85)=k6_relat_1(A_29) | ~r1_tarski(A_29, k3_xboole_0(k1_relat_1(k6_relat_1(A_29)), A_85)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_411, c_325])).
% 15.33/7.32  tff(c_449, plain, (![A_29, A_85]: (k7_relat_1(k6_relat_1(A_29), A_85)=k6_relat_1(A_29) | ~r1_tarski(A_29, k3_xboole_0(A_29, A_85)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28, c_418])).
% 15.33/7.32  tff(c_1899, plain, (![B_145, A_146]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_145, A_146)), A_146)=k6_relat_1(k3_xboole_0(B_145, A_146)) | ~r1_tarski(k3_xboole_0(B_145, A_146), k3_xboole_0(B_145, A_146)))), inference(superposition, [status(thm), theory('equality')], [c_1874, c_449])).
% 15.33/7.32  tff(c_1989, plain, (![B_145, A_146]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_145, A_146)), A_146)=k6_relat_1(k3_xboole_0(B_145, A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1899])).
% 15.33/7.32  tff(c_443, plain, (![B_84, A_1]: (k7_relat_1(B_84, k3_xboole_0(A_1, k1_relat_1(B_84)))=k7_relat_1(B_84, A_1) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_2, c_411])).
% 15.33/7.32  tff(c_446, plain, (![A_29, A_85]: (k7_relat_1(k6_relat_1(A_29), k3_xboole_0(A_29, A_85))=k7_relat_1(k6_relat_1(A_29), A_85) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_411])).
% 15.33/7.32  tff(c_640, plain, (![A_101, A_102]: (k7_relat_1(k6_relat_1(A_101), k3_xboole_0(A_101, A_102))=k7_relat_1(k6_relat_1(A_101), A_102))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_446])).
% 15.33/7.32  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k5_relat_1(A_14, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.33/7.32  tff(c_213, plain, (![B_62, A_61]: (v1_relat_1(k7_relat_1(B_62, A_61)) | ~v1_relat_1(B_62) | ~v1_relat_1(k6_relat_1(A_61)) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_207, c_18])).
% 15.33/7.32  tff(c_244, plain, (![B_62, A_61]: (v1_relat_1(k7_relat_1(B_62, A_61)) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_213])).
% 15.33/7.32  tff(c_664, plain, (![A_101, A_102]: (v1_relat_1(k7_relat_1(k6_relat_1(A_101), A_102)) | ~v1_relat_1(k6_relat_1(A_101)))), inference(superposition, [status(thm), theory('equality')], [c_640, c_244])).
% 15.33/7.32  tff(c_686, plain, (![A_101, A_102]: (v1_relat_1(k7_relat_1(k6_relat_1(A_101), A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_664])).
% 15.33/7.32  tff(c_456, plain, (![A_29, A_85]: (k7_relat_1(k6_relat_1(A_29), k3_xboole_0(A_29, A_85))=k7_relat_1(k6_relat_1(A_29), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_446])).
% 15.33/7.32  tff(c_674, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(B_2, A_1))=k7_relat_1(k6_relat_1(A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_640])).
% 15.33/7.32  tff(c_24, plain, (![B_21, A_20]: (k7_relat_1(B_21, k3_xboole_0(k1_relat_1(B_21), A_20))=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.33/7.32  tff(c_492, plain, (![C_90, A_91, B_92]: (k7_relat_1(k7_relat_1(C_90, A_91), B_92)=k7_relat_1(C_90, k3_xboole_0(A_91, B_92)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.33/7.32  tff(c_2489, plain, (![B_155, A_156, B_157]: (k7_relat_1(B_155, k3_xboole_0(k3_xboole_0(k1_relat_1(B_155), A_156), B_157))=k7_relat_1(k7_relat_1(B_155, A_156), B_157) | ~v1_relat_1(B_155) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_24, c_492])).
% 15.33/7.32  tff(c_2587, plain, (![A_1, A_156]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(k1_relat_1(k6_relat_1(A_1)), A_156))=k7_relat_1(k7_relat_1(k6_relat_1(A_1), A_156), A_1) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_674, c_2489])).
% 15.33/7.32  tff(c_2632, plain, (![A_1, A_156]: (k7_relat_1(k7_relat_1(k6_relat_1(A_1), A_156), A_1)=k7_relat_1(k6_relat_1(A_1), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_456, c_28, c_2587])).
% 15.33/7.32  tff(c_38, plain, (![A_33, B_34]: (k5_relat_1(k6_relat_1(A_33), B_34)=k7_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.33/7.32  tff(c_32, plain, (![A_30, B_31]: (r1_tarski(k5_relat_1(k6_relat_1(A_30), B_31), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.33/7.32  tff(c_177, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.33/7.32  tff(c_992, plain, (![A_121, B_122]: (k5_relat_1(k6_relat_1(A_121), B_122)=B_122 | ~r1_tarski(B_122, k5_relat_1(k6_relat_1(A_121), B_122)) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_32, c_177])).
% 15.33/7.32  tff(c_17770, plain, (![A_346, B_347]: (k5_relat_1(k6_relat_1(A_346), B_347)=B_347 | ~r1_tarski(B_347, k7_relat_1(B_347, A_346)) | ~v1_relat_1(B_347) | ~v1_relat_1(B_347))), inference(superposition, [status(thm), theory('equality')], [c_38, c_992])).
% 15.33/7.32  tff(c_17806, plain, (![A_1, A_156]: (k5_relat_1(k6_relat_1(A_1), k7_relat_1(k6_relat_1(A_1), A_156))=k7_relat_1(k6_relat_1(A_1), A_156) | ~r1_tarski(k7_relat_1(k6_relat_1(A_1), A_156), k7_relat_1(k6_relat_1(A_1), A_156)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_1), A_156)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_1), A_156)))), inference(superposition, [status(thm), theory('equality')], [c_2632, c_17770])).
% 15.33/7.32  tff(c_17859, plain, (![A_1, A_156]: (k5_relat_1(k6_relat_1(A_1), k7_relat_1(k6_relat_1(A_1), A_156))=k7_relat_1(k6_relat_1(A_1), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_686, c_8, c_17806])).
% 15.33/7.32  tff(c_589, plain, (![A_98, B_99, C_100]: (k5_relat_1(k5_relat_1(A_98, B_99), C_100)=k5_relat_1(A_98, k5_relat_1(B_99, C_100)) | ~v1_relat_1(C_100) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.33/7.32  tff(c_615, plain, (![A_33, B_34, C_100]: (k5_relat_1(k6_relat_1(A_33), k5_relat_1(B_34, C_100))=k5_relat_1(k7_relat_1(B_34, A_33), C_100) | ~v1_relat_1(C_100) | ~v1_relat_1(B_34) | ~v1_relat_1(k6_relat_1(A_33)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_38, c_589])).
% 15.33/7.32  tff(c_1674, plain, (![A_140, B_141, C_142]: (k5_relat_1(k6_relat_1(A_140), k5_relat_1(B_141, C_142))=k5_relat_1(k7_relat_1(B_141, A_140), C_142) | ~v1_relat_1(C_142) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_615])).
% 15.33/7.32  tff(c_1725, plain, (![A_33, A_140, B_34]: (k5_relat_1(k7_relat_1(k6_relat_1(A_33), A_140), B_34)=k5_relat_1(k6_relat_1(A_140), k7_relat_1(B_34, A_33)) | ~v1_relat_1(B_34) | ~v1_relat_1(k6_relat_1(A_33)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1674])).
% 15.33/7.32  tff(c_15053, plain, (![A_322, A_323, B_324]: (k5_relat_1(k7_relat_1(k6_relat_1(A_322), A_323), B_324)=k5_relat_1(k6_relat_1(A_323), k7_relat_1(B_324, A_322)) | ~v1_relat_1(B_324))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1725])).
% 15.33/7.32  tff(c_15124, plain, (![A_323, A_30, A_322]: (r1_tarski(k5_relat_1(k6_relat_1(A_323), k7_relat_1(k6_relat_1(A_30), A_322)), k7_relat_1(k6_relat_1(A_322), A_323)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_322), A_323)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_15053, c_34])).
% 15.33/7.32  tff(c_38055, plain, (![A_498, A_499, A_500]: (r1_tarski(k5_relat_1(k6_relat_1(A_498), k7_relat_1(k6_relat_1(A_499), A_500)), k7_relat_1(k6_relat_1(A_500), A_498)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_686, c_15124])).
% 15.33/7.32  tff(c_38505, plain, (![A_504, A_505]: (r1_tarski(k7_relat_1(k6_relat_1(A_504), A_505), k7_relat_1(k6_relat_1(A_505), A_504)))), inference(superposition, [status(thm), theory('equality')], [c_17859, c_38055])).
% 15.33/7.32  tff(c_38689, plain, (![A_1, A_505]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(A_1, k1_relat_1(k6_relat_1(A_505)))), A_505), k7_relat_1(k6_relat_1(A_505), A_1)) | ~v1_relat_1(k6_relat_1(A_505)))), inference(superposition, [status(thm), theory('equality')], [c_443, c_38505])).
% 15.33/7.32  tff(c_39594, plain, (![A_508, A_509]: (r1_tarski(k6_relat_1(k3_xboole_0(A_508, A_509)), k7_relat_1(k6_relat_1(A_509), A_508)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1989, c_28, c_38689])).
% 15.33/7.32  tff(c_39604, plain, (![A_509, A_508]: (k7_relat_1(k6_relat_1(A_509), A_508)=k6_relat_1(k3_xboole_0(A_508, A_509)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_509), A_508), k6_relat_1(k3_xboole_0(A_508, A_509))))), inference(resolution, [status(thm)], [c_39594, c_4])).
% 15.33/7.32  tff(c_39830, plain, (![A_509, A_508]: (k7_relat_1(k6_relat_1(A_509), A_508)=k6_relat_1(k3_xboole_0(A_508, A_509)))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_39604])).
% 15.33/7.32  tff(c_42, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.33/7.32  tff(c_231, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_42])).
% 15.33/7.32  tff(c_252, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_231])).
% 15.33/7.32  tff(c_40227, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_39830, c_252])).
% 15.33/7.32  tff(c_40255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_40227])).
% 15.33/7.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.33/7.32  
% 15.33/7.32  Inference rules
% 15.33/7.32  ----------------------
% 15.33/7.32  #Ref     : 0
% 15.33/7.32  #Sup     : 9956
% 15.33/7.32  #Fact    : 0
% 15.33/7.32  #Define  : 0
% 15.33/7.32  #Split   : 1
% 15.33/7.32  #Chain   : 0
% 15.33/7.32  #Close   : 0
% 15.33/7.32  
% 15.33/7.32  Ordering : KBO
% 15.33/7.32  
% 15.33/7.32  Simplification rules
% 15.33/7.32  ----------------------
% 15.33/7.32  #Subsume      : 1091
% 15.33/7.32  #Demod        : 11796
% 15.33/7.32  #Tautology    : 3846
% 15.33/7.32  #SimpNegUnit  : 0
% 15.33/7.32  #BackRed      : 78
% 15.33/7.32  
% 15.33/7.32  #Partial instantiations: 0
% 15.33/7.32  #Strategies tried      : 1
% 15.33/7.32  
% 15.33/7.32  Timing (in seconds)
% 15.33/7.32  ----------------------
% 15.33/7.32  Preprocessing        : 0.34
% 15.33/7.32  Parsing              : 0.19
% 15.33/7.32  CNF conversion       : 0.02
% 15.33/7.32  Main loop            : 6.16
% 15.33/7.32  Inferencing          : 1.08
% 15.33/7.32  Reduction            : 3.35
% 15.33/7.32  Demodulation         : 2.99
% 15.33/7.32  BG Simplification    : 0.16
% 15.33/7.32  Subsumption          : 1.26
% 15.33/7.32  Abstraction          : 0.29
% 15.33/7.32  MUC search           : 0.00
% 15.33/7.32  Cooper               : 0.00
% 15.33/7.32  Total                : 6.54
% 15.33/7.32  Index Insertion      : 0.00
% 15.33/7.32  Index Deletion       : 0.00
% 15.33/7.32  Index Matching       : 0.00
% 15.33/7.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
