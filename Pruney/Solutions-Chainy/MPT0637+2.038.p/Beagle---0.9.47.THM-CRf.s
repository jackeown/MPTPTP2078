%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 13.69s
% Output     : CNFRefutation 13.77s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 327 expanded)
%              Number of leaves         :   32 ( 128 expanded)
%              Depth                    :   16
%              Number of atoms          :  168 ( 541 expanded)
%              Number of equality atoms :   59 ( 193 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_528,plain,(
    ! [B_83,A_84] :
      ( k7_relat_1(B_83,k3_xboole_0(k1_relat_1(B_83),A_84)) = k7_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_458,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = k7_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k5_relat_1(B_32,k6_relat_1(A_31)),B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_465,plain,(
    ! [A_31,A_78] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_78),k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_34])).

tff(c_492,plain,(
    ! [A_31,A_78] : r1_tarski(k7_relat_1(k6_relat_1(A_31),A_78),k6_relat_1(A_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_465])).

tff(c_535,plain,(
    ! [A_31,A_84] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_31),A_84),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)),A_84)))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_492])).

tff(c_1694,plain,(
    ! [A_122,A_123] : r1_tarski(k7_relat_1(k6_relat_1(A_122),A_123),k6_relat_1(k3_xboole_0(A_122,A_123))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_535])).

tff(c_1742,plain,(
    ! [B_2,A_1] : r1_tarski(k7_relat_1(k6_relat_1(B_2),A_1),k6_relat_1(k3_xboole_0(A_1,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1694])).

tff(c_557,plain,(
    ! [A_30,A_84] :
      ( k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_84)) = k7_relat_1(k6_relat_1(A_30),A_84)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_528])).

tff(c_565,plain,(
    ! [A_30,A_84] : k7_relat_1(k6_relat_1(A_30),k3_xboole_0(A_30,A_84)) = k7_relat_1(k6_relat_1(A_30),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_557])).

tff(c_30,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_35] :
      ( k5_relat_1(A_35,k6_relat_1(k2_relat_1(A_35))) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_473,plain,(
    ! [A_78] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78))),A_78) = k6_relat_1(A_78)
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_38])).

tff(c_496,plain,(
    ! [A_78] : k7_relat_1(k6_relat_1(A_78),A_78) = k6_relat_1(A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_30,c_473])).

tff(c_71,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [B_48,A_49] : r1_tarski(k3_xboole_0(B_48,A_49),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_142,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [B_48,A_49] : k3_xboole_0(k3_xboole_0(B_48,A_49),A_49) = k3_xboole_0(B_48,A_49) ),
    inference(resolution,[status(thm)],[c_92,c_142])).

tff(c_1806,plain,(
    ! [A_125,A_126] : k7_relat_1(k6_relat_1(A_125),k3_xboole_0(A_125,A_126)) = k7_relat_1(k6_relat_1(A_125),A_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_557])).

tff(c_1852,plain,(
    ! [B_48,A_49] : k7_relat_1(k6_relat_1(k3_xboole_0(B_48,A_49)),k3_xboole_0(B_48,A_49)) = k7_relat_1(k6_relat_1(k3_xboole_0(B_48,A_49)),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_1806])).

tff(c_4212,plain,(
    ! [B_181,A_182] : k7_relat_1(k6_relat_1(k3_xboole_0(B_181,A_182)),A_182) = k6_relat_1(k3_xboole_0(B_181,A_182)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_1852])).

tff(c_4319,plain,(
    ! [B_2,A_1] : k7_relat_1(k6_relat_1(k3_xboole_0(B_2,A_1)),B_2) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4212])).

tff(c_1864,plain,(
    ! [B_2,A_1] : k7_relat_1(k6_relat_1(B_2),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1806])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_31),B_32),B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1206,plain,(
    ! [B_104,A_105] :
      ( r1_tarski(k7_relat_1(B_104,A_105),B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_32])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1211,plain,(
    ! [B_104,A_105] :
      ( k3_xboole_0(k7_relat_1(B_104,A_105),B_104) = k7_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_1206,c_12])).

tff(c_3182,plain,(
    ! [B_155,A_156] :
      ( k3_xboole_0(B_155,k7_relat_1(B_155,A_156)) = k7_relat_1(B_155,A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1211])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3575,plain,(
    ! [B_161,A_162] :
      ( v1_relat_1(k7_relat_1(B_161,A_162))
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3182,c_20])).

tff(c_3581,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(B_2),A_1))
      | ~ v1_relat_1(k6_relat_1(B_2))
      | ~ v1_relat_1(k6_relat_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_3575])).

tff(c_3606,plain,(
    ! [B_2,A_1] : v1_relat_1(k7_relat_1(k6_relat_1(B_2),A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_3581])).

tff(c_516,plain,(
    ! [A_81,A_82] : r1_tarski(k7_relat_1(k6_relat_1(A_81),A_82),k6_relat_1(A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_465])).

tff(c_8889,plain,(
    ! [A_251,A_252] : k3_xboole_0(k7_relat_1(k6_relat_1(A_251),A_252),k6_relat_1(A_252)) = k7_relat_1(k6_relat_1(A_251),A_252) ),
    inference(resolution,[status(thm)],[c_516,c_12])).

tff(c_9032,plain,(
    ! [A_252,A_251] : k3_xboole_0(k6_relat_1(A_252),k7_relat_1(k6_relat_1(A_251),A_252)) = k7_relat_1(k6_relat_1(A_251),A_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_8889,c_2])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_243,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k5_relat_1(B_67,k6_relat_1(A_68)),B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_248,plain,(
    ! [B_67,A_68] :
      ( k3_xboole_0(k5_relat_1(B_67,k6_relat_1(A_68)),B_67) = k5_relat_1(B_67,k6_relat_1(A_68))
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_243,c_12])).

tff(c_3349,plain,(
    ! [B_157,A_158] :
      ( k3_xboole_0(B_157,k5_relat_1(B_157,k6_relat_1(A_158))) = k5_relat_1(B_157,k6_relat_1(A_158))
      | ~ v1_relat_1(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_248])).

tff(c_3477,plain,(
    ! [A_36,A_158] :
      ( k3_xboole_0(k6_relat_1(A_36),k7_relat_1(k6_relat_1(A_158),A_36)) = k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_158))
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k6_relat_1(A_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3349])).

tff(c_3524,plain,(
    ! [A_36,A_158] : k3_xboole_0(k6_relat_1(A_36),k7_relat_1(k6_relat_1(A_158),A_36)) = k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_158)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_3477])).

tff(c_11943,plain,(
    ! [A_36,A_158] : k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_158)) = k7_relat_1(k6_relat_1(A_158),A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9032,c_3524])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,k3_xboole_0(k1_relat_1(B_22),A_21)) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_866,plain,(
    ! [C_94,A_95,B_96] :
      ( k7_relat_1(k7_relat_1(C_94,A_95),B_96) = k7_relat_1(C_94,k3_xboole_0(A_95,B_96))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6524,plain,(
    ! [B_210,A_211,B_212] :
      ( k7_relat_1(B_210,k3_xboole_0(k3_xboole_0(k1_relat_1(B_210),A_211),B_212)) = k7_relat_1(k7_relat_1(B_210,A_211),B_212)
      | ~ v1_relat_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_866])).

tff(c_6551,plain,(
    ! [B_212,A_211] :
      ( k7_relat_1(k6_relat_1(B_212),k3_xboole_0(k1_relat_1(k6_relat_1(B_212)),A_211)) = k7_relat_1(k7_relat_1(k6_relat_1(B_212),A_211),B_212)
      | ~ v1_relat_1(k6_relat_1(B_212))
      | ~ v1_relat_1(k6_relat_1(B_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6524,c_1864])).

tff(c_6718,plain,(
    ! [B_212,A_211] : k7_relat_1(k7_relat_1(k6_relat_1(B_212),A_211),B_212) = k7_relat_1(k6_relat_1(B_212),A_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_565,c_28,c_6551])).

tff(c_187,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_61),B_62),B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_190,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(k5_relat_1(k6_relat_1(A_61),B_62),B_62) = k5_relat_1(k6_relat_1(A_61),B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_187,c_12])).

tff(c_2877,plain,(
    ! [B_149,A_150] :
      ( k3_xboole_0(B_149,k5_relat_1(k6_relat_1(A_150),B_149)) = k5_relat_1(k6_relat_1(A_150),B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_190])).

tff(c_13900,plain,(
    ! [A_310,B_311] :
      ( k5_relat_1(k6_relat_1(A_310),B_311) = k3_xboole_0(B_311,k7_relat_1(B_311,A_310))
      | ~ v1_relat_1(B_311)
      | ~ v1_relat_1(B_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2877])).

tff(c_14163,plain,(
    ! [B_212,A_211] :
      ( k3_xboole_0(k7_relat_1(k6_relat_1(B_212),A_211),k7_relat_1(k6_relat_1(B_212),A_211)) = k5_relat_1(k6_relat_1(B_212),k7_relat_1(k6_relat_1(B_212),A_211))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_212),A_211))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_212),A_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6718,c_13900])).

tff(c_14274,plain,(
    ! [B_212,A_211] : k5_relat_1(k6_relat_1(B_212),k7_relat_1(k6_relat_1(B_212),A_211)) = k7_relat_1(k6_relat_1(B_212),A_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_3606,c_154,c_14163])).

tff(c_1010,plain,(
    ! [A_99,B_100,C_101] :
      ( k5_relat_1(k5_relat_1(A_99,B_100),C_101) = k5_relat_1(A_99,k5_relat_1(B_100,C_101))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1020,plain,(
    ! [A_99,B_100,A_31] :
      ( r1_tarski(k5_relat_1(A_99,k5_relat_1(B_100,k6_relat_1(A_31))),k5_relat_1(A_99,B_100))
      | ~ v1_relat_1(k5_relat_1(A_99,B_100))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_34])).

tff(c_7197,plain,(
    ! [A_225,B_226,A_227] :
      ( r1_tarski(k5_relat_1(A_225,k5_relat_1(B_226,k6_relat_1(A_227))),k5_relat_1(A_225,B_226))
      | ~ v1_relat_1(k5_relat_1(A_225,B_226))
      | ~ v1_relat_1(B_226)
      | ~ v1_relat_1(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1020])).

tff(c_7259,plain,(
    ! [A_225,A_227,A_36] :
      ( r1_tarski(k5_relat_1(A_225,k7_relat_1(k6_relat_1(A_227),A_36)),k5_relat_1(A_225,k6_relat_1(A_36)))
      | ~ v1_relat_1(k5_relat_1(A_225,k6_relat_1(A_36)))
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(A_225)
      | ~ v1_relat_1(k6_relat_1(A_227)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7197])).

tff(c_35969,plain,(
    ! [A_488,A_489,A_490] :
      ( r1_tarski(k5_relat_1(A_488,k7_relat_1(k6_relat_1(A_489),A_490)),k5_relat_1(A_488,k6_relat_1(A_490)))
      | ~ v1_relat_1(k5_relat_1(A_488,k6_relat_1(A_490)))
      | ~ v1_relat_1(A_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_7259])).

tff(c_36044,plain,(
    ! [B_212,A_211] :
      ( r1_tarski(k7_relat_1(k6_relat_1(B_212),A_211),k5_relat_1(k6_relat_1(B_212),k6_relat_1(A_211)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(B_212),k6_relat_1(A_211)))
      | ~ v1_relat_1(k6_relat_1(B_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14274,c_35969])).

tff(c_36243,plain,(
    ! [B_491,A_492] : r1_tarski(k7_relat_1(k6_relat_1(B_491),A_492),k7_relat_1(k6_relat_1(A_492),B_491)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3606,c_11943,c_11943,c_36044])).

tff(c_36350,plain,(
    ! [A_1,B_2] : r1_tarski(k6_relat_1(k3_xboole_0(A_1,B_2)),k7_relat_1(k6_relat_1(B_2),k3_xboole_0(B_2,A_1))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4319,c_36243])).

tff(c_37180,plain,(
    ! [A_495,B_496] : r1_tarski(k6_relat_1(k3_xboole_0(A_495,B_496)),k7_relat_1(k6_relat_1(B_496),A_495)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_36350])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37187,plain,(
    ! [B_496,A_495] :
      ( k7_relat_1(k6_relat_1(B_496),A_495) = k6_relat_1(k3_xboole_0(A_495,B_496))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_496),A_495),k6_relat_1(k3_xboole_0(A_495,B_496))) ) ),
    inference(resolution,[status(thm)],[c_37180,c_4])).

tff(c_37405,plain,(
    ! [B_496,A_495] : k7_relat_1(k6_relat_1(B_496),A_495) = k6_relat_1(k3_xboole_0(A_495,B_496)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_37187])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_479,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_46])).

tff(c_498,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_479])).

tff(c_37784,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37405,c_498])).

tff(c_37813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_37784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.69/6.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.69/6.39  
% 13.69/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.69/6.40  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 13.69/6.40  
% 13.69/6.40  %Foreground sorts:
% 13.69/6.40  
% 13.69/6.40  
% 13.69/6.40  %Background operators:
% 13.69/6.40  
% 13.69/6.40  
% 13.69/6.40  %Foreground operators:
% 13.69/6.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.69/6.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.69/6.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.69/6.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.69/6.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.69/6.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.69/6.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.69/6.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.69/6.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.69/6.40  tff('#skF_2', type, '#skF_2': $i).
% 13.69/6.40  tff('#skF_1', type, '#skF_1': $i).
% 13.69/6.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.69/6.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.69/6.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.69/6.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.69/6.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.69/6.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.69/6.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.69/6.40  
% 13.77/6.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.77/6.42  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 13.77/6.42  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.77/6.42  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 13.77/6.42  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 13.77/6.42  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 13.77/6.42  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 13.77/6.42  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.77/6.42  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.77/6.42  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 13.77/6.42  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.77/6.42  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 13.77/6.42  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 13.77/6.42  tff(f_98, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 13.77/6.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.77/6.42  tff(c_42, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.77/6.42  tff(c_28, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.77/6.42  tff(c_528, plain, (![B_83, A_84]: (k7_relat_1(B_83, k3_xboole_0(k1_relat_1(B_83), A_84))=k7_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.77/6.42  tff(c_458, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=k7_relat_1(B_79, A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.77/6.42  tff(c_34, plain, (![B_32, A_31]: (r1_tarski(k5_relat_1(B_32, k6_relat_1(A_31)), B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.77/6.42  tff(c_465, plain, (![A_31, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_78), k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_458, c_34])).
% 13.77/6.42  tff(c_492, plain, (![A_31, A_78]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_78), k6_relat_1(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_465])).
% 13.77/6.42  tff(c_535, plain, (![A_31, A_84]: (r1_tarski(k7_relat_1(k6_relat_1(A_31), A_84), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)), A_84))) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_528, c_492])).
% 13.77/6.42  tff(c_1694, plain, (![A_122, A_123]: (r1_tarski(k7_relat_1(k6_relat_1(A_122), A_123), k6_relat_1(k3_xboole_0(A_122, A_123))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_535])).
% 13.77/6.42  tff(c_1742, plain, (![B_2, A_1]: (r1_tarski(k7_relat_1(k6_relat_1(B_2), A_1), k6_relat_1(k3_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1694])).
% 13.77/6.42  tff(c_557, plain, (![A_30, A_84]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_84))=k7_relat_1(k6_relat_1(A_30), A_84) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_528])).
% 13.77/6.42  tff(c_565, plain, (![A_30, A_84]: (k7_relat_1(k6_relat_1(A_30), k3_xboole_0(A_30, A_84))=k7_relat_1(k6_relat_1(A_30), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_557])).
% 13.77/6.42  tff(c_30, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.77/6.42  tff(c_38, plain, (![A_35]: (k5_relat_1(A_35, k6_relat_1(k2_relat_1(A_35)))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.77/6.42  tff(c_473, plain, (![A_78]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78))), A_78)=k6_relat_1(A_78) | ~v1_relat_1(k6_relat_1(A_78)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_78)))))), inference(superposition, [status(thm), theory('equality')], [c_458, c_38])).
% 13.77/6.42  tff(c_496, plain, (![A_78]: (k7_relat_1(k6_relat_1(A_78), A_78)=k6_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_30, c_473])).
% 13.77/6.42  tff(c_71, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.77/6.42  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.77/6.42  tff(c_92, plain, (![B_48, A_49]: (r1_tarski(k3_xboole_0(B_48, A_49), A_49))), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 13.77/6.42  tff(c_142, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.77/6.42  tff(c_152, plain, (![B_48, A_49]: (k3_xboole_0(k3_xboole_0(B_48, A_49), A_49)=k3_xboole_0(B_48, A_49))), inference(resolution, [status(thm)], [c_92, c_142])).
% 13.77/6.42  tff(c_1806, plain, (![A_125, A_126]: (k7_relat_1(k6_relat_1(A_125), k3_xboole_0(A_125, A_126))=k7_relat_1(k6_relat_1(A_125), A_126))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_557])).
% 13.77/6.42  tff(c_1852, plain, (![B_48, A_49]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_48, A_49)), k3_xboole_0(B_48, A_49))=k7_relat_1(k6_relat_1(k3_xboole_0(B_48, A_49)), A_49))), inference(superposition, [status(thm), theory('equality')], [c_152, c_1806])).
% 13.77/6.42  tff(c_4212, plain, (![B_181, A_182]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_181, A_182)), A_182)=k6_relat_1(k3_xboole_0(B_181, A_182)))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_1852])).
% 13.77/6.42  tff(c_4319, plain, (![B_2, A_1]: (k7_relat_1(k6_relat_1(k3_xboole_0(B_2, A_1)), B_2)=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4212])).
% 13.77/6.42  tff(c_1864, plain, (![B_2, A_1]: (k7_relat_1(k6_relat_1(B_2), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1806])).
% 13.77/6.42  tff(c_32, plain, (![A_31, B_32]: (r1_tarski(k5_relat_1(k6_relat_1(A_31), B_32), B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.77/6.42  tff(c_1206, plain, (![B_104, A_105]: (r1_tarski(k7_relat_1(B_104, A_105), B_104) | ~v1_relat_1(B_104) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_458, c_32])).
% 13.77/6.42  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.77/6.42  tff(c_1211, plain, (![B_104, A_105]: (k3_xboole_0(k7_relat_1(B_104, A_105), B_104)=k7_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_1206, c_12])).
% 13.77/6.42  tff(c_3182, plain, (![B_155, A_156]: (k3_xboole_0(B_155, k7_relat_1(B_155, A_156))=k7_relat_1(B_155, A_156) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1211])).
% 13.77/6.42  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.77/6.42  tff(c_3575, plain, (![B_161, A_162]: (v1_relat_1(k7_relat_1(B_161, A_162)) | ~v1_relat_1(B_161) | ~v1_relat_1(B_161))), inference(superposition, [status(thm), theory('equality')], [c_3182, c_20])).
% 13.77/6.42  tff(c_3581, plain, (![B_2, A_1]: (v1_relat_1(k7_relat_1(k6_relat_1(B_2), A_1)) | ~v1_relat_1(k6_relat_1(B_2)) | ~v1_relat_1(k6_relat_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_1864, c_3575])).
% 13.77/6.42  tff(c_3606, plain, (![B_2, A_1]: (v1_relat_1(k7_relat_1(k6_relat_1(B_2), A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_3581])).
% 13.77/6.42  tff(c_516, plain, (![A_81, A_82]: (r1_tarski(k7_relat_1(k6_relat_1(A_81), A_82), k6_relat_1(A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_465])).
% 13.77/6.42  tff(c_8889, plain, (![A_251, A_252]: (k3_xboole_0(k7_relat_1(k6_relat_1(A_251), A_252), k6_relat_1(A_252))=k7_relat_1(k6_relat_1(A_251), A_252))), inference(resolution, [status(thm)], [c_516, c_12])).
% 13.77/6.42  tff(c_9032, plain, (![A_252, A_251]: (k3_xboole_0(k6_relat_1(A_252), k7_relat_1(k6_relat_1(A_251), A_252))=k7_relat_1(k6_relat_1(A_251), A_252))), inference(superposition, [status(thm), theory('equality')], [c_8889, c_2])).
% 13.77/6.42  tff(c_40, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.77/6.42  tff(c_243, plain, (![B_67, A_68]: (r1_tarski(k5_relat_1(B_67, k6_relat_1(A_68)), B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.77/6.42  tff(c_248, plain, (![B_67, A_68]: (k3_xboole_0(k5_relat_1(B_67, k6_relat_1(A_68)), B_67)=k5_relat_1(B_67, k6_relat_1(A_68)) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_243, c_12])).
% 13.77/6.42  tff(c_3349, plain, (![B_157, A_158]: (k3_xboole_0(B_157, k5_relat_1(B_157, k6_relat_1(A_158)))=k5_relat_1(B_157, k6_relat_1(A_158)) | ~v1_relat_1(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_248])).
% 13.77/6.42  tff(c_3477, plain, (![A_36, A_158]: (k3_xboole_0(k6_relat_1(A_36), k7_relat_1(k6_relat_1(A_158), A_36))=k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_158)) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k6_relat_1(A_158)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3349])).
% 13.77/6.42  tff(c_3524, plain, (![A_36, A_158]: (k3_xboole_0(k6_relat_1(A_36), k7_relat_1(k6_relat_1(A_158), A_36))=k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_158)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_3477])).
% 13.77/6.42  tff(c_11943, plain, (![A_36, A_158]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_158))=k7_relat_1(k6_relat_1(A_158), A_36))), inference(demodulation, [status(thm), theory('equality')], [c_9032, c_3524])).
% 13.77/6.42  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.77/6.42  tff(c_154, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_142])).
% 13.77/6.42  tff(c_24, plain, (![B_22, A_21]: (k7_relat_1(B_22, k3_xboole_0(k1_relat_1(B_22), A_21))=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.77/6.42  tff(c_866, plain, (![C_94, A_95, B_96]: (k7_relat_1(k7_relat_1(C_94, A_95), B_96)=k7_relat_1(C_94, k3_xboole_0(A_95, B_96)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.77/6.42  tff(c_6524, plain, (![B_210, A_211, B_212]: (k7_relat_1(B_210, k3_xboole_0(k3_xboole_0(k1_relat_1(B_210), A_211), B_212))=k7_relat_1(k7_relat_1(B_210, A_211), B_212) | ~v1_relat_1(B_210) | ~v1_relat_1(B_210))), inference(superposition, [status(thm), theory('equality')], [c_24, c_866])).
% 13.77/6.42  tff(c_6551, plain, (![B_212, A_211]: (k7_relat_1(k6_relat_1(B_212), k3_xboole_0(k1_relat_1(k6_relat_1(B_212)), A_211))=k7_relat_1(k7_relat_1(k6_relat_1(B_212), A_211), B_212) | ~v1_relat_1(k6_relat_1(B_212)) | ~v1_relat_1(k6_relat_1(B_212)))), inference(superposition, [status(thm), theory('equality')], [c_6524, c_1864])).
% 13.77/6.42  tff(c_6718, plain, (![B_212, A_211]: (k7_relat_1(k7_relat_1(k6_relat_1(B_212), A_211), B_212)=k7_relat_1(k6_relat_1(B_212), A_211))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_565, c_28, c_6551])).
% 13.77/6.42  tff(c_187, plain, (![A_61, B_62]: (r1_tarski(k5_relat_1(k6_relat_1(A_61), B_62), B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.77/6.42  tff(c_190, plain, (![A_61, B_62]: (k3_xboole_0(k5_relat_1(k6_relat_1(A_61), B_62), B_62)=k5_relat_1(k6_relat_1(A_61), B_62) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_187, c_12])).
% 13.77/6.42  tff(c_2877, plain, (![B_149, A_150]: (k3_xboole_0(B_149, k5_relat_1(k6_relat_1(A_150), B_149))=k5_relat_1(k6_relat_1(A_150), B_149) | ~v1_relat_1(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_190])).
% 13.77/6.42  tff(c_13900, plain, (![A_310, B_311]: (k5_relat_1(k6_relat_1(A_310), B_311)=k3_xboole_0(B_311, k7_relat_1(B_311, A_310)) | ~v1_relat_1(B_311) | ~v1_relat_1(B_311))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2877])).
% 13.77/6.42  tff(c_14163, plain, (![B_212, A_211]: (k3_xboole_0(k7_relat_1(k6_relat_1(B_212), A_211), k7_relat_1(k6_relat_1(B_212), A_211))=k5_relat_1(k6_relat_1(B_212), k7_relat_1(k6_relat_1(B_212), A_211)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_212), A_211)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_212), A_211)))), inference(superposition, [status(thm), theory('equality')], [c_6718, c_13900])).
% 13.77/6.42  tff(c_14274, plain, (![B_212, A_211]: (k5_relat_1(k6_relat_1(B_212), k7_relat_1(k6_relat_1(B_212), A_211))=k7_relat_1(k6_relat_1(B_212), A_211))), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_3606, c_154, c_14163])).
% 13.77/6.42  tff(c_1010, plain, (![A_99, B_100, C_101]: (k5_relat_1(k5_relat_1(A_99, B_100), C_101)=k5_relat_1(A_99, k5_relat_1(B_100, C_101)) | ~v1_relat_1(C_101) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.77/6.42  tff(c_1020, plain, (![A_99, B_100, A_31]: (r1_tarski(k5_relat_1(A_99, k5_relat_1(B_100, k6_relat_1(A_31))), k5_relat_1(A_99, B_100)) | ~v1_relat_1(k5_relat_1(A_99, B_100)) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_1010, c_34])).
% 13.77/6.42  tff(c_7197, plain, (![A_225, B_226, A_227]: (r1_tarski(k5_relat_1(A_225, k5_relat_1(B_226, k6_relat_1(A_227))), k5_relat_1(A_225, B_226)) | ~v1_relat_1(k5_relat_1(A_225, B_226)) | ~v1_relat_1(B_226) | ~v1_relat_1(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1020])).
% 13.77/6.42  tff(c_7259, plain, (![A_225, A_227, A_36]: (r1_tarski(k5_relat_1(A_225, k7_relat_1(k6_relat_1(A_227), A_36)), k5_relat_1(A_225, k6_relat_1(A_36))) | ~v1_relat_1(k5_relat_1(A_225, k6_relat_1(A_36))) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(A_225) | ~v1_relat_1(k6_relat_1(A_227)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_7197])).
% 13.77/6.42  tff(c_35969, plain, (![A_488, A_489, A_490]: (r1_tarski(k5_relat_1(A_488, k7_relat_1(k6_relat_1(A_489), A_490)), k5_relat_1(A_488, k6_relat_1(A_490))) | ~v1_relat_1(k5_relat_1(A_488, k6_relat_1(A_490))) | ~v1_relat_1(A_488))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_7259])).
% 13.77/6.42  tff(c_36044, plain, (![B_212, A_211]: (r1_tarski(k7_relat_1(k6_relat_1(B_212), A_211), k5_relat_1(k6_relat_1(B_212), k6_relat_1(A_211))) | ~v1_relat_1(k5_relat_1(k6_relat_1(B_212), k6_relat_1(A_211))) | ~v1_relat_1(k6_relat_1(B_212)))), inference(superposition, [status(thm), theory('equality')], [c_14274, c_35969])).
% 13.77/6.42  tff(c_36243, plain, (![B_491, A_492]: (r1_tarski(k7_relat_1(k6_relat_1(B_491), A_492), k7_relat_1(k6_relat_1(A_492), B_491)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3606, c_11943, c_11943, c_36044])).
% 13.77/6.42  tff(c_36350, plain, (![A_1, B_2]: (r1_tarski(k6_relat_1(k3_xboole_0(A_1, B_2)), k7_relat_1(k6_relat_1(B_2), k3_xboole_0(B_2, A_1))))), inference(superposition, [status(thm), theory('equality')], [c_4319, c_36243])).
% 13.77/6.42  tff(c_37180, plain, (![A_495, B_496]: (r1_tarski(k6_relat_1(k3_xboole_0(A_495, B_496)), k7_relat_1(k6_relat_1(B_496), A_495)))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_36350])).
% 13.77/6.42  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.77/6.42  tff(c_37187, plain, (![B_496, A_495]: (k7_relat_1(k6_relat_1(B_496), A_495)=k6_relat_1(k3_xboole_0(A_495, B_496)) | ~r1_tarski(k7_relat_1(k6_relat_1(B_496), A_495), k6_relat_1(k3_xboole_0(A_495, B_496))))), inference(resolution, [status(thm)], [c_37180, c_4])).
% 13.77/6.42  tff(c_37405, plain, (![B_496, A_495]: (k7_relat_1(k6_relat_1(B_496), A_495)=k6_relat_1(k3_xboole_0(A_495, B_496)))), inference(demodulation, [status(thm), theory('equality')], [c_1742, c_37187])).
% 13.77/6.42  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.77/6.42  tff(c_479, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_458, c_46])).
% 13.77/6.42  tff(c_498, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_479])).
% 13.77/6.42  tff(c_37784, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_37405, c_498])).
% 13.77/6.42  tff(c_37813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_37784])).
% 13.77/6.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.77/6.42  
% 13.77/6.42  Inference rules
% 13.77/6.42  ----------------------
% 13.77/6.42  #Ref     : 0
% 13.77/6.42  #Sup     : 9374
% 13.77/6.42  #Fact    : 0
% 13.77/6.42  #Define  : 0
% 13.77/6.42  #Split   : 1
% 13.77/6.42  #Chain   : 0
% 13.77/6.42  #Close   : 0
% 13.77/6.42  
% 13.77/6.42  Ordering : KBO
% 13.77/6.42  
% 13.77/6.42  Simplification rules
% 13.77/6.42  ----------------------
% 13.77/6.42  #Subsume      : 967
% 13.77/6.42  #Demod        : 11512
% 13.77/6.42  #Tautology    : 3879
% 13.77/6.42  #SimpNegUnit  : 0
% 13.77/6.42  #BackRed      : 72
% 13.77/6.42  
% 13.77/6.42  #Partial instantiations: 0
% 13.77/6.42  #Strategies tried      : 1
% 13.77/6.42  
% 13.77/6.42  Timing (in seconds)
% 13.77/6.42  ----------------------
% 13.77/6.42  Preprocessing        : 0.33
% 13.77/6.42  Parsing              : 0.17
% 13.77/6.42  CNF conversion       : 0.02
% 13.77/6.42  Main loop            : 5.31
% 13.77/6.42  Inferencing          : 0.92
% 13.77/6.42  Reduction            : 2.90
% 13.77/6.42  Demodulation         : 2.59
% 13.77/6.42  BG Simplification    : 0.14
% 13.77/6.42  Subsumption          : 1.08
% 13.77/6.42  Abstraction          : 0.24
% 13.77/6.42  MUC search           : 0.00
% 13.77/6.42  Cooper               : 0.00
% 13.77/6.42  Total                : 5.68
% 13.77/6.42  Index Insertion      : 0.00
% 13.87/6.42  Index Deletion       : 0.00
% 13.87/6.42  Index Matching       : 0.00
% 13.87/6.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
