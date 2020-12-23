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
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 10.52s
% Output     : CNFRefutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 293 expanded)
%              Number of leaves         :   32 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  155 ( 493 expanded)
%              Number of equality atoms :   72 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,k1_tarski(B_45)) = A_44
      | r2_hidden(B_45,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_5'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_214,plain,(
    ! [D_70,B_71,A_72] :
      ( r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k3_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_225,plain,(
    ! [A_72,B_71] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_72,B_71)),B_71)
      | k3_xboole_0(A_72,B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_214])).

tff(c_170,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k4_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_347,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_88,B_89)),B_89)
      | k4_xboole_0(A_88,B_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_170])).

tff(c_361,plain,(
    ! [A_22] :
      ( ~ r2_hidden('#skF_5'(A_22),k1_xboole_0)
      | k4_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_347])).

tff(c_408,plain,(
    ! [A_91] :
      ( ~ r2_hidden('#skF_5'(A_91),k1_xboole_0)
      | k1_xboole_0 = A_91 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_361])).

tff(c_425,plain,(
    ! [A_92] : k3_xboole_0(A_92,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_408])).

tff(c_54,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_442,plain,(
    ! [A_92] : k5_xboole_0(A_92,k1_xboole_0) = k4_xboole_0(A_92,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_54])).

tff(c_461,plain,(
    ! [A_92] : k5_xboole_0(A_92,k1_xboole_0) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_442])).

tff(c_202,plain,(
    ! [D_67,A_68,B_69] :
      ( r2_hidden(D_67,A_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_213,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_68,B_69)),A_68)
      | k4_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_202])).

tff(c_463,plain,(
    ! [B_93] : k4_xboole_0(k1_xboole_0,B_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_213,c_408])).

tff(c_70,plain,(
    ! [B_45,A_44] :
      ( ~ r2_hidden(B_45,A_44)
      | k4_xboole_0(A_44,k1_tarski(B_45)) != A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_510,plain,(
    ! [B_45] : ~ r2_hidden(B_45,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_458,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_425])).

tff(c_1556,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden('#skF_1'(A_167,B_168,C_169),B_168)
      | r2_hidden('#skF_2'(A_167,B_168,C_169),C_169)
      | k3_xboole_0(A_167,B_168) = C_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14681,plain,(
    ! [A_453,B_454,A_455,B_456] :
      ( r2_hidden('#skF_2'(A_453,B_454,k3_xboole_0(A_455,B_456)),A_455)
      | r2_hidden('#skF_1'(A_453,B_454,k3_xboole_0(A_455,B_456)),B_454)
      | k3_xboole_0(A_455,B_456) = k3_xboole_0(A_453,B_454) ) ),
    inference(resolution,[status(thm)],[c_1556,c_8])).

tff(c_14914,plain,(
    ! [A_453,B_454,B_2] :
      ( r2_hidden('#skF_2'(A_453,B_454,k3_xboole_0(k1_xboole_0,B_2)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_453,B_454,k1_xboole_0),B_454)
      | k3_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(A_453,B_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_14681])).

tff(c_14980,plain,(
    ! [A_453,B_454] :
      ( r2_hidden('#skF_2'(A_453,B_454,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_453,B_454,k1_xboole_0),B_454)
      | k3_xboole_0(A_453,B_454) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_458,c_14914])).

tff(c_14981,plain,(
    ! [A_453,B_454] :
      ( r2_hidden('#skF_1'(A_453,B_454,k1_xboole_0),B_454)
      | k3_xboole_0(A_453,B_454) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_14980])).

tff(c_2840,plain,(
    ! [A_217,B_218,C_219] :
      ( r2_hidden('#skF_1'(A_217,B_218,C_219),A_217)
      | r2_hidden('#skF_2'(A_217,B_218,C_219),C_219)
      | k3_xboole_0(A_217,B_218) = C_219 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17672,plain,(
    ! [A_492,B_493,B_494,C_495] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_492,B_493),B_494,C_495),B_493)
      | r2_hidden('#skF_2'(k4_xboole_0(A_492,B_493),B_494,C_495),C_495)
      | k3_xboole_0(k4_xboole_0(A_492,B_493),B_494) = C_495 ) ),
    inference(resolution,[status(thm)],[c_2840,c_24])).

tff(c_17687,plain,(
    ! [A_492,B_454] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_492,B_454),B_454,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_492,B_454),B_454) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14981,c_17672])).

tff(c_17758,plain,(
    ! [A_492,B_454] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_492,B_454),B_454,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_454,k4_xboole_0(A_492,B_454)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17687])).

tff(c_17779,plain,(
    ! [B_496,A_497] : k3_xboole_0(B_496,k4_xboole_0(A_497,B_496)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_510,c_17758])).

tff(c_17931,plain,(
    ! [B_496,A_497] : k4_xboole_0(B_496,k4_xboole_0(A_497,B_496)) = k5_xboole_0(B_496,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17779,c_54])).

tff(c_18092,plain,(
    ! [B_498,A_499] : k4_xboole_0(B_498,k4_xboole_0(A_499,B_498)) = B_498 ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_17931])).

tff(c_21320,plain,(
    ! [B_525,A_526] :
      ( k4_xboole_0(k1_tarski(B_525),A_526) = k1_tarski(B_525)
      | r2_hidden(B_525,A_526) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_18092])).

tff(c_74,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_253,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_21542,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_21320,c_253])).

tff(c_21630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_21542])).

tff(c_21631,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_158,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,A_56)
      | ~ r2_hidden(D_55,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_169,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_56,B_57)),A_56)
      | k3_xboole_0(A_56,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_158])).

tff(c_21774,plain,(
    ! [A_539,B_540] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_539,B_540)),B_540)
      | k4_xboole_0(A_539,B_540) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_170])).

tff(c_21786,plain,(
    ! [A_22] :
      ( ~ r2_hidden('#skF_5'(A_22),k1_xboole_0)
      | k4_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_21774])).

tff(c_21802,plain,(
    ! [A_544] :
      ( ~ r2_hidden('#skF_5'(A_544),k1_xboole_0)
      | k1_xboole_0 = A_544 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21786])).

tff(c_21861,plain,(
    ! [B_546] : k3_xboole_0(k1_xboole_0,B_546) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_21802])).

tff(c_143,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_21875,plain,(
    ! [B_546] : k5_xboole_0(B_546,k1_xboole_0) = k4_xboole_0(B_546,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_21861,c_152])).

tff(c_21908,plain,(
    ! [B_546] : k5_xboole_0(B_546,k1_xboole_0) = B_546 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21875])).

tff(c_21729,plain,(
    ! [A_537,B_538] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_537,B_538)),B_538)
      | k3_xboole_0(A_537,B_538) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_214])).

tff(c_21632,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_21706,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21632,c_78])).

tff(c_21713,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_9')
      | ~ r2_hidden(D_14,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21706,c_24])).

tff(c_22194,plain,(
    ! [A_558] :
      ( ~ r2_hidden('#skF_5'(k3_xboole_0(A_558,k1_tarski('#skF_8'))),'#skF_9')
      | k3_xboole_0(A_558,k1_tarski('#skF_8')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_21729,c_21713])).

tff(c_22212,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_22194])).

tff(c_22234,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = k5_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22212,c_54])).

tff(c_22241,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21908,c_22234])).

tff(c_22252,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_22241,c_70])).

tff(c_22268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21631,c_22252])).

tff(c_22269,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_22370,plain,(
    ! [D_580,B_581,A_582] :
      ( r2_hidden(D_580,B_581)
      | ~ r2_hidden(D_580,k3_xboole_0(A_582,B_581)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22381,plain,(
    ! [A_582,B_581] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_582,B_581)),B_581)
      | k3_xboole_0(A_582,B_581) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_22370])).

tff(c_22308,plain,(
    ! [D_567,B_568,A_569] :
      ( ~ r2_hidden(D_567,B_568)
      | ~ r2_hidden(D_567,k4_xboole_0(A_569,B_568)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22559,plain,(
    ! [A_600,B_601] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_600,B_601)),B_601)
      | k4_xboole_0(A_600,B_601) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_22308])).

tff(c_22576,plain,(
    ! [A_22] :
      ( ~ r2_hidden('#skF_5'(A_22),k1_xboole_0)
      | k4_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22559])).

tff(c_22624,plain,(
    ! [A_603] :
      ( ~ r2_hidden('#skF_5'(A_603),k1_xboole_0)
      | k1_xboole_0 = A_603 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22576])).

tff(c_22755,plain,(
    ! [A_609] : k3_xboole_0(A_609,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22381,c_22624])).

tff(c_22775,plain,(
    ! [A_609] : k5_xboole_0(A_609,k1_xboole_0) = k4_xboole_0(A_609,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22755,c_54])).

tff(c_22798,plain,(
    ! [A_609] : k5_xboole_0(A_609,k1_xboole_0) = A_609 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22775])).

tff(c_22296,plain,(
    ! [D_564,A_565,B_566] :
      ( r2_hidden(D_564,A_565)
      | ~ r2_hidden(D_564,k3_xboole_0(A_565,B_566)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22307,plain,(
    ! [A_565,B_566] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_565,B_566)),A_565)
      | k3_xboole_0(A_565,B_566) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_22296])).

tff(c_22464,plain,(
    ! [A_593,B_594] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_593,B_594)),B_594)
      | k3_xboole_0(A_593,B_594) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_22370])).

tff(c_22270,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22318,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22270,c_80])).

tff(c_22322,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_9')
      | ~ r2_hidden(D_14,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22318,c_24])).

tff(c_22941,plain,(
    ! [A_616] :
      ( ~ r2_hidden('#skF_5'(k3_xboole_0(A_616,k1_tarski('#skF_8'))),'#skF_9')
      | k3_xboole_0(A_616,k1_tarski('#skF_8')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22464,c_22322])).

tff(c_22959,plain,(
    k3_xboole_0('#skF_9',k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22307,c_22941])).

tff(c_22982,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = k5_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22959,c_54])).

tff(c_22989,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22798,c_22982])).

tff(c_23003,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_22989,c_70])).

tff(c_23023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22269,c_23003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.52/4.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/4.06  
% 10.52/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/4.06  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 10.52/4.06  
% 10.52/4.06  %Foreground sorts:
% 10.52/4.06  
% 10.52/4.06  
% 10.52/4.06  %Background operators:
% 10.52/4.06  
% 10.52/4.06  
% 10.52/4.06  %Foreground operators:
% 10.52/4.06  tff('#skF_5', type, '#skF_5': $i > $i).
% 10.52/4.06  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.52/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.52/4.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.52/4.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.52/4.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.52/4.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.52/4.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.52/4.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.52/4.06  tff('#skF_7', type, '#skF_7': $i).
% 10.52/4.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.52/4.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.52/4.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.52/4.06  tff('#skF_6', type, '#skF_6': $i).
% 10.52/4.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.52/4.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.52/4.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.52/4.06  tff('#skF_9', type, '#skF_9': $i).
% 10.52/4.06  tff('#skF_8', type, '#skF_8': $i).
% 10.52/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.52/4.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.52/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.52/4.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.52/4.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.52/4.06  
% 10.52/4.08  tff(f_88, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 10.52/4.08  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.52/4.08  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.52/4.08  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.52/4.08  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.52/4.08  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.52/4.08  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.52/4.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.52/4.08  tff(c_76, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.52/4.08  tff(c_132, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_76])).
% 10.52/4.08  tff(c_72, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k1_tarski(B_45))=A_44 | r2_hidden(B_45, A_44))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.52/4.08  tff(c_56, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.52/4.08  tff(c_52, plain, (![A_18]: (r2_hidden('#skF_5'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.52/4.08  tff(c_214, plain, (![D_70, B_71, A_72]: (r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k3_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_225, plain, (![A_72, B_71]: (r2_hidden('#skF_5'(k3_xboole_0(A_72, B_71)), B_71) | k3_xboole_0(A_72, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_214])).
% 10.52/4.08  tff(c_170, plain, (![D_58, B_59, A_60]: (~r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k4_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.52/4.08  tff(c_347, plain, (![A_88, B_89]: (~r2_hidden('#skF_5'(k4_xboole_0(A_88, B_89)), B_89) | k4_xboole_0(A_88, B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_170])).
% 10.52/4.08  tff(c_361, plain, (![A_22]: (~r2_hidden('#skF_5'(A_22), k1_xboole_0) | k4_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_347])).
% 10.52/4.08  tff(c_408, plain, (![A_91]: (~r2_hidden('#skF_5'(A_91), k1_xboole_0) | k1_xboole_0=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_361])).
% 10.52/4.08  tff(c_425, plain, (![A_92]: (k3_xboole_0(A_92, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_408])).
% 10.52/4.08  tff(c_54, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.52/4.08  tff(c_442, plain, (![A_92]: (k5_xboole_0(A_92, k1_xboole_0)=k4_xboole_0(A_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_425, c_54])).
% 10.52/4.08  tff(c_461, plain, (![A_92]: (k5_xboole_0(A_92, k1_xboole_0)=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_442])).
% 10.52/4.08  tff(c_202, plain, (![D_67, A_68, B_69]: (r2_hidden(D_67, A_68) | ~r2_hidden(D_67, k4_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.52/4.08  tff(c_213, plain, (![A_68, B_69]: (r2_hidden('#skF_5'(k4_xboole_0(A_68, B_69)), A_68) | k4_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_202])).
% 10.52/4.08  tff(c_463, plain, (![B_93]: (k4_xboole_0(k1_xboole_0, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_213, c_408])).
% 10.52/4.08  tff(c_70, plain, (![B_45, A_44]: (~r2_hidden(B_45, A_44) | k4_xboole_0(A_44, k1_tarski(B_45))!=A_44)), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.52/4.08  tff(c_510, plain, (![B_45]: (~r2_hidden(B_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_463, c_70])).
% 10.52/4.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.52/4.08  tff(c_458, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_425])).
% 10.52/4.08  tff(c_1556, plain, (![A_167, B_168, C_169]: (r2_hidden('#skF_1'(A_167, B_168, C_169), B_168) | r2_hidden('#skF_2'(A_167, B_168, C_169), C_169) | k3_xboole_0(A_167, B_168)=C_169)), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_14681, plain, (![A_453, B_454, A_455, B_456]: (r2_hidden('#skF_2'(A_453, B_454, k3_xboole_0(A_455, B_456)), A_455) | r2_hidden('#skF_1'(A_453, B_454, k3_xboole_0(A_455, B_456)), B_454) | k3_xboole_0(A_455, B_456)=k3_xboole_0(A_453, B_454))), inference(resolution, [status(thm)], [c_1556, c_8])).
% 10.52/4.08  tff(c_14914, plain, (![A_453, B_454, B_2]: (r2_hidden('#skF_2'(A_453, B_454, k3_xboole_0(k1_xboole_0, B_2)), k1_xboole_0) | r2_hidden('#skF_1'(A_453, B_454, k1_xboole_0), B_454) | k3_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(A_453, B_454))), inference(superposition, [status(thm), theory('equality')], [c_458, c_14681])).
% 10.52/4.08  tff(c_14980, plain, (![A_453, B_454]: (r2_hidden('#skF_2'(A_453, B_454, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_453, B_454, k1_xboole_0), B_454) | k3_xboole_0(A_453, B_454)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_458, c_458, c_14914])).
% 10.52/4.08  tff(c_14981, plain, (![A_453, B_454]: (r2_hidden('#skF_1'(A_453, B_454, k1_xboole_0), B_454) | k3_xboole_0(A_453, B_454)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_510, c_14980])).
% 10.52/4.08  tff(c_2840, plain, (![A_217, B_218, C_219]: (r2_hidden('#skF_1'(A_217, B_218, C_219), A_217) | r2_hidden('#skF_2'(A_217, B_218, C_219), C_219) | k3_xboole_0(A_217, B_218)=C_219)), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.52/4.08  tff(c_17672, plain, (![A_492, B_493, B_494, C_495]: (~r2_hidden('#skF_1'(k4_xboole_0(A_492, B_493), B_494, C_495), B_493) | r2_hidden('#skF_2'(k4_xboole_0(A_492, B_493), B_494, C_495), C_495) | k3_xboole_0(k4_xboole_0(A_492, B_493), B_494)=C_495)), inference(resolution, [status(thm)], [c_2840, c_24])).
% 10.52/4.08  tff(c_17687, plain, (![A_492, B_454]: (r2_hidden('#skF_2'(k4_xboole_0(A_492, B_454), B_454, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_492, B_454), B_454)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14981, c_17672])).
% 10.52/4.08  tff(c_17758, plain, (![A_492, B_454]: (r2_hidden('#skF_2'(k4_xboole_0(A_492, B_454), B_454, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_454, k4_xboole_0(A_492, B_454))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17687])).
% 10.52/4.08  tff(c_17779, plain, (![B_496, A_497]: (k3_xboole_0(B_496, k4_xboole_0(A_497, B_496))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_510, c_17758])).
% 10.52/4.08  tff(c_17931, plain, (![B_496, A_497]: (k4_xboole_0(B_496, k4_xboole_0(A_497, B_496))=k5_xboole_0(B_496, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_17779, c_54])).
% 10.52/4.08  tff(c_18092, plain, (![B_498, A_499]: (k4_xboole_0(B_498, k4_xboole_0(A_499, B_498))=B_498)), inference(demodulation, [status(thm), theory('equality')], [c_461, c_17931])).
% 10.52/4.08  tff(c_21320, plain, (![B_525, A_526]: (k4_xboole_0(k1_tarski(B_525), A_526)=k1_tarski(B_525) | r2_hidden(B_525, A_526))), inference(superposition, [status(thm), theory('equality')], [c_72, c_18092])).
% 10.52/4.08  tff(c_74, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.52/4.08  tff(c_253, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 10.52/4.08  tff(c_21542, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_21320, c_253])).
% 10.52/4.08  tff(c_21630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_21542])).
% 10.52/4.08  tff(c_21631, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_74])).
% 10.52/4.08  tff(c_158, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, A_56) | ~r2_hidden(D_55, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_169, plain, (![A_56, B_57]: (r2_hidden('#skF_5'(k3_xboole_0(A_56, B_57)), A_56) | k3_xboole_0(A_56, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_158])).
% 10.52/4.08  tff(c_21774, plain, (![A_539, B_540]: (~r2_hidden('#skF_5'(k4_xboole_0(A_539, B_540)), B_540) | k4_xboole_0(A_539, B_540)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_170])).
% 10.52/4.08  tff(c_21786, plain, (![A_22]: (~r2_hidden('#skF_5'(A_22), k1_xboole_0) | k4_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_21774])).
% 10.52/4.08  tff(c_21802, plain, (![A_544]: (~r2_hidden('#skF_5'(A_544), k1_xboole_0) | k1_xboole_0=A_544)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_21786])).
% 10.52/4.08  tff(c_21861, plain, (![B_546]: (k3_xboole_0(k1_xboole_0, B_546)=k1_xboole_0)), inference(resolution, [status(thm)], [c_169, c_21802])).
% 10.52/4.08  tff(c_143, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.52/4.08  tff(c_152, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 10.52/4.08  tff(c_21875, plain, (![B_546]: (k5_xboole_0(B_546, k1_xboole_0)=k4_xboole_0(B_546, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21861, c_152])).
% 10.52/4.08  tff(c_21908, plain, (![B_546]: (k5_xboole_0(B_546, k1_xboole_0)=B_546)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_21875])).
% 10.52/4.08  tff(c_21729, plain, (![A_537, B_538]: (r2_hidden('#skF_5'(k3_xboole_0(A_537, B_538)), B_538) | k3_xboole_0(A_537, B_538)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_214])).
% 10.52/4.08  tff(c_21632, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 10.52/4.08  tff(c_78, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.52/4.08  tff(c_21706, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21632, c_78])).
% 10.52/4.08  tff(c_21713, plain, (![D_14]: (~r2_hidden(D_14, '#skF_9') | ~r2_hidden(D_14, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_21706, c_24])).
% 10.52/4.08  tff(c_22194, plain, (![A_558]: (~r2_hidden('#skF_5'(k3_xboole_0(A_558, k1_tarski('#skF_8'))), '#skF_9') | k3_xboole_0(A_558, k1_tarski('#skF_8'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_21729, c_21713])).
% 10.52/4.08  tff(c_22212, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_22194])).
% 10.52/4.08  tff(c_22234, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))=k5_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22212, c_54])).
% 10.52/4.08  tff(c_22241, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_21908, c_22234])).
% 10.52/4.08  tff(c_22252, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_22241, c_70])).
% 10.52/4.08  tff(c_22268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21631, c_22252])).
% 10.52/4.08  tff(c_22269, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 10.52/4.08  tff(c_22370, plain, (![D_580, B_581, A_582]: (r2_hidden(D_580, B_581) | ~r2_hidden(D_580, k3_xboole_0(A_582, B_581)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_22381, plain, (![A_582, B_581]: (r2_hidden('#skF_5'(k3_xboole_0(A_582, B_581)), B_581) | k3_xboole_0(A_582, B_581)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_22370])).
% 10.52/4.08  tff(c_22308, plain, (![D_567, B_568, A_569]: (~r2_hidden(D_567, B_568) | ~r2_hidden(D_567, k4_xboole_0(A_569, B_568)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.52/4.08  tff(c_22559, plain, (![A_600, B_601]: (~r2_hidden('#skF_5'(k4_xboole_0(A_600, B_601)), B_601) | k4_xboole_0(A_600, B_601)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_22308])).
% 10.52/4.08  tff(c_22576, plain, (![A_22]: (~r2_hidden('#skF_5'(A_22), k1_xboole_0) | k4_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_22559])).
% 10.52/4.08  tff(c_22624, plain, (![A_603]: (~r2_hidden('#skF_5'(A_603), k1_xboole_0) | k1_xboole_0=A_603)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_22576])).
% 10.52/4.08  tff(c_22755, plain, (![A_609]: (k3_xboole_0(A_609, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22381, c_22624])).
% 10.52/4.08  tff(c_22775, plain, (![A_609]: (k5_xboole_0(A_609, k1_xboole_0)=k4_xboole_0(A_609, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22755, c_54])).
% 10.52/4.08  tff(c_22798, plain, (![A_609]: (k5_xboole_0(A_609, k1_xboole_0)=A_609)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_22775])).
% 10.52/4.08  tff(c_22296, plain, (![D_564, A_565, B_566]: (r2_hidden(D_564, A_565) | ~r2_hidden(D_564, k3_xboole_0(A_565, B_566)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.52/4.08  tff(c_22307, plain, (![A_565, B_566]: (r2_hidden('#skF_5'(k3_xboole_0(A_565, B_566)), A_565) | k3_xboole_0(A_565, B_566)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_22296])).
% 10.52/4.08  tff(c_22464, plain, (![A_593, B_594]: (r2_hidden('#skF_5'(k3_xboole_0(A_593, B_594)), B_594) | k3_xboole_0(A_593, B_594)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_22370])).
% 10.52/4.08  tff(c_22270, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 10.52/4.08  tff(c_80, plain, (~r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.52/4.08  tff(c_22318, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22270, c_80])).
% 10.52/4.08  tff(c_22322, plain, (![D_14]: (~r2_hidden(D_14, '#skF_9') | ~r2_hidden(D_14, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_22318, c_24])).
% 10.52/4.08  tff(c_22941, plain, (![A_616]: (~r2_hidden('#skF_5'(k3_xboole_0(A_616, k1_tarski('#skF_8'))), '#skF_9') | k3_xboole_0(A_616, k1_tarski('#skF_8'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22464, c_22322])).
% 10.52/4.08  tff(c_22959, plain, (k3_xboole_0('#skF_9', k1_tarski('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22307, c_22941])).
% 10.52/4.08  tff(c_22982, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))=k5_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22959, c_54])).
% 10.52/4.08  tff(c_22989, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_22798, c_22982])).
% 10.52/4.08  tff(c_23003, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_22989, c_70])).
% 10.52/4.08  tff(c_23023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22269, c_23003])).
% 10.52/4.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/4.08  
% 10.52/4.08  Inference rules
% 10.52/4.08  ----------------------
% 10.52/4.08  #Ref     : 0
% 10.52/4.08  #Sup     : 5701
% 10.52/4.08  #Fact    : 2
% 10.52/4.08  #Define  : 0
% 10.52/4.08  #Split   : 6
% 10.52/4.08  #Chain   : 0
% 10.52/4.08  #Close   : 0
% 10.52/4.08  
% 10.52/4.08  Ordering : KBO
% 10.52/4.08  
% 10.52/4.08  Simplification rules
% 10.52/4.08  ----------------------
% 10.52/4.08  #Subsume      : 1928
% 10.52/4.08  #Demod        : 1267
% 10.52/4.08  #Tautology    : 1134
% 10.52/4.08  #SimpNegUnit  : 208
% 10.52/4.08  #BackRed      : 2
% 10.52/4.08  
% 10.52/4.08  #Partial instantiations: 0
% 10.52/4.08  #Strategies tried      : 1
% 10.52/4.08  
% 10.52/4.08  Timing (in seconds)
% 10.52/4.08  ----------------------
% 10.52/4.09  Preprocessing        : 0.36
% 10.52/4.09  Parsing              : 0.18
% 10.52/4.09  CNF conversion       : 0.03
% 10.52/4.09  Main loop            : 2.89
% 10.52/4.09  Inferencing          : 0.76
% 10.52/4.09  Reduction            : 0.88
% 10.52/4.09  Demodulation         : 0.62
% 10.52/4.09  BG Simplification    : 0.10
% 10.52/4.09  Subsumption          : 0.94
% 10.52/4.09  Abstraction          : 0.13
% 10.52/4.09  MUC search           : 0.00
% 10.52/4.09  Cooper               : 0.00
% 10.52/4.09  Total                : 3.29
% 10.52/4.09  Index Insertion      : 0.00
% 10.52/4.09  Index Deletion       : 0.00
% 10.52/4.09  Index Matching       : 0.00
% 10.52/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
