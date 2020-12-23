%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:24 EST 2020

% Result     : Theorem 11.37s
% Output     : CNFRefutation 11.37s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 259 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 333 expanded)
%              Number of equality atoms :   70 ( 170 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_117,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_375,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_274,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_32,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    ! [B_54,A_55] :
      ( r1_xboole_0(B_54,A_55)
      | ~ r1_xboole_0(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [B_36,A_35] : r1_xboole_0(B_36,k4_xboole_0(A_35,B_36)) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_1017,plain,(
    ! [B_108,A_109,C_110] :
      ( r1_xboole_0(B_108,k4_xboole_0(A_109,C_110))
      | ~ r1_xboole_0(A_109,k4_xboole_0(B_108,C_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1042,plain,(
    ! [A_35,B_36] : r1_xboole_0(A_35,k4_xboole_0(B_36,B_36)) ),
    inference(resolution,[status(thm)],[c_101,c_1017])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_62,B_63] : k3_xboole_0(A_62,k2_xboole_0(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_160,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1366,plain,(
    ! [A_131,B_132,C_133] :
      ( k3_xboole_0(A_131,k2_xboole_0(B_132,C_133)) = k3_xboole_0(A_131,C_133)
      | ~ r1_xboole_0(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1474,plain,(
    ! [B_132,C_133] :
      ( k3_xboole_0(k2_xboole_0(B_132,C_133),C_133) = k2_xboole_0(B_132,C_133)
      | ~ r1_xboole_0(k2_xboole_0(B_132,C_133),B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1366])).

tff(c_6958,plain,(
    ! [B_310,C_311] :
      ( k2_xboole_0(B_310,C_311) = C_311
      | ~ r1_xboole_0(k2_xboole_0(B_310,C_311),B_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_4,c_1474])).

tff(c_7040,plain,(
    ! [B_36,C_311] : k2_xboole_0(k4_xboole_0(B_36,B_36),C_311) = C_311 ),
    inference(resolution,[status(thm)],[c_1042,c_6958])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7050,plain,(
    ! [B_312,C_313] : k2_xboole_0(k4_xboole_0(B_312,B_312),C_313) = C_313 ),
    inference(resolution,[status(thm)],[c_1042,c_6958])).

tff(c_7189,plain,(
    ! [B_16,B_312] : k4_xboole_0(B_16,k4_xboole_0(B_312,B_312)) = k2_xboole_0(k4_xboole_0(B_312,B_312),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7050])).

tff(c_7243,plain,(
    ! [B_16,B_312] : k4_xboole_0(B_16,k4_xboole_0(B_312,B_312)) = B_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7040,c_7189])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_194,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    ! [A_68,B_69] : k2_xboole_0(k4_xboole_0(A_68,B_69),A_68) = A_68 ),
    inference(resolution,[status(thm)],[c_14,c_194])).

tff(c_59,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_53,B_52] : r1_tarski(A_53,k2_xboole_0(B_52,A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_34])).

tff(c_244,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_74])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_248,plain,(
    ! [A_70] : k2_xboole_0(A_70,A_70) = A_70 ),
    inference(resolution,[status(thm)],[c_244,c_10])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_810,plain,(
    ! [A_101,B_102] : k2_xboole_0(A_101,k4_xboole_0(B_102,A_101)) = k2_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_844,plain,(
    ! [B_18,A_17] : k2_xboole_0(B_18,k4_xboole_0(A_17,B_18)) = k2_xboole_0(B_18,k2_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_810])).

tff(c_861,plain,(
    ! [B_18,A_17] : k2_xboole_0(B_18,k2_xboole_0(A_17,B_18)) = k2_xboole_0(B_18,A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_844])).

tff(c_7074,plain,(
    ! [C_313,B_312] : k2_xboole_0(C_313,k4_xboole_0(B_312,B_312)) = k2_xboole_0(C_313,C_313) ),
    inference(superposition,[status(thm),theory(equality)],[c_7050,c_861])).

tff(c_7219,plain,(
    ! [C_313,B_312] : k2_xboole_0(C_313,k4_xboole_0(B_312,B_312)) = C_313 ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_7074])).

tff(c_22,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1405,plain,(
    ! [A_131,C_133,B_132] :
      ( k4_xboole_0(A_131,k3_xboole_0(A_131,C_133)) = k4_xboole_0(A_131,k2_xboole_0(B_132,C_133))
      | ~ r1_xboole_0(A_131,B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_22])).

tff(c_18717,plain,(
    ! [A_483,B_484,C_485] :
      ( k4_xboole_0(A_483,k2_xboole_0(B_484,C_485)) = k4_xboole_0(A_483,C_485)
      | ~ r1_xboole_0(A_483,B_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1405])).

tff(c_19046,plain,(
    ! [A_483,B_312,C_313] :
      ( k4_xboole_0(A_483,k4_xboole_0(B_312,B_312)) = k4_xboole_0(A_483,C_313)
      | ~ r1_xboole_0(A_483,C_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7219,c_18717])).

tff(c_19176,plain,(
    ! [A_486,C_487] :
      ( k4_xboole_0(A_486,C_487) = A_486
      | ~ r1_xboole_0(A_486,C_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7243,c_19046])).

tff(c_19281,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_274,c_19176])).

tff(c_19331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_19281])).

tff(c_19332,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_19349,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19332,c_32])).

tff(c_19358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_19349])).

tff(c_19359,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_19370,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19359,c_32])).

tff(c_19378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_19370])).

tff(c_19380,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_19577,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19380,c_40])).

tff(c_19379,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_19975,plain,(
    ! [B_525,A_526,C_527] :
      ( r1_xboole_0(B_525,k4_xboole_0(A_526,C_527))
      | ~ r1_xboole_0(A_526,k4_xboole_0(B_525,C_527)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_19990,plain,(
    ! [A_35,B_36] : r1_xboole_0(A_35,k4_xboole_0(B_36,B_36)) ),
    inference(resolution,[status(thm)],[c_101,c_19975])).

tff(c_19428,plain,(
    ! [A_490,B_491] : k3_xboole_0(A_490,k2_xboole_0(A_490,B_491)) = A_490 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_19437,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19428])).

tff(c_20345,plain,(
    ! [A_547,B_548,C_549] :
      ( k3_xboole_0(A_547,k2_xboole_0(B_548,C_549)) = k3_xboole_0(A_547,C_549)
      | ~ r1_xboole_0(A_547,B_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20444,plain,(
    ! [B_548,C_549] :
      ( k3_xboole_0(k2_xboole_0(B_548,C_549),C_549) = k2_xboole_0(B_548,C_549)
      | ~ r1_xboole_0(k2_xboole_0(B_548,C_549),B_548) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20345])).

tff(c_25446,plain,(
    ! [B_723,C_724] :
      ( k2_xboole_0(B_723,C_724) = C_724
      | ~ r1_xboole_0(k2_xboole_0(B_723,C_724),B_723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19437,c_4,c_20444])).

tff(c_25535,plain,(
    ! [B_36,C_724] : k2_xboole_0(k4_xboole_0(B_36,B_36),C_724) = C_724 ),
    inference(resolution,[status(thm)],[c_19990,c_25446])).

tff(c_25542,plain,(
    ! [B_725,C_726] : k2_xboole_0(k4_xboole_0(B_725,B_725),C_726) = C_726 ),
    inference(resolution,[status(thm)],[c_19990,c_25446])).

tff(c_25626,plain,(
    ! [B_16,B_725] : k4_xboole_0(B_16,k4_xboole_0(B_725,B_725)) = k2_xboole_0(k4_xboole_0(B_725,B_725),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_25542,c_16])).

tff(c_25738,plain,(
    ! [B_16,B_725] : k4_xboole_0(B_16,k4_xboole_0(B_725,B_725)) = B_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25535,c_25626])).

tff(c_19472,plain,(
    ! [A_494,B_495] :
      ( k2_xboole_0(A_494,B_495) = B_495
      | ~ r1_tarski(A_494,B_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19485,plain,(
    ! [A_496,B_497] : k2_xboole_0(k4_xboole_0(A_496,B_497),A_496) = A_496 ),
    inference(resolution,[status(thm)],[c_14,c_19472])).

tff(c_19522,plain,(
    ! [A_498] : r1_tarski(A_498,A_498) ),
    inference(superposition,[status(thm),theory(equality)],[c_19485,c_74])).

tff(c_19526,plain,(
    ! [A_498] : k2_xboole_0(A_498,A_498) = A_498 ),
    inference(resolution,[status(thm)],[c_19522,c_10])).

tff(c_19694,plain,(
    ! [A_513,B_514] : k2_xboole_0(A_513,k4_xboole_0(B_514,A_513)) = k2_xboole_0(A_513,B_514) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_19728,plain,(
    ! [B_18,A_17] : k2_xboole_0(B_18,k4_xboole_0(A_17,B_18)) = k2_xboole_0(B_18,k2_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_19694])).

tff(c_19739,plain,(
    ! [B_18,A_17] : k2_xboole_0(B_18,k2_xboole_0(A_17,B_18)) = k2_xboole_0(B_18,A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_19728])).

tff(c_25592,plain,(
    ! [C_726,B_725] : k2_xboole_0(C_726,k4_xboole_0(B_725,B_725)) = k2_xboole_0(C_726,C_726) ),
    inference(superposition,[status(thm),theory(equality)],[c_25542,c_19739])).

tff(c_25729,plain,(
    ! [C_726,B_725] : k2_xboole_0(C_726,k4_xboole_0(B_725,B_725)) = C_726 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19526,c_25592])).

tff(c_20372,plain,(
    ! [A_547,C_549,B_548] :
      ( k4_xboole_0(A_547,k3_xboole_0(A_547,C_549)) = k4_xboole_0(A_547,k2_xboole_0(B_548,C_549))
      | ~ r1_xboole_0(A_547,B_548) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20345,c_22])).

tff(c_31677,plain,(
    ! [A_820,B_821,C_822] :
      ( k4_xboole_0(A_820,k2_xboole_0(B_821,C_822)) = k4_xboole_0(A_820,C_822)
      | ~ r1_xboole_0(A_820,B_821) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20372])).

tff(c_31986,plain,(
    ! [A_820,B_725,C_726] :
      ( k4_xboole_0(A_820,k4_xboole_0(B_725,B_725)) = k4_xboole_0(A_820,C_726)
      | ~ r1_xboole_0(A_820,C_726) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25729,c_31677])).

tff(c_32108,plain,(
    ! [A_823,C_824] :
      ( k4_xboole_0(A_823,C_824) = A_823
      | ~ r1_xboole_0(A_823,C_824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25738,c_31986])).

tff(c_32228,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_19379,c_32108])).

tff(c_32280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19577,c_32228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:39:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.37/4.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.39  
% 11.37/4.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.40  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.37/4.40  
% 11.37/4.40  %Foreground sorts:
% 11.37/4.40  
% 11.37/4.40  
% 11.37/4.40  %Background operators:
% 11.37/4.40  
% 11.37/4.40  
% 11.37/4.40  %Foreground operators:
% 11.37/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.37/4.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.37/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.37/4.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.37/4.40  tff('#skF_2', type, '#skF_2': $i).
% 11.37/4.40  tff('#skF_3', type, '#skF_3': $i).
% 11.37/4.40  tff('#skF_1', type, '#skF_1': $i).
% 11.37/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.37/4.40  tff('#skF_4', type, '#skF_4': $i).
% 11.37/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.37/4.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.37/4.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.37/4.40  
% 11.37/4.42  tff(f_86, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.37/4.42  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.37/4.42  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.37/4.42  tff(f_81, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.37/4.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.37/4.42  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 11.37/4.42  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.37/4.42  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.37/4.42  tff(f_69, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 11.37/4.42  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.37/4.42  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.37/4.42  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.37/4.42  tff(f_73, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.37/4.42  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 11.37/4.42  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.37/4.42  tff(c_44, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.37/4.42  tff(c_117, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 11.37/4.42  tff(c_42, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.37/4.42  tff(c_375, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_42])).
% 11.37/4.42  tff(c_46, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.37/4.42  tff(c_274, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 11.37/4.42  tff(c_32, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.37/4.42  tff(c_98, plain, (![B_54, A_55]: (r1_xboole_0(B_54, A_55) | ~r1_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.37/4.42  tff(c_101, plain, (![B_36, A_35]: (r1_xboole_0(B_36, k4_xboole_0(A_35, B_36)))), inference(resolution, [status(thm)], [c_32, c_98])).
% 11.37/4.42  tff(c_1017, plain, (![B_108, A_109, C_110]: (r1_xboole_0(B_108, k4_xboole_0(A_109, C_110)) | ~r1_xboole_0(A_109, k4_xboole_0(B_108, C_110)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.37/4.42  tff(c_1042, plain, (![A_35, B_36]: (r1_xboole_0(A_35, k4_xboole_0(B_36, B_36)))), inference(resolution, [status(thm)], [c_101, c_1017])).
% 11.37/4.42  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.37/4.42  tff(c_151, plain, (![A_62, B_63]: (k3_xboole_0(A_62, k2_xboole_0(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.37/4.42  tff(c_160, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 11.37/4.42  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.37/4.42  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.37/4.42  tff(c_1366, plain, (![A_131, B_132, C_133]: (k3_xboole_0(A_131, k2_xboole_0(B_132, C_133))=k3_xboole_0(A_131, C_133) | ~r1_xboole_0(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.37/4.42  tff(c_1474, plain, (![B_132, C_133]: (k3_xboole_0(k2_xboole_0(B_132, C_133), C_133)=k2_xboole_0(B_132, C_133) | ~r1_xboole_0(k2_xboole_0(B_132, C_133), B_132))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1366])).
% 11.37/4.42  tff(c_6958, plain, (![B_310, C_311]: (k2_xboole_0(B_310, C_311)=C_311 | ~r1_xboole_0(k2_xboole_0(B_310, C_311), B_310))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_4, c_1474])).
% 11.37/4.42  tff(c_7040, plain, (![B_36, C_311]: (k2_xboole_0(k4_xboole_0(B_36, B_36), C_311)=C_311)), inference(resolution, [status(thm)], [c_1042, c_6958])).
% 11.37/4.42  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.37/4.42  tff(c_7050, plain, (![B_312, C_313]: (k2_xboole_0(k4_xboole_0(B_312, B_312), C_313)=C_313)), inference(resolution, [status(thm)], [c_1042, c_6958])).
% 11.37/4.42  tff(c_7189, plain, (![B_16, B_312]: (k4_xboole_0(B_16, k4_xboole_0(B_312, B_312))=k2_xboole_0(k4_xboole_0(B_312, B_312), B_16))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7050])).
% 11.37/4.42  tff(c_7243, plain, (![B_16, B_312]: (k4_xboole_0(B_16, k4_xboole_0(B_312, B_312))=B_16)), inference(demodulation, [status(thm), theory('equality')], [c_7040, c_7189])).
% 11.37/4.42  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.37/4.42  tff(c_194, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.37/4.42  tff(c_207, plain, (![A_68, B_69]: (k2_xboole_0(k4_xboole_0(A_68, B_69), A_68)=A_68)), inference(resolution, [status(thm)], [c_14, c_194])).
% 11.37/4.42  tff(c_59, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.37/4.42  tff(c_34, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.37/4.42  tff(c_74, plain, (![A_53, B_52]: (r1_tarski(A_53, k2_xboole_0(B_52, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_34])).
% 11.37/4.42  tff(c_244, plain, (![A_70]: (r1_tarski(A_70, A_70))), inference(superposition, [status(thm), theory('equality')], [c_207, c_74])).
% 11.37/4.42  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.37/4.42  tff(c_248, plain, (![A_70]: (k2_xboole_0(A_70, A_70)=A_70)), inference(resolution, [status(thm)], [c_244, c_10])).
% 11.37/4.42  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.37/4.42  tff(c_810, plain, (![A_101, B_102]: (k2_xboole_0(A_101, k4_xboole_0(B_102, A_101))=k2_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.37/4.42  tff(c_844, plain, (![B_18, A_17]: (k2_xboole_0(B_18, k4_xboole_0(A_17, B_18))=k2_xboole_0(B_18, k2_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_810])).
% 11.37/4.42  tff(c_861, plain, (![B_18, A_17]: (k2_xboole_0(B_18, k2_xboole_0(A_17, B_18))=k2_xboole_0(B_18, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_844])).
% 11.37/4.42  tff(c_7074, plain, (![C_313, B_312]: (k2_xboole_0(C_313, k4_xboole_0(B_312, B_312))=k2_xboole_0(C_313, C_313))), inference(superposition, [status(thm), theory('equality')], [c_7050, c_861])).
% 11.37/4.42  tff(c_7219, plain, (![C_313, B_312]: (k2_xboole_0(C_313, k4_xboole_0(B_312, B_312))=C_313)), inference(demodulation, [status(thm), theory('equality')], [c_248, c_7074])).
% 11.37/4.42  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.37/4.42  tff(c_1405, plain, (![A_131, C_133, B_132]: (k4_xboole_0(A_131, k3_xboole_0(A_131, C_133))=k4_xboole_0(A_131, k2_xboole_0(B_132, C_133)) | ~r1_xboole_0(A_131, B_132))), inference(superposition, [status(thm), theory('equality')], [c_1366, c_22])).
% 11.37/4.42  tff(c_18717, plain, (![A_483, B_484, C_485]: (k4_xboole_0(A_483, k2_xboole_0(B_484, C_485))=k4_xboole_0(A_483, C_485) | ~r1_xboole_0(A_483, B_484))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1405])).
% 11.37/4.42  tff(c_19046, plain, (![A_483, B_312, C_313]: (k4_xboole_0(A_483, k4_xboole_0(B_312, B_312))=k4_xboole_0(A_483, C_313) | ~r1_xboole_0(A_483, C_313))), inference(superposition, [status(thm), theory('equality')], [c_7219, c_18717])).
% 11.37/4.42  tff(c_19176, plain, (![A_486, C_487]: (k4_xboole_0(A_486, C_487)=A_486 | ~r1_xboole_0(A_486, C_487))), inference(demodulation, [status(thm), theory('equality')], [c_7243, c_19046])).
% 11.37/4.42  tff(c_19281, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_274, c_19176])).
% 11.37/4.42  tff(c_19331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_19281])).
% 11.37/4.42  tff(c_19332, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 11.37/4.42  tff(c_19349, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19332, c_32])).
% 11.37/4.42  tff(c_19358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_19349])).
% 11.37/4.42  tff(c_19359, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 11.37/4.42  tff(c_19370, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19359, c_32])).
% 11.37/4.42  tff(c_19378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_19370])).
% 11.37/4.42  tff(c_19380, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 11.37/4.42  tff(c_40, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.37/4.42  tff(c_19577, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19380, c_40])).
% 11.37/4.42  tff(c_19379, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 11.37/4.42  tff(c_19975, plain, (![B_525, A_526, C_527]: (r1_xboole_0(B_525, k4_xboole_0(A_526, C_527)) | ~r1_xboole_0(A_526, k4_xboole_0(B_525, C_527)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.37/4.42  tff(c_19990, plain, (![A_35, B_36]: (r1_xboole_0(A_35, k4_xboole_0(B_36, B_36)))), inference(resolution, [status(thm)], [c_101, c_19975])).
% 11.37/4.42  tff(c_19428, plain, (![A_490, B_491]: (k3_xboole_0(A_490, k2_xboole_0(A_490, B_491))=A_490)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.37/4.42  tff(c_19437, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_19428])).
% 11.37/4.42  tff(c_20345, plain, (![A_547, B_548, C_549]: (k3_xboole_0(A_547, k2_xboole_0(B_548, C_549))=k3_xboole_0(A_547, C_549) | ~r1_xboole_0(A_547, B_548))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.37/4.42  tff(c_20444, plain, (![B_548, C_549]: (k3_xboole_0(k2_xboole_0(B_548, C_549), C_549)=k2_xboole_0(B_548, C_549) | ~r1_xboole_0(k2_xboole_0(B_548, C_549), B_548))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20345])).
% 11.37/4.42  tff(c_25446, plain, (![B_723, C_724]: (k2_xboole_0(B_723, C_724)=C_724 | ~r1_xboole_0(k2_xboole_0(B_723, C_724), B_723))), inference(demodulation, [status(thm), theory('equality')], [c_19437, c_4, c_20444])).
% 11.37/4.42  tff(c_25535, plain, (![B_36, C_724]: (k2_xboole_0(k4_xboole_0(B_36, B_36), C_724)=C_724)), inference(resolution, [status(thm)], [c_19990, c_25446])).
% 11.37/4.42  tff(c_25542, plain, (![B_725, C_726]: (k2_xboole_0(k4_xboole_0(B_725, B_725), C_726)=C_726)), inference(resolution, [status(thm)], [c_19990, c_25446])).
% 11.37/4.42  tff(c_25626, plain, (![B_16, B_725]: (k4_xboole_0(B_16, k4_xboole_0(B_725, B_725))=k2_xboole_0(k4_xboole_0(B_725, B_725), B_16))), inference(superposition, [status(thm), theory('equality')], [c_25542, c_16])).
% 11.37/4.42  tff(c_25738, plain, (![B_16, B_725]: (k4_xboole_0(B_16, k4_xboole_0(B_725, B_725))=B_16)), inference(demodulation, [status(thm), theory('equality')], [c_25535, c_25626])).
% 11.37/4.42  tff(c_19472, plain, (![A_494, B_495]: (k2_xboole_0(A_494, B_495)=B_495 | ~r1_tarski(A_494, B_495))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.37/4.42  tff(c_19485, plain, (![A_496, B_497]: (k2_xboole_0(k4_xboole_0(A_496, B_497), A_496)=A_496)), inference(resolution, [status(thm)], [c_14, c_19472])).
% 11.37/4.42  tff(c_19522, plain, (![A_498]: (r1_tarski(A_498, A_498))), inference(superposition, [status(thm), theory('equality')], [c_19485, c_74])).
% 11.37/4.42  tff(c_19526, plain, (![A_498]: (k2_xboole_0(A_498, A_498)=A_498)), inference(resolution, [status(thm)], [c_19522, c_10])).
% 11.37/4.42  tff(c_19694, plain, (![A_513, B_514]: (k2_xboole_0(A_513, k4_xboole_0(B_514, A_513))=k2_xboole_0(A_513, B_514))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.37/4.42  tff(c_19728, plain, (![B_18, A_17]: (k2_xboole_0(B_18, k4_xboole_0(A_17, B_18))=k2_xboole_0(B_18, k2_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_19694])).
% 11.37/4.42  tff(c_19739, plain, (![B_18, A_17]: (k2_xboole_0(B_18, k2_xboole_0(A_17, B_18))=k2_xboole_0(B_18, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_19728])).
% 11.37/4.42  tff(c_25592, plain, (![C_726, B_725]: (k2_xboole_0(C_726, k4_xboole_0(B_725, B_725))=k2_xboole_0(C_726, C_726))), inference(superposition, [status(thm), theory('equality')], [c_25542, c_19739])).
% 11.37/4.42  tff(c_25729, plain, (![C_726, B_725]: (k2_xboole_0(C_726, k4_xboole_0(B_725, B_725))=C_726)), inference(demodulation, [status(thm), theory('equality')], [c_19526, c_25592])).
% 11.37/4.42  tff(c_20372, plain, (![A_547, C_549, B_548]: (k4_xboole_0(A_547, k3_xboole_0(A_547, C_549))=k4_xboole_0(A_547, k2_xboole_0(B_548, C_549)) | ~r1_xboole_0(A_547, B_548))), inference(superposition, [status(thm), theory('equality')], [c_20345, c_22])).
% 11.37/4.42  tff(c_31677, plain, (![A_820, B_821, C_822]: (k4_xboole_0(A_820, k2_xboole_0(B_821, C_822))=k4_xboole_0(A_820, C_822) | ~r1_xboole_0(A_820, B_821))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20372])).
% 11.37/4.42  tff(c_31986, plain, (![A_820, B_725, C_726]: (k4_xboole_0(A_820, k4_xboole_0(B_725, B_725))=k4_xboole_0(A_820, C_726) | ~r1_xboole_0(A_820, C_726))), inference(superposition, [status(thm), theory('equality')], [c_25729, c_31677])).
% 11.37/4.42  tff(c_32108, plain, (![A_823, C_824]: (k4_xboole_0(A_823, C_824)=A_823 | ~r1_xboole_0(A_823, C_824))), inference(demodulation, [status(thm), theory('equality')], [c_25738, c_31986])).
% 11.37/4.42  tff(c_32228, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_19379, c_32108])).
% 11.37/4.42  tff(c_32280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19577, c_32228])).
% 11.37/4.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.37/4.42  
% 11.37/4.42  Inference rules
% 11.37/4.42  ----------------------
% 11.37/4.42  #Ref     : 0
% 11.37/4.42  #Sup     : 8055
% 11.37/4.42  #Fact    : 0
% 11.37/4.42  #Define  : 0
% 11.37/4.42  #Split   : 3
% 11.37/4.42  #Chain   : 0
% 11.37/4.42  #Close   : 0
% 11.37/4.42  
% 11.37/4.42  Ordering : KBO
% 11.37/4.42  
% 11.37/4.42  Simplification rules
% 11.37/4.42  ----------------------
% 11.37/4.42  #Subsume      : 640
% 11.37/4.42  #Demod        : 6458
% 11.37/4.42  #Tautology    : 4584
% 11.37/4.42  #SimpNegUnit  : 4
% 11.37/4.42  #BackRed      : 29
% 11.37/4.42  
% 11.37/4.42  #Partial instantiations: 0
% 11.37/4.42  #Strategies tried      : 1
% 11.37/4.42  
% 11.37/4.42  Timing (in seconds)
% 11.37/4.42  ----------------------
% 11.37/4.42  Preprocessing        : 0.33
% 11.37/4.42  Parsing              : 0.17
% 11.37/4.42  CNF conversion       : 0.02
% 11.37/4.42  Main loop            : 3.29
% 11.37/4.42  Inferencing          : 0.70
% 11.37/4.42  Reduction            : 1.70
% 11.37/4.42  Demodulation         : 1.48
% 11.37/4.42  BG Simplification    : 0.09
% 11.37/4.42  Subsumption          : 0.62
% 11.37/4.42  Abstraction          : 0.14
% 11.37/4.42  MUC search           : 0.00
% 11.37/4.42  Cooper               : 0.00
% 11.37/4.42  Total                : 3.67
% 11.37/4.42  Index Insertion      : 0.00
% 11.37/4.42  Index Deletion       : 0.00
% 11.37/4.42  Index Matching       : 0.00
% 11.37/4.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
