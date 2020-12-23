%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 490 expanded)
%              Number of leaves         :   21 ( 155 expanded)
%              Depth                    :   10
%              Number of atoms          :  182 (1030 expanded)
%              Number of equality atoms :    5 (  88 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k5_xboole_0(B,C))
      <=> ~ ( r2_hidden(A,B)
          <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_100,plain,(
    ! [D_35,A_36,B_37] :
      ( r2_hidden(D_35,k4_xboole_0(A_36,B_37))
      | r2_hidden(D_35,B_37)
      | ~ r2_hidden(D_35,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),k4_xboole_0(B_28,A_27)) = k5_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,k4_xboole_0(B_30,A_31))
      | r2_hidden(D_29,k5_xboole_0(A_31,B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_89,c_73])).

tff(c_106,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_93])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_106])).

tff(c_58,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_132,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_94,c_58])).

tff(c_133,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_116,c_94,c_48])).

tff(c_68,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,(
    r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_94,c_68])).

tff(c_38,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(B_14,A_13)) = k5_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | r2_hidden(D_38,A_40)
      | ~ r2_hidden(D_38,k2_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [D_41,B_42,A_43] :
      ( r2_hidden(D_41,k4_xboole_0(B_42,A_43))
      | r2_hidden(D_41,k4_xboole_0(A_43,B_42))
      | ~ r2_hidden(D_41,k5_xboole_0(A_43,B_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_120])).

tff(c_147,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_119,c_137])).

tff(c_176,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_24,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_182,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_176,c_24])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_182])).

tff(c_188,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_200,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_188,c_24])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_200])).

tff(c_207,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_206,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_236,plain,(
    ! [D_50,B_51,A_52] :
      ( r2_hidden(D_50,k4_xboole_0(B_51,A_52))
      | r2_hidden(D_50,k4_xboole_0(A_52,B_51))
      | ~ r2_hidden(D_50,k5_xboole_0(A_52,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_120])).

tff(c_246,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_119,c_236])).

tff(c_249,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_249,c_22])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_252])).

tff(c_260,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_264,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_260,c_22])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_264])).

tff(c_273,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_272,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_274,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_296,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,k4_xboole_0(A_60,B_61))
      | r2_hidden(D_59,B_61)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_275,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,k4_xboole_0(A_54,B_55))
      | r2_hidden(D_53,k5_xboole_0(A_54,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_279,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_275,c_73])).

tff(c_299,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_296,c_279])).

tff(c_311,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_299])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_311])).

tff(c_315,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_335,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_315,c_42])).

tff(c_336,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_362,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_315,c_52])).

tff(c_363,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_362])).

tff(c_314,plain,(
    r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_322,plain,(
    ! [D_65,B_66,A_67] :
      ( r2_hidden(D_65,B_66)
      | r2_hidden(D_65,A_67)
      | ~ r2_hidden(D_65,k2_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_385,plain,(
    ! [D_74,B_75,A_76] :
      ( r2_hidden(D_74,k4_xboole_0(B_75,A_76))
      | r2_hidden(D_74,k4_xboole_0(A_76,B_75))
      | ~ r2_hidden(D_74,k5_xboole_0(A_76,B_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_322])).

tff(c_396,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_314,c_385])).

tff(c_398,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_404,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_398,c_24])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_404])).

tff(c_410,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_417,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_410,c_24])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_417])).

tff(c_423,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_424,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_452,plain,(
    ! [D_80,B_81,A_82] :
      ( r2_hidden(D_80,k4_xboole_0(B_81,A_82))
      | r2_hidden(D_80,k4_xboole_0(A_82,B_81))
      | ~ r2_hidden(D_80,k5_xboole_0(A_82,B_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_322])).

tff(c_463,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_314,c_452])).

tff(c_465,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_468,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_465,c_22])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_468])).

tff(c_476,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_480,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_476,c_22])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_480])).

tff(c_489,plain,(
    r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_508,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_40])).

tff(c_509,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_508])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_5',k5_xboole_0('#skF_6','#skF_7'))
    | r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_524,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_50])).

tff(c_525,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_524])).

tff(c_488,plain,(
    r2_hidden('#skF_8',k5_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_510,plain,(
    ! [D_91,B_92,A_93] :
      ( r2_hidden(D_91,B_92)
      | r2_hidden(D_91,A_93)
      | ~ r2_hidden(D_91,k2_xboole_0(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_540,plain,(
    ! [D_97,B_98,A_99] :
      ( r2_hidden(D_97,k4_xboole_0(B_98,A_99))
      | r2_hidden(D_97,k4_xboole_0(A_99,B_98))
      | ~ r2_hidden(D_97,k5_xboole_0(A_99,B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_510])).

tff(c_556,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_488,c_540])).

tff(c_566,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_572,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_566,c_24])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_572])).

tff(c_578,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_616,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_578,c_24])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_616])).

tff(c_622,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_623,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_627,plain,(
    ! [D_103,B_104,A_105] :
      ( r2_hidden(D_103,B_104)
      | r2_hidden(D_103,A_105)
      | ~ r2_hidden(D_103,k2_xboole_0(A_105,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_688,plain,(
    ! [D_112,B_113,A_114] :
      ( r2_hidden(D_112,k4_xboole_0(B_113,A_114))
      | r2_hidden(D_112,k4_xboole_0(A_114,B_113))
      | ~ r2_hidden(D_112,k5_xboole_0(A_114,B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_627])).

tff(c_714,plain,
    ( r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9'))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_488,c_688])).

tff(c_750,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_753,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_750,c_22])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_753])).

tff(c_761,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_765,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_761,c_22])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.78/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.78/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.78/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.78/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.78/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.44  
% 3.03/1.46  tff(f_54, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.03/1.46  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.03/1.46  tff(f_46, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.03/1.46  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.03/1.46  tff(c_62, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_94, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 3.03/1.46  tff(c_100, plain, (![D_35, A_36, B_37]: (r2_hidden(D_35, k4_xboole_0(A_36, B_37)) | r2_hidden(D_35, B_37) | ~r2_hidden(D_35, A_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.46  tff(c_74, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k4_xboole_0(B_28, A_27))=k5_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.03/1.46  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_89, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, k4_xboole_0(B_30, A_31)) | r2_hidden(D_29, k5_xboole_0(A_31, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4])).
% 3.03/1.46  tff(c_60, plain, (~r2_hidden('#skF_5', k5_xboole_0('#skF_6', '#skF_7')) | r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_73, plain, (~r2_hidden('#skF_5', k5_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.03/1.46  tff(c_93, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_89, c_73])).
% 3.03/1.46  tff(c_106, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_100, c_93])).
% 3.03/1.46  tff(c_116, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_94, c_106])).
% 3.03/1.46  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_132, plain, (r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_116, c_94, c_58])).
% 3.03/1.46  tff(c_133, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_132])).
% 3.03/1.46  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_134, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_133, c_116, c_94, c_48])).
% 3.03/1.46  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_119, plain, (r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_116, c_94, c_68])).
% 3.03/1.46  tff(c_38, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(B_14, A_13))=k5_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.03/1.46  tff(c_120, plain, (![D_38, B_39, A_40]: (r2_hidden(D_38, B_39) | r2_hidden(D_38, A_40) | ~r2_hidden(D_38, k2_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_137, plain, (![D_41, B_42, A_43]: (r2_hidden(D_41, k4_xboole_0(B_42, A_43)) | r2_hidden(D_41, k4_xboole_0(A_43, B_42)) | ~r2_hidden(D_41, k5_xboole_0(A_43, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_120])).
% 3.03/1.46  tff(c_147, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9')) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_119, c_137])).
% 3.03/1.46  tff(c_176, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_147])).
% 3.03/1.46  tff(c_24, plain, (![D_12, A_7, B_8]: (r2_hidden(D_12, A_7) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.46  tff(c_182, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_176, c_24])).
% 3.03/1.46  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_182])).
% 3.03/1.46  tff(c_188, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_147])).
% 3.03/1.46  tff(c_200, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_188, c_24])).
% 3.03/1.46  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_200])).
% 3.03/1.46  tff(c_207, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_132])).
% 3.03/1.46  tff(c_206, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_132])).
% 3.03/1.46  tff(c_236, plain, (![D_50, B_51, A_52]: (r2_hidden(D_50, k4_xboole_0(B_51, A_52)) | r2_hidden(D_50, k4_xboole_0(A_52, B_51)) | ~r2_hidden(D_50, k5_xboole_0(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_120])).
% 3.03/1.46  tff(c_246, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9')) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_119, c_236])).
% 3.03/1.46  tff(c_249, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_246])).
% 3.03/1.46  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.46  tff(c_252, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_249, c_22])).
% 3.03/1.46  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_252])).
% 3.03/1.46  tff(c_260, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_246])).
% 3.03/1.46  tff(c_264, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_260, c_22])).
% 3.03/1.46  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_264])).
% 3.03/1.46  tff(c_273, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 3.03/1.46  tff(c_272, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_62])).
% 3.03/1.46  tff(c_274, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_272])).
% 3.03/1.46  tff(c_296, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, k4_xboole_0(A_60, B_61)) | r2_hidden(D_59, B_61) | ~r2_hidden(D_59, A_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.46  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_275, plain, (![D_53, A_54, B_55]: (~r2_hidden(D_53, k4_xboole_0(A_54, B_55)) | r2_hidden(D_53, k5_xboole_0(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 3.03/1.46  tff(c_279, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_275, c_73])).
% 3.03/1.46  tff(c_299, plain, (r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_296, c_279])).
% 3.03/1.46  tff(c_311, plain, (r2_hidden('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_299])).
% 3.03/1.46  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_311])).
% 3.03/1.46  tff(c_315, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_272])).
% 3.03/1.46  tff(c_42, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_335, plain, (r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_315, c_42])).
% 3.03/1.46  tff(c_336, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_335])).
% 3.03/1.46  tff(c_52, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_362, plain, (r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_315, c_52])).
% 3.03/1.46  tff(c_363, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_336, c_362])).
% 3.03/1.46  tff(c_314, plain, (r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_272])).
% 3.03/1.46  tff(c_322, plain, (![D_65, B_66, A_67]: (r2_hidden(D_65, B_66) | r2_hidden(D_65, A_67) | ~r2_hidden(D_65, k2_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_385, plain, (![D_74, B_75, A_76]: (r2_hidden(D_74, k4_xboole_0(B_75, A_76)) | r2_hidden(D_74, k4_xboole_0(A_76, B_75)) | ~r2_hidden(D_74, k5_xboole_0(A_76, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_322])).
% 3.03/1.46  tff(c_396, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9')) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_314, c_385])).
% 3.03/1.46  tff(c_398, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_396])).
% 3.03/1.46  tff(c_404, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_398, c_24])).
% 3.03/1.46  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_404])).
% 3.03/1.46  tff(c_410, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_396])).
% 3.03/1.46  tff(c_417, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_410, c_24])).
% 3.03/1.46  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_417])).
% 3.03/1.46  tff(c_423, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_335])).
% 3.03/1.46  tff(c_424, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_335])).
% 3.03/1.46  tff(c_452, plain, (![D_80, B_81, A_82]: (r2_hidden(D_80, k4_xboole_0(B_81, A_82)) | r2_hidden(D_80, k4_xboole_0(A_82, B_81)) | ~r2_hidden(D_80, k5_xboole_0(A_82, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_322])).
% 3.03/1.46  tff(c_463, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9')) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_314, c_452])).
% 3.03/1.46  tff(c_465, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_463])).
% 3.03/1.46  tff(c_468, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_465, c_22])).
% 3.03/1.46  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_424, c_468])).
% 3.03/1.46  tff(c_476, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_463])).
% 3.03/1.46  tff(c_480, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_476, c_22])).
% 3.03/1.46  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_423, c_480])).
% 3.03/1.46  tff(c_489, plain, (r2_hidden('#skF_5', k5_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 3.03/1.46  tff(c_40, plain, (~r2_hidden('#skF_5', k5_xboole_0('#skF_6', '#skF_7')) | r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_508, plain, (r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_40])).
% 3.03/1.46  tff(c_509, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_508])).
% 3.03/1.46  tff(c_50, plain, (~r2_hidden('#skF_5', k5_xboole_0('#skF_6', '#skF_7')) | r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.46  tff(c_524, plain, (r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_50])).
% 3.03/1.46  tff(c_525, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_509, c_524])).
% 3.03/1.46  tff(c_488, plain, (r2_hidden('#skF_8', k5_xboole_0('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_60])).
% 3.03/1.46  tff(c_510, plain, (![D_91, B_92, A_93]: (r2_hidden(D_91, B_92) | r2_hidden(D_91, A_93) | ~r2_hidden(D_91, k2_xboole_0(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_540, plain, (![D_97, B_98, A_99]: (r2_hidden(D_97, k4_xboole_0(B_98, A_99)) | r2_hidden(D_97, k4_xboole_0(A_99, B_98)) | ~r2_hidden(D_97, k5_xboole_0(A_99, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_510])).
% 3.03/1.46  tff(c_556, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9')) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_488, c_540])).
% 3.03/1.46  tff(c_566, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_556])).
% 3.03/1.46  tff(c_572, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_566, c_24])).
% 3.03/1.46  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_572])).
% 3.03/1.46  tff(c_578, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_556])).
% 3.03/1.46  tff(c_616, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_578, c_24])).
% 3.03/1.46  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_509, c_616])).
% 3.03/1.46  tff(c_622, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_508])).
% 3.03/1.46  tff(c_623, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_508])).
% 3.03/1.46  tff(c_627, plain, (![D_103, B_104, A_105]: (r2_hidden(D_103, B_104) | r2_hidden(D_103, A_105) | ~r2_hidden(D_103, k2_xboole_0(A_105, B_104)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_688, plain, (![D_112, B_113, A_114]: (r2_hidden(D_112, k4_xboole_0(B_113, A_114)) | r2_hidden(D_112, k4_xboole_0(A_114, B_113)) | ~r2_hidden(D_112, k5_xboole_0(A_114, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_627])).
% 3.03/1.46  tff(c_714, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9')) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_488, c_688])).
% 3.03/1.46  tff(c_750, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_714])).
% 3.03/1.46  tff(c_753, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_750, c_22])).
% 3.03/1.46  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_623, c_753])).
% 3.03/1.46  tff(c_761, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_10', '#skF_9'))), inference(splitRight, [status(thm)], [c_714])).
% 3.03/1.46  tff(c_765, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_761, c_22])).
% 3.03/1.46  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_622, c_765])).
% 3.03/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  Inference rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Ref     : 0
% 3.03/1.46  #Sup     : 130
% 3.03/1.46  #Fact    : 0
% 3.03/1.46  #Define  : 0
% 3.03/1.46  #Split   : 14
% 3.03/1.46  #Chain   : 0
% 3.03/1.46  #Close   : 0
% 3.03/1.46  
% 3.03/1.46  Ordering : KBO
% 3.03/1.46  
% 3.03/1.46  Simplification rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Subsume      : 25
% 3.03/1.46  #Demod        : 63
% 3.03/1.46  #Tautology    : 62
% 3.03/1.46  #SimpNegUnit  : 24
% 3.03/1.46  #BackRed      : 0
% 3.03/1.46  
% 3.03/1.46  #Partial instantiations: 0
% 3.03/1.46  #Strategies tried      : 1
% 3.03/1.46  
% 3.03/1.46  Timing (in seconds)
% 3.03/1.46  ----------------------
% 3.03/1.46  Preprocessing        : 0.29
% 3.03/1.46  Parsing              : 0.15
% 3.03/1.46  CNF conversion       : 0.02
% 3.03/1.46  Main loop            : 0.39
% 3.03/1.46  Inferencing          : 0.16
% 3.03/1.46  Reduction            : 0.10
% 3.03/1.46  Demodulation         : 0.06
% 3.03/1.46  BG Simplification    : 0.02
% 3.03/1.46  Subsumption          : 0.08
% 3.03/1.46  Abstraction          : 0.02
% 3.03/1.46  MUC search           : 0.00
% 3.03/1.46  Cooper               : 0.00
% 3.03/1.46  Total                : 0.73
% 3.03/1.46  Index Insertion      : 0.00
% 3.03/1.46  Index Deletion       : 0.00
% 3.03/1.46  Index Matching       : 0.00
% 3.03/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
