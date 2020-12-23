%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:22 EST 2020

% Result     : Theorem 8.10s
% Output     : CNFRefutation 8.30s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 472 expanded)
%              Number of leaves         :   39 ( 163 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 975 expanded)
%              Number of equality atoms :   19 ( 187 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_20 > #skF_18 > #skF_17 > #skF_11 > #skF_15 > #skF_19 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_21 > #skF_9 > #skF_8 > #skF_5 > #skF_22 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
      <=> ( r2_hidden(A,E)
          & r2_hidden(B,F)
          & r2_hidden(C,G)
          & r2_hidden(D,H) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] :
      ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
    <=> ( r2_hidden(A,D)
        & r2_hidden(B,E)
        & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_48,plain,
    ( r2_hidden('#skF_8','#skF_12')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_15','#skF_19') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_30,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_zfmisc_1(k3_zfmisc_1(A_41,B_42,C_43),D_44) = k4_zfmisc_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40) = k3_zfmisc_1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_55,B_56,C_57] : k2_zfmisc_1(k2_zfmisc_1(A_55,B_56),C_57) = k3_zfmisc_1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_38,B_39,C_40,C_57] : k3_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40,C_57) = k2_zfmisc_1(k3_zfmisc_1(A_38,B_39,C_40),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_119,plain,(
    ! [A_38,B_39,C_40,C_57] : k3_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40,C_57) = k4_zfmisc_1(A_38,B_39,C_40,C_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k4_tarski(k4_tarski(A_35,B_36),C_37) = k3_mcart_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_45,B_46,C_47,D_48] : k4_tarski(k4_tarski(k4_tarski(A_45,B_46),C_47),D_48) = k4_mcart_1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_45,B_46,C_47,D_48] : k4_tarski(k3_mcart_1(A_45,B_46,C_47),D_48) = k4_mcart_1(A_45,B_46,C_47,D_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32])).

tff(c_77,plain,(
    ! [A_58,B_59,C_60] : k4_tarski(k4_tarski(A_58,B_59),C_60) = k3_mcart_1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_35,B_36,C_37,C_60] : k3_mcart_1(k4_tarski(A_35,B_36),C_37,C_60) = k4_tarski(k3_mcart_1(A_35,B_36,C_37),C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_77])).

tff(c_150,plain,(
    ! [A_91,B_92,C_93,C_94] : k3_mcart_1(k4_tarski(A_91,B_92),C_93,C_94) = k4_mcart_1(A_91,B_92,C_93,C_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_86])).

tff(c_40,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( r2_hidden(A_49,D_52)
      | ~ r2_hidden(k3_mcart_1(A_49,B_50,C_51),k3_zfmisc_1(D_52,E_53,F_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_423,plain,(
    ! [D_205,F_203,A_206,C_204,E_200,C_202,B_201] :
      ( r2_hidden(k4_tarski(A_206,B_201),D_205)
      | ~ r2_hidden(k4_mcart_1(A_206,B_201,C_204,C_202),k3_zfmisc_1(D_205,E_200,F_203)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_40])).

tff(c_1022,plain,(
    ! [A_375,B_374,C_371,A_372,B_370,C_376,C_373,C_377] :
      ( r2_hidden(k4_tarski(A_375,B_370),k2_zfmisc_1(A_372,B_374))
      | ~ r2_hidden(k4_mcart_1(A_375,B_370,C_371,C_373),k4_zfmisc_1(A_372,B_374,C_376,C_377)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_423])).

tff(c_1042,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k2_zfmisc_1('#skF_19','#skF_20')) ),
    inference(resolution,[status(thm)],[c_148,c_1022])).

tff(c_178,plain,(
    ! [E_95,F_96,A_97,B_98] :
      ( r2_hidden(k4_tarski(E_95,F_96),k2_zfmisc_1(A_97,B_98))
      | ~ r2_hidden(F_96,B_98)
      | ~ r2_hidden(E_95,A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_448,plain,(
    ! [C_226,A_225,A_224,B_227,B_228] :
      ( r2_hidden(k3_mcart_1(A_224,B_228,C_226),k2_zfmisc_1(A_225,B_227))
      | ~ r2_hidden(C_226,B_227)
      | ~ r2_hidden(k4_tarski(A_224,B_228),A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_178])).

tff(c_1389,plain,(
    ! [B_449,C_453,A_448,B_450,C_452,A_451] :
      ( r2_hidden(k3_mcart_1(A_451,B_449,C_453),k3_zfmisc_1(A_448,B_450,C_452))
      | ~ r2_hidden(C_453,C_452)
      | ~ r2_hidden(k4_tarski(A_451,B_449),k2_zfmisc_1(A_448,B_450)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_448])).

tff(c_1413,plain,(
    ! [B_449,C_453,A_448,B_450,C_452,A_451] :
      ( r2_hidden(A_451,A_448)
      | ~ r2_hidden(C_453,C_452)
      | ~ r2_hidden(k4_tarski(A_451,B_449),k2_zfmisc_1(A_448,B_450)) ) ),
    inference(resolution,[status(thm)],[c_1389,c_40])).

tff(c_1620,plain,(
    ! [C_453,C_452] : ~ r2_hidden(C_453,C_452) ),
    inference(splitLeft,[status(thm)],[c_1413])).

tff(c_38,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( r2_hidden(B_50,E_53)
      | ~ r2_hidden(k3_mcart_1(A_49,B_50,C_51),k3_zfmisc_1(D_52,E_53,F_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1412,plain,(
    ! [B_449,C_453,A_448,B_450,C_452,A_451] :
      ( r2_hidden(B_449,B_450)
      | ~ r2_hidden(C_453,C_452)
      | ~ r2_hidden(k4_tarski(A_451,B_449),k2_zfmisc_1(A_448,B_450)) ) ),
    inference(resolution,[status(thm)],[c_1389,c_38])).

tff(c_1418,plain,(
    ! [C_453,C_452] : ~ r2_hidden(C_453,C_452) ),
    inference(splitLeft,[status(thm)],[c_1412])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1418,c_1042])).

tff(c_1477,plain,(
    ! [B_454,B_455,A_456,A_457] :
      ( r2_hidden(B_454,B_455)
      | ~ r2_hidden(k4_tarski(A_456,B_454),k2_zfmisc_1(A_457,B_455)) ) ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_1502,plain,(
    r2_hidden('#skF_16','#skF_20') ),
    inference(resolution,[status(thm)],[c_1042,c_1477])).

tff(c_1675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1620,c_1502])).

tff(c_1677,plain,(
    ! [A_472,A_473,B_474,B_475] :
      ( r2_hidden(A_472,A_473)
      | ~ r2_hidden(k4_tarski(A_472,B_474),k2_zfmisc_1(A_473,B_475)) ) ),
    inference(splitRight,[status(thm)],[c_1413])).

tff(c_1680,plain,(
    r2_hidden('#skF_15','#skF_19') ),
    inference(resolution,[status(thm)],[c_1042,c_1677])).

tff(c_1705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_1680])).

tff(c_1707,plain,(
    r2_hidden('#skF_15','#skF_19') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1706,plain,
    ( ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_18','#skF_22')
    | r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1708,plain,(
    ~ r2_hidden('#skF_18','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_1706])).

tff(c_36,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( r2_hidden(C_51,F_54)
      | ~ r2_hidden(k3_mcart_1(A_49,B_50,C_51),k3_zfmisc_1(D_52,E_53,F_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_191,plain,(
    ! [C_103,D_104,F_102,E_99,A_105,C_101,B_100] :
      ( r2_hidden(C_101,F_102)
      | ~ r2_hidden(k4_mcart_1(A_105,B_100,C_103,C_101),k3_zfmisc_1(D_104,E_99,F_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_36])).

tff(c_1770,plain,(
    ! [C_500,A_494,C_499,A_497,C_498,C_501,B_496,B_495] :
      ( r2_hidden(C_499,C_500)
      | ~ r2_hidden(k4_mcart_1(A_497,B_496,C_501,C_499),k4_zfmisc_1(A_494,B_495,C_498,C_500)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_191])).

tff(c_1779,plain,(
    r2_hidden('#skF_18','#skF_22') ),
    inference(resolution,[status(thm)],[c_148,c_1770])).

tff(c_1783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1708,c_1779])).

tff(c_1784,plain,
    ( ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_1706])).

tff(c_1786,plain,(
    ~ r2_hidden('#skF_16','#skF_20') ),
    inference(splitLeft,[status(thm)],[c_1784])).

tff(c_149,plain,(
    ! [A_35,B_36,C_37,C_60] : k3_mcart_1(k4_tarski(A_35,B_36),C_37,C_60) = k4_mcart_1(A_35,B_36,C_37,C_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_86])).

tff(c_120,plain,(
    ! [A_87,B_88,C_89,C_90] : k3_zfmisc_1(k2_zfmisc_1(A_87,B_88),C_89,C_90) = k4_zfmisc_1(A_87,B_88,C_89,C_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_1895,plain,(
    ! [C_555,A_558,B_553,C_557,C_552,B_556,A_554] :
      ( r2_hidden(A_558,k2_zfmisc_1(A_554,B_556))
      | ~ r2_hidden(k3_mcart_1(A_558,B_553,C_552),k4_zfmisc_1(A_554,B_556,C_555,C_557)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_40])).

tff(c_2554,plain,(
    ! [B_750,C_746,C_752,C_748,A_745,B_751,C_747,A_749] :
      ( r2_hidden(k4_tarski(A_745,B_751),k2_zfmisc_1(A_749,B_750))
      | ~ r2_hidden(k4_mcart_1(A_745,B_751,C_747,C_752),k4_zfmisc_1(A_749,B_750,C_746,C_748)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_1895])).

tff(c_2574,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k2_zfmisc_1('#skF_19','#skF_20')) ),
    inference(resolution,[status(thm)],[c_148,c_2554])).

tff(c_2073,plain,(
    ! [C_623,A_622,B_624,A_621,B_625] :
      ( r2_hidden(k3_mcart_1(A_621,B_625,C_623),k2_zfmisc_1(A_622,B_624))
      | ~ r2_hidden(C_623,B_624)
      | ~ r2_hidden(k4_tarski(A_621,B_625),A_622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_178])).

tff(c_2899,plain,(
    ! [B_815,C_817,B_816,A_813,A_818,C_814] :
      ( r2_hidden(k3_mcart_1(A_818,B_816,C_814),k3_zfmisc_1(A_813,B_815,C_817))
      | ~ r2_hidden(C_814,C_817)
      | ~ r2_hidden(k4_tarski(A_818,B_816),k2_zfmisc_1(A_813,B_815)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2073])).

tff(c_2922,plain,(
    ! [B_815,C_817,B_816,A_813,A_818,C_814] :
      ( r2_hidden(B_816,B_815)
      | ~ r2_hidden(C_814,C_817)
      | ~ r2_hidden(k4_tarski(A_818,B_816),k2_zfmisc_1(A_813,B_815)) ) ),
    inference(resolution,[status(thm)],[c_2899,c_38])).

tff(c_2928,plain,(
    ! [C_814,C_817] : ~ r2_hidden(C_814,C_817) ),
    inference(splitLeft,[status(thm)],[c_2922])).

tff(c_2986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2928,c_2574])).

tff(c_3048,plain,(
    ! [B_819,B_820,A_821,A_822] :
      ( r2_hidden(B_819,B_820)
      | ~ r2_hidden(k4_tarski(A_821,B_819),k2_zfmisc_1(A_822,B_820)) ) ),
    inference(splitRight,[status(thm)],[c_2922])).

tff(c_3051,plain,(
    r2_hidden('#skF_16','#skF_20') ),
    inference(resolution,[status(thm)],[c_2574,c_3048])).

tff(c_3076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1786,c_3051])).

tff(c_3078,plain,(
    r2_hidden('#skF_16','#skF_20') ),
    inference(splitRight,[status(thm)],[c_1784])).

tff(c_3077,plain,
    ( ~ r2_hidden('#skF_17','#skF_21')
    | r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_1784])).

tff(c_3079,plain,(
    ~ r2_hidden('#skF_17','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_3077])).

tff(c_204,plain,(
    ! [F_112,B_110,C_111,A_115,D_114,E_109,C_113] :
      ( r2_hidden(C_113,E_109)
      | ~ r2_hidden(k4_mcart_1(A_115,B_110,C_113,C_111),k3_zfmisc_1(D_114,E_109,F_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_38])).

tff(c_3131,plain,(
    ! [C_834,B_835,C_839,C_836,A_833,A_840,B_837,C_838] :
      ( r2_hidden(C_834,C_836)
      | ~ r2_hidden(k4_mcart_1(A_840,B_837,C_834,C_838),k4_zfmisc_1(A_833,B_835,C_836,C_839)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_204])).

tff(c_3140,plain,(
    r2_hidden('#skF_17','#skF_21') ),
    inference(resolution,[status(thm)],[c_148,c_3131])).

tff(c_3144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3079,c_3140])).

tff(c_3146,plain,(
    r2_hidden('#skF_17','#skF_21') ),
    inference(splitRight,[status(thm)],[c_3077])).

tff(c_1785,plain,(
    r2_hidden('#skF_18','#skF_22') ),
    inference(splitRight,[status(thm)],[c_1706])).

tff(c_50,plain,
    ( r2_hidden('#skF_7','#skF_11')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3170,plain,(
    r2_hidden('#skF_7','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_3078,c_3146,c_1785,c_50])).

tff(c_3145,plain,(
    r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_3077])).

tff(c_46,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3222,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_3078,c_3146,c_1785,c_46])).

tff(c_34,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( r2_hidden(k3_mcart_1(A_49,B_50,C_51),k3_zfmisc_1(D_52,E_53,F_54))
      | ~ r2_hidden(C_51,F_54)
      | ~ r2_hidden(B_50,E_53)
      | ~ r2_hidden(A_49,D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3196,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_3078,c_3146,c_1785,c_44])).

tff(c_3814,plain,(
    ! [F_1044,E_1042,A_1039,C_1040,D_1041,B_1043] :
      ( r2_hidden(k4_tarski(E_1042,F_1044),k4_zfmisc_1(A_1039,B_1043,C_1040,D_1041))
      | ~ r2_hidden(F_1044,D_1041)
      | ~ r2_hidden(E_1042,k3_zfmisc_1(A_1039,B_1043,C_1040)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_178])).

tff(c_6286,plain,(
    ! [A_1445,A_1440,C_1442,D_1438,D_1441,C_1444,B_1443,B_1439] :
      ( r2_hidden(k4_mcart_1(A_1440,B_1439,C_1442,D_1441),k4_zfmisc_1(A_1445,B_1443,C_1444,D_1438))
      | ~ r2_hidden(D_1441,D_1438)
      | ~ r2_hidden(k3_mcart_1(A_1440,B_1439,C_1442),k3_zfmisc_1(A_1445,B_1443,C_1444)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_3814])).

tff(c_42,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14'))
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3292,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_3078,c_3146,c_1785,c_42])).

tff(c_6297,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_6286,c_3292])).

tff(c_6321,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3196,c_6297])).

tff(c_6333,plain,
    ( ~ r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_8','#skF_12')
    | ~ r2_hidden('#skF_7','#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_6321])).

tff(c_6340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_3145,c_3222,c_6333])).

tff(c_6342,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( r2_hidden('#skF_7','#skF_11')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6411,plain,(
    r2_hidden('#skF_7','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_6342,c_60])).

tff(c_58,plain,
    ( r2_hidden('#skF_8','#skF_12')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6406,plain,(
    r2_hidden('#skF_8','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_6342,c_58])).

tff(c_6341,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6421,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_6342,c_54])).

tff(c_6372,plain,(
    ! [E_1450,F_1451,A_1452,B_1453] :
      ( r2_hidden(k4_tarski(E_1450,F_1451),k2_zfmisc_1(A_1452,B_1453))
      | ~ r2_hidden(F_1451,B_1453)
      | ~ r2_hidden(E_1450,A_1452) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7121,plain,(
    ! [C_1702,A_1704,B_1703,A_1700,B_1699,D_1701] :
      ( r2_hidden(k4_mcart_1(A_1700,B_1699,C_1702,D_1701),k2_zfmisc_1(A_1704,B_1703))
      | ~ r2_hidden(D_1701,B_1703)
      | ~ r2_hidden(k3_mcart_1(A_1700,B_1699,C_1702),A_1704) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_6372])).

tff(c_8530,plain,(
    ! [D_1962,A_1959,C_1965,C_1961,D_1960,A_1964,B_1963,B_1966] :
      ( r2_hidden(k4_mcart_1(A_1964,B_1963,C_1965,D_1960),k4_zfmisc_1(A_1959,B_1966,C_1961,D_1962))
      | ~ r2_hidden(D_1960,D_1962)
      | ~ r2_hidden(k3_mcart_1(A_1964,B_1963,C_1965),k3_zfmisc_1(A_1959,B_1966,C_1961)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7121])).

tff(c_52,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14'))
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6576,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_6342,c_52])).

tff(c_8541,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_8530,c_6576])).

tff(c_8568,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_8541])).

tff(c_8581,plain,
    ( ~ r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_8','#skF_12')
    | ~ r2_hidden('#skF_7','#skF_11') ),
    inference(resolution,[status(thm)],[c_34,c_8568])).

tff(c_8588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6411,c_6406,c_6341,c_8581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.10/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.10/2.78  
% 8.10/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.10/2.78  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_20 > #skF_18 > #skF_17 > #skF_11 > #skF_15 > #skF_19 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_21 > #skF_9 > #skF_8 > #skF_5 > #skF_22 > #skF_3 > #skF_12
% 8.10/2.78  
% 8.10/2.78  %Foreground sorts:
% 8.10/2.78  
% 8.10/2.78  
% 8.10/2.78  %Background operators:
% 8.10/2.78  
% 8.10/2.78  
% 8.10/2.78  %Foreground operators:
% 8.10/2.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_20', type, '#skF_20': $i).
% 8.10/2.78  tff('#skF_18', type, '#skF_18': $i).
% 8.10/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.10/2.78  tff('#skF_17', type, '#skF_17': $i).
% 8.10/2.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.10/2.78  tff('#skF_11', type, '#skF_11': $i).
% 8.10/2.78  tff('#skF_15', type, '#skF_15': $i).
% 8.10/2.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.10/2.78  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 8.10/2.78  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_19', type, '#skF_19': $i).
% 8.10/2.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_7', type, '#skF_7': $i).
% 8.10/2.78  tff('#skF_10', type, '#skF_10': $i).
% 8.10/2.78  tff('#skF_16', type, '#skF_16': $i).
% 8.10/2.78  tff('#skF_14', type, '#skF_14': $i).
% 8.10/2.78  tff('#skF_13', type, '#skF_13': $i).
% 8.10/2.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_21', type, '#skF_21': $i).
% 8.10/2.78  tff('#skF_9', type, '#skF_9': $i).
% 8.10/2.78  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_8', type, '#skF_8': $i).
% 8.10/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.10/2.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.10/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.10/2.78  tff('#skF_22', type, '#skF_22': $i).
% 8.10/2.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.10/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.10/2.78  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 8.10/2.78  tff('#skF_12', type, '#skF_12': $i).
% 8.10/2.78  
% 8.30/2.82  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (r2_hidden(k4_mcart_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) <=> (((r2_hidden(A, E) & r2_hidden(B, F)) & r2_hidden(C, G)) & r2_hidden(D, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_mcart_1)).
% 8.30/2.82  tff(f_43, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 8.30/2.82  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.30/2.82  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 8.30/2.82  tff(f_45, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 8.30/2.82  tff(f_53, axiom, (![A, B, C, D, E, F]: (r2_hidden(k3_mcart_1(A, B, C), k3_zfmisc_1(D, E, F)) <=> ((r2_hidden(A, D) & r2_hidden(B, E)) & r2_hidden(C, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_mcart_1)).
% 8.30/2.82  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.30/2.82  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_12') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_306, plain, (~r2_hidden('#skF_15', '#skF_19')), inference(splitLeft, [status(thm)], [c_48])).
% 8.30/2.82  tff(c_56, plain, (r2_hidden('#skF_9', '#skF_13') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_148, plain, (r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.30/2.82  tff(c_30, plain, (![A_41, B_42, C_43, D_44]: (k2_zfmisc_1(k3_zfmisc_1(A_41, B_42, C_43), D_44)=k4_zfmisc_1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.30/2.82  tff(c_28, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)=k3_zfmisc_1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.30/2.82  tff(c_62, plain, (![A_55, B_56, C_57]: (k2_zfmisc_1(k2_zfmisc_1(A_55, B_56), C_57)=k3_zfmisc_1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.30/2.82  tff(c_71, plain, (![A_38, B_39, C_40, C_57]: (k3_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40, C_57)=k2_zfmisc_1(k3_zfmisc_1(A_38, B_39, C_40), C_57))), inference(superposition, [status(thm), theory('equality')], [c_28, c_62])).
% 8.30/2.82  tff(c_119, plain, (![A_38, B_39, C_40, C_57]: (k3_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40, C_57)=k4_zfmisc_1(A_38, B_39, C_40, C_57))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71])).
% 8.30/2.82  tff(c_26, plain, (![A_35, B_36, C_37]: (k4_tarski(k4_tarski(A_35, B_36), C_37)=k3_mcart_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.30/2.82  tff(c_32, plain, (![A_45, B_46, C_47, D_48]: (k4_tarski(k4_tarski(k4_tarski(A_45, B_46), C_47), D_48)=k4_mcart_1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.30/2.82  tff(c_61, plain, (![A_45, B_46, C_47, D_48]: (k4_tarski(k3_mcart_1(A_45, B_46, C_47), D_48)=k4_mcart_1(A_45, B_46, C_47, D_48))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32])).
% 8.30/2.82  tff(c_77, plain, (![A_58, B_59, C_60]: (k4_tarski(k4_tarski(A_58, B_59), C_60)=k3_mcart_1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.30/2.82  tff(c_86, plain, (![A_35, B_36, C_37, C_60]: (k3_mcart_1(k4_tarski(A_35, B_36), C_37, C_60)=k4_tarski(k3_mcart_1(A_35, B_36, C_37), C_60))), inference(superposition, [status(thm), theory('equality')], [c_26, c_77])).
% 8.30/2.82  tff(c_150, plain, (![A_91, B_92, C_93, C_94]: (k3_mcart_1(k4_tarski(A_91, B_92), C_93, C_94)=k4_mcart_1(A_91, B_92, C_93, C_94))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_86])).
% 8.30/2.82  tff(c_40, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (r2_hidden(A_49, D_52) | ~r2_hidden(k3_mcart_1(A_49, B_50, C_51), k3_zfmisc_1(D_52, E_53, F_54)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.30/2.82  tff(c_423, plain, (![D_205, F_203, A_206, C_204, E_200, C_202, B_201]: (r2_hidden(k4_tarski(A_206, B_201), D_205) | ~r2_hidden(k4_mcart_1(A_206, B_201, C_204, C_202), k3_zfmisc_1(D_205, E_200, F_203)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_40])).
% 8.30/2.82  tff(c_1022, plain, (![A_375, B_374, C_371, A_372, B_370, C_376, C_373, C_377]: (r2_hidden(k4_tarski(A_375, B_370), k2_zfmisc_1(A_372, B_374)) | ~r2_hidden(k4_mcart_1(A_375, B_370, C_371, C_373), k4_zfmisc_1(A_372, B_374, C_376, C_377)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_423])).
% 8.30/2.82  tff(c_1042, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k2_zfmisc_1('#skF_19', '#skF_20'))), inference(resolution, [status(thm)], [c_148, c_1022])).
% 8.30/2.82  tff(c_178, plain, (![E_95, F_96, A_97, B_98]: (r2_hidden(k4_tarski(E_95, F_96), k2_zfmisc_1(A_97, B_98)) | ~r2_hidden(F_96, B_98) | ~r2_hidden(E_95, A_97))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.30/2.82  tff(c_448, plain, (![C_226, A_225, A_224, B_227, B_228]: (r2_hidden(k3_mcart_1(A_224, B_228, C_226), k2_zfmisc_1(A_225, B_227)) | ~r2_hidden(C_226, B_227) | ~r2_hidden(k4_tarski(A_224, B_228), A_225))), inference(superposition, [status(thm), theory('equality')], [c_26, c_178])).
% 8.30/2.82  tff(c_1389, plain, (![B_449, C_453, A_448, B_450, C_452, A_451]: (r2_hidden(k3_mcart_1(A_451, B_449, C_453), k3_zfmisc_1(A_448, B_450, C_452)) | ~r2_hidden(C_453, C_452) | ~r2_hidden(k4_tarski(A_451, B_449), k2_zfmisc_1(A_448, B_450)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_448])).
% 8.30/2.82  tff(c_1413, plain, (![B_449, C_453, A_448, B_450, C_452, A_451]: (r2_hidden(A_451, A_448) | ~r2_hidden(C_453, C_452) | ~r2_hidden(k4_tarski(A_451, B_449), k2_zfmisc_1(A_448, B_450)))), inference(resolution, [status(thm)], [c_1389, c_40])).
% 8.30/2.82  tff(c_1620, plain, (![C_453, C_452]: (~r2_hidden(C_453, C_452))), inference(splitLeft, [status(thm)], [c_1413])).
% 8.30/2.82  tff(c_38, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (r2_hidden(B_50, E_53) | ~r2_hidden(k3_mcart_1(A_49, B_50, C_51), k3_zfmisc_1(D_52, E_53, F_54)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.30/2.82  tff(c_1412, plain, (![B_449, C_453, A_448, B_450, C_452, A_451]: (r2_hidden(B_449, B_450) | ~r2_hidden(C_453, C_452) | ~r2_hidden(k4_tarski(A_451, B_449), k2_zfmisc_1(A_448, B_450)))), inference(resolution, [status(thm)], [c_1389, c_38])).
% 8.30/2.82  tff(c_1418, plain, (![C_453, C_452]: (~r2_hidden(C_453, C_452))), inference(splitLeft, [status(thm)], [c_1412])).
% 8.30/2.82  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1418, c_1042])).
% 8.30/2.82  tff(c_1477, plain, (![B_454, B_455, A_456, A_457]: (r2_hidden(B_454, B_455) | ~r2_hidden(k4_tarski(A_456, B_454), k2_zfmisc_1(A_457, B_455)))), inference(splitRight, [status(thm)], [c_1412])).
% 8.30/2.82  tff(c_1502, plain, (r2_hidden('#skF_16', '#skF_20')), inference(resolution, [status(thm)], [c_1042, c_1477])).
% 8.30/2.82  tff(c_1675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1620, c_1502])).
% 8.30/2.82  tff(c_1677, plain, (![A_472, A_473, B_474, B_475]: (r2_hidden(A_472, A_473) | ~r2_hidden(k4_tarski(A_472, B_474), k2_zfmisc_1(A_473, B_475)))), inference(splitRight, [status(thm)], [c_1413])).
% 8.30/2.82  tff(c_1680, plain, (r2_hidden('#skF_15', '#skF_19')), inference(resolution, [status(thm)], [c_1042, c_1677])).
% 8.30/2.82  tff(c_1705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_1680])).
% 8.30/2.82  tff(c_1707, plain, (r2_hidden('#skF_15', '#skF_19')), inference(splitRight, [status(thm)], [c_48])).
% 8.30/2.82  tff(c_1706, plain, (~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_18', '#skF_22') | r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_48])).
% 8.30/2.82  tff(c_1708, plain, (~r2_hidden('#skF_18', '#skF_22')), inference(splitLeft, [status(thm)], [c_1706])).
% 8.30/2.82  tff(c_36, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (r2_hidden(C_51, F_54) | ~r2_hidden(k3_mcart_1(A_49, B_50, C_51), k3_zfmisc_1(D_52, E_53, F_54)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.30/2.82  tff(c_191, plain, (![C_103, D_104, F_102, E_99, A_105, C_101, B_100]: (r2_hidden(C_101, F_102) | ~r2_hidden(k4_mcart_1(A_105, B_100, C_103, C_101), k3_zfmisc_1(D_104, E_99, F_102)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_36])).
% 8.30/2.82  tff(c_1770, plain, (![C_500, A_494, C_499, A_497, C_498, C_501, B_496, B_495]: (r2_hidden(C_499, C_500) | ~r2_hidden(k4_mcart_1(A_497, B_496, C_501, C_499), k4_zfmisc_1(A_494, B_495, C_498, C_500)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_191])).
% 8.30/2.82  tff(c_1779, plain, (r2_hidden('#skF_18', '#skF_22')), inference(resolution, [status(thm)], [c_148, c_1770])).
% 8.30/2.82  tff(c_1783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1708, c_1779])).
% 8.30/2.82  tff(c_1784, plain, (~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_1706])).
% 8.30/2.82  tff(c_1786, plain, (~r2_hidden('#skF_16', '#skF_20')), inference(splitLeft, [status(thm)], [c_1784])).
% 8.30/2.82  tff(c_149, plain, (![A_35, B_36, C_37, C_60]: (k3_mcart_1(k4_tarski(A_35, B_36), C_37, C_60)=k4_mcart_1(A_35, B_36, C_37, C_60))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_86])).
% 8.30/2.82  tff(c_120, plain, (![A_87, B_88, C_89, C_90]: (k3_zfmisc_1(k2_zfmisc_1(A_87, B_88), C_89, C_90)=k4_zfmisc_1(A_87, B_88, C_89, C_90))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71])).
% 8.30/2.82  tff(c_1895, plain, (![C_555, A_558, B_553, C_557, C_552, B_556, A_554]: (r2_hidden(A_558, k2_zfmisc_1(A_554, B_556)) | ~r2_hidden(k3_mcart_1(A_558, B_553, C_552), k4_zfmisc_1(A_554, B_556, C_555, C_557)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_40])).
% 8.30/2.82  tff(c_2554, plain, (![B_750, C_746, C_752, C_748, A_745, B_751, C_747, A_749]: (r2_hidden(k4_tarski(A_745, B_751), k2_zfmisc_1(A_749, B_750)) | ~r2_hidden(k4_mcart_1(A_745, B_751, C_747, C_752), k4_zfmisc_1(A_749, B_750, C_746, C_748)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_1895])).
% 8.30/2.82  tff(c_2574, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k2_zfmisc_1('#skF_19', '#skF_20'))), inference(resolution, [status(thm)], [c_148, c_2554])).
% 8.30/2.82  tff(c_2073, plain, (![C_623, A_622, B_624, A_621, B_625]: (r2_hidden(k3_mcart_1(A_621, B_625, C_623), k2_zfmisc_1(A_622, B_624)) | ~r2_hidden(C_623, B_624) | ~r2_hidden(k4_tarski(A_621, B_625), A_622))), inference(superposition, [status(thm), theory('equality')], [c_26, c_178])).
% 8.30/2.82  tff(c_2899, plain, (![B_815, C_817, B_816, A_813, A_818, C_814]: (r2_hidden(k3_mcart_1(A_818, B_816, C_814), k3_zfmisc_1(A_813, B_815, C_817)) | ~r2_hidden(C_814, C_817) | ~r2_hidden(k4_tarski(A_818, B_816), k2_zfmisc_1(A_813, B_815)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2073])).
% 8.30/2.82  tff(c_2922, plain, (![B_815, C_817, B_816, A_813, A_818, C_814]: (r2_hidden(B_816, B_815) | ~r2_hidden(C_814, C_817) | ~r2_hidden(k4_tarski(A_818, B_816), k2_zfmisc_1(A_813, B_815)))), inference(resolution, [status(thm)], [c_2899, c_38])).
% 8.30/2.82  tff(c_2928, plain, (![C_814, C_817]: (~r2_hidden(C_814, C_817))), inference(splitLeft, [status(thm)], [c_2922])).
% 8.30/2.82  tff(c_2986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2928, c_2574])).
% 8.30/2.82  tff(c_3048, plain, (![B_819, B_820, A_821, A_822]: (r2_hidden(B_819, B_820) | ~r2_hidden(k4_tarski(A_821, B_819), k2_zfmisc_1(A_822, B_820)))), inference(splitRight, [status(thm)], [c_2922])).
% 8.30/2.82  tff(c_3051, plain, (r2_hidden('#skF_16', '#skF_20')), inference(resolution, [status(thm)], [c_2574, c_3048])).
% 8.30/2.82  tff(c_3076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1786, c_3051])).
% 8.30/2.82  tff(c_3078, plain, (r2_hidden('#skF_16', '#skF_20')), inference(splitRight, [status(thm)], [c_1784])).
% 8.30/2.82  tff(c_3077, plain, (~r2_hidden('#skF_17', '#skF_21') | r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_1784])).
% 8.30/2.82  tff(c_3079, plain, (~r2_hidden('#skF_17', '#skF_21')), inference(splitLeft, [status(thm)], [c_3077])).
% 8.30/2.82  tff(c_204, plain, (![F_112, B_110, C_111, A_115, D_114, E_109, C_113]: (r2_hidden(C_113, E_109) | ~r2_hidden(k4_mcart_1(A_115, B_110, C_113, C_111), k3_zfmisc_1(D_114, E_109, F_112)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_38])).
% 8.30/2.82  tff(c_3131, plain, (![C_834, B_835, C_839, C_836, A_833, A_840, B_837, C_838]: (r2_hidden(C_834, C_836) | ~r2_hidden(k4_mcart_1(A_840, B_837, C_834, C_838), k4_zfmisc_1(A_833, B_835, C_836, C_839)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_204])).
% 8.30/2.82  tff(c_3140, plain, (r2_hidden('#skF_17', '#skF_21')), inference(resolution, [status(thm)], [c_148, c_3131])).
% 8.30/2.82  tff(c_3144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3079, c_3140])).
% 8.30/2.82  tff(c_3146, plain, (r2_hidden('#skF_17', '#skF_21')), inference(splitRight, [status(thm)], [c_3077])).
% 8.30/2.82  tff(c_1785, plain, (r2_hidden('#skF_18', '#skF_22')), inference(splitRight, [status(thm)], [c_1706])).
% 8.30/2.82  tff(c_50, plain, (r2_hidden('#skF_7', '#skF_11') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_3170, plain, (r2_hidden('#skF_7', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_3078, c_3146, c_1785, c_50])).
% 8.30/2.82  tff(c_3145, plain, (r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_3077])).
% 8.30/2.82  tff(c_46, plain, (r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_3222, plain, (r2_hidden('#skF_9', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_3078, c_3146, c_1785, c_46])).
% 8.30/2.82  tff(c_34, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (r2_hidden(k3_mcart_1(A_49, B_50, C_51), k3_zfmisc_1(D_52, E_53, F_54)) | ~r2_hidden(C_51, F_54) | ~r2_hidden(B_50, E_53) | ~r2_hidden(A_49, D_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.30/2.82  tff(c_44, plain, (r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_3196, plain, (r2_hidden('#skF_10', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_3078, c_3146, c_1785, c_44])).
% 8.30/2.82  tff(c_3814, plain, (![F_1044, E_1042, A_1039, C_1040, D_1041, B_1043]: (r2_hidden(k4_tarski(E_1042, F_1044), k4_zfmisc_1(A_1039, B_1043, C_1040, D_1041)) | ~r2_hidden(F_1044, D_1041) | ~r2_hidden(E_1042, k3_zfmisc_1(A_1039, B_1043, C_1040)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_178])).
% 8.30/2.82  tff(c_6286, plain, (![A_1445, A_1440, C_1442, D_1438, D_1441, C_1444, B_1443, B_1439]: (r2_hidden(k4_mcart_1(A_1440, B_1439, C_1442, D_1441), k4_zfmisc_1(A_1445, B_1443, C_1444, D_1438)) | ~r2_hidden(D_1441, D_1438) | ~r2_hidden(k3_mcart_1(A_1440, B_1439, C_1442), k3_zfmisc_1(A_1445, B_1443, C_1444)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_3814])).
% 8.30/2.82  tff(c_42, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14')) | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_3292, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_3078, c_3146, c_1785, c_42])).
% 8.30/2.82  tff(c_6297, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_6286, c_3292])).
% 8.30/2.82  tff(c_6321, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_3196, c_6297])).
% 8.30/2.82  tff(c_6333, plain, (~r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_8', '#skF_12') | ~r2_hidden('#skF_7', '#skF_11')), inference(resolution, [status(thm)], [c_34, c_6321])).
% 8.30/2.82  tff(c_6340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3170, c_3145, c_3222, c_6333])).
% 8.30/2.82  tff(c_6342, plain, (~r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(splitRight, [status(thm)], [c_56])).
% 8.30/2.82  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_11') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_6411, plain, (r2_hidden('#skF_7', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_6342, c_60])).
% 8.30/2.82  tff(c_58, plain, (r2_hidden('#skF_8', '#skF_12') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_6406, plain, (r2_hidden('#skF_8', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_6342, c_58])).
% 8.30/2.82  tff(c_6341, plain, (r2_hidden('#skF_9', '#skF_13')), inference(splitRight, [status(thm)], [c_56])).
% 8.30/2.82  tff(c_54, plain, (r2_hidden('#skF_10', '#skF_14') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_6421, plain, (r2_hidden('#skF_10', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_6342, c_54])).
% 8.30/2.82  tff(c_6372, plain, (![E_1450, F_1451, A_1452, B_1453]: (r2_hidden(k4_tarski(E_1450, F_1451), k2_zfmisc_1(A_1452, B_1453)) | ~r2_hidden(F_1451, B_1453) | ~r2_hidden(E_1450, A_1452))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.30/2.82  tff(c_7121, plain, (![C_1702, A_1704, B_1703, A_1700, B_1699, D_1701]: (r2_hidden(k4_mcart_1(A_1700, B_1699, C_1702, D_1701), k2_zfmisc_1(A_1704, B_1703)) | ~r2_hidden(D_1701, B_1703) | ~r2_hidden(k3_mcart_1(A_1700, B_1699, C_1702), A_1704))), inference(superposition, [status(thm), theory('equality')], [c_61, c_6372])).
% 8.30/2.82  tff(c_8530, plain, (![D_1962, A_1959, C_1965, C_1961, D_1960, A_1964, B_1963, B_1966]: (r2_hidden(k4_mcart_1(A_1964, B_1963, C_1965, D_1960), k4_zfmisc_1(A_1959, B_1966, C_1961, D_1962)) | ~r2_hidden(D_1960, D_1962) | ~r2_hidden(k3_mcart_1(A_1964, B_1963, C_1965), k3_zfmisc_1(A_1959, B_1966, C_1961)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_7121])).
% 8.30/2.82  tff(c_52, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14')) | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.30/2.82  tff(c_6576, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_6342, c_52])).
% 8.30/2.82  tff(c_8541, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_8530, c_6576])).
% 8.30/2.82  tff(c_8568, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_6421, c_8541])).
% 8.30/2.82  tff(c_8581, plain, (~r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_8', '#skF_12') | ~r2_hidden('#skF_7', '#skF_11')), inference(resolution, [status(thm)], [c_34, c_8568])).
% 8.30/2.82  tff(c_8588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6411, c_6406, c_6341, c_8581])).
% 8.30/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.30/2.82  
% 8.30/2.82  Inference rules
% 8.30/2.82  ----------------------
% 8.30/2.82  #Ref     : 0
% 8.30/2.82  #Sup     : 2012
% 8.30/2.82  #Fact    : 0
% 8.30/2.82  #Define  : 0
% 8.30/2.82  #Split   : 31
% 8.30/2.82  #Chain   : 0
% 8.30/2.82  #Close   : 0
% 8.30/2.82  
% 8.30/2.82  Ordering : KBO
% 8.30/2.82  
% 8.30/2.82  Simplification rules
% 8.30/2.82  ----------------------
% 8.30/2.82  #Subsume      : 1624
% 8.30/2.82  #Demod        : 1163
% 8.30/2.82  #Tautology    : 340
% 8.30/2.82  #SimpNegUnit  : 922
% 8.30/2.82  #BackRed      : 171
% 8.30/2.82  
% 8.30/2.82  #Partial instantiations: 0
% 8.30/2.82  #Strategies tried      : 1
% 8.30/2.82  
% 8.30/2.82  Timing (in seconds)
% 8.30/2.82  ----------------------
% 8.30/2.83  Preprocessing        : 0.32
% 8.30/2.83  Parsing              : 0.16
% 8.30/2.83  CNF conversion       : 0.03
% 8.30/2.83  Main loop            : 1.71
% 8.30/2.83  Inferencing          : 0.64
% 8.30/2.83  Reduction            : 0.53
% 8.30/2.83  Demodulation         : 0.38
% 8.30/2.83  BG Simplification    : 0.07
% 8.30/2.83  Subsumption          : 0.37
% 8.30/2.83  Abstraction          : 0.09
% 8.30/2.83  MUC search           : 0.00
% 8.30/2.83  Cooper               : 0.00
% 8.30/2.83  Total                : 2.09
% 8.30/2.83  Index Insertion      : 0.00
% 8.30/2.83  Index Deletion       : 0.00
% 8.30/2.83  Index Matching       : 0.00
% 8.30/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
