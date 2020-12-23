%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:22 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 781 expanded)
%              Number of leaves         :   41 ( 266 expanded)
%              Depth                    :   14
%              Number of atoms          :  286 (1630 expanded)
%              Number of equality atoms :   52 ( 472 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_20 > #skF_18 > #skF_17 > #skF_11 > #skF_15 > #skF_19 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_21 > #skF_9 > #skF_8 > #skF_5 > #skF_22 > #skF_3 > #skF_12

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

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

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
      <=> ( r2_hidden(A,E)
          & r2_hidden(B,F)
          & r2_hidden(C,G)
          & r2_hidden(D,H) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_44,plain,
    ( r2_hidden('#skF_8','#skF_12')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_332,plain,(
    ~ r2_hidden('#skF_15','#skF_19') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,(
    r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_129,plain,(
    ! [A_67,B_68,C_69,D_70] : k4_tarski(k3_mcart_1(A_67,B_68,C_69),D_70) = k4_mcart_1(A_67,B_68,C_69,D_70) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_49,B_50] : k1_mcart_1(k4_tarski(A_49,B_50)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,(
    ! [A_67,B_68,C_69,D_70] : k1_mcart_1(k4_mcart_1(A_67,B_68,C_69,D_70)) = k3_mcart_1(A_67,B_68,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_34])).

tff(c_32,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48) = k4_zfmisc_1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_440,plain,(
    ! [A_152,B_153,D_154] :
      ( k4_tarski('#skF_5'(A_152,B_153,k2_zfmisc_1(A_152,B_153),D_154),'#skF_6'(A_152,B_153,k2_zfmisc_1(A_152,B_153),D_154)) = D_154
      | ~ r2_hidden(D_154,k2_zfmisc_1(A_152,B_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_486,plain,(
    ! [A_155,B_156,D_157] :
      ( '#skF_5'(A_155,B_156,k2_zfmisc_1(A_155,B_156),D_157) = k1_mcart_1(D_157)
      | ~ r2_hidden(D_157,k2_zfmisc_1(A_155,B_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_34])).

tff(c_510,plain,(
    ! [D_48,D_157,C_47,A_45,B_46] :
      ( '#skF_5'(k3_zfmisc_1(A_45,B_46,C_47),D_48,k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48),D_157) = k1_mcart_1(D_157)
      | ~ r2_hidden(D_157,k4_zfmisc_1(A_45,B_46,C_47,D_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_486])).

tff(c_1192,plain,(
    ! [D_274,C_278,B_275,A_276,D_277] :
      ( '#skF_5'(k3_zfmisc_1(A_276,B_275,C_278),D_277,k4_zfmisc_1(A_276,B_275,C_278,D_277),D_274) = k1_mcart_1(D_274)
      | ~ r2_hidden(D_274,k4_zfmisc_1(A_276,B_275,C_278,D_277)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_510])).

tff(c_240,plain,(
    ! [A_95,B_96,D_97] :
      ( r2_hidden('#skF_5'(A_95,B_96,k2_zfmisc_1(A_95,B_96),D_97),A_95)
      | ~ r2_hidden(D_97,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_243,plain,(
    ! [D_48,C_47,A_45,B_46,D_97] :
      ( r2_hidden('#skF_5'(k3_zfmisc_1(A_45,B_46,C_47),D_48,k4_zfmisc_1(A_45,B_46,C_47,D_48),D_97),k3_zfmisc_1(A_45,B_46,C_47))
      | ~ r2_hidden(D_97,k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_240])).

tff(c_247,plain,(
    ! [D_48,C_47,A_45,B_46,D_97] :
      ( r2_hidden('#skF_5'(k3_zfmisc_1(A_45,B_46,C_47),D_48,k4_zfmisc_1(A_45,B_46,C_47,D_48),D_97),k3_zfmisc_1(A_45,B_46,C_47))
      | ~ r2_hidden(D_97,k4_zfmisc_1(A_45,B_46,C_47,D_48)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_1386,plain,(
    ! [D_303,B_302,D_299,C_300,A_301] :
      ( r2_hidden(k1_mcart_1(D_303),k3_zfmisc_1(A_301,B_302,C_300))
      | ~ r2_hidden(D_303,k4_zfmisc_1(A_301,B_302,C_300,D_299))
      | ~ r2_hidden(D_303,k4_zfmisc_1(A_301,B_302,C_300,D_299)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_247])).

tff(c_1426,plain,
    ( r2_hidden(k1_mcart_1(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18')),k3_zfmisc_1('#skF_19','#skF_20','#skF_21'))
    | ~ r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(resolution,[status(thm)],[c_165,c_1386])).

tff(c_1445,plain,(
    r2_hidden(k3_mcart_1('#skF_15','#skF_16','#skF_17'),k3_zfmisc_1('#skF_19','#skF_20','#skF_21')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_138,c_1426])).

tff(c_75,plain,(
    ! [A_55,B_56,C_57] : k4_tarski(k4_tarski(A_55,B_56),C_57) = k3_mcart_1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_55,B_56,C_57] : k1_mcart_1(k3_mcart_1(A_55,B_56,C_57)) = k4_tarski(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_34])).

tff(c_28,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40) = k3_zfmisc_1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_512,plain,(
    ! [A_38,B_39,C_40,D_157] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_157) = k1_mcart_1(D_157)
      | ~ r2_hidden(D_157,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_486])).

tff(c_526,plain,(
    ! [A_38,B_39,C_40,D_157] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_157) = k1_mcart_1(D_157)
      | ~ r2_hidden(D_157,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_512])).

tff(c_246,plain,(
    ! [A_38,B_39,C_40,D_97] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_97),k2_zfmisc_1(A_38,B_39))
      | ~ r2_hidden(D_97,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_240])).

tff(c_991,plain,(
    ! [A_242,B_243,C_244,D_245] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_242,B_243),C_244,k3_zfmisc_1(A_242,B_243,C_244),D_245),k2_zfmisc_1(A_242,B_243))
      | ~ r2_hidden(D_245,k3_zfmisc_1(A_242,B_243,C_244)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_246])).

tff(c_998,plain,(
    ! [D_157,A_38,B_39,C_40] :
      ( r2_hidden(k1_mcart_1(D_157),k2_zfmisc_1(A_38,B_39))
      | ~ r2_hidden(D_157,k3_zfmisc_1(A_38,B_39,C_40))
      | ~ r2_hidden(D_157,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_991])).

tff(c_1447,plain,
    ( r2_hidden(k1_mcart_1(k3_mcart_1('#skF_15','#skF_16','#skF_17')),k2_zfmisc_1('#skF_19','#skF_20'))
    | ~ r2_hidden(k3_mcart_1('#skF_15','#skF_16','#skF_17'),k3_zfmisc_1('#skF_19','#skF_20','#skF_21')) ),
    inference(resolution,[status(thm)],[c_1445,c_998])).

tff(c_1452,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k2_zfmisc_1('#skF_19','#skF_20')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_84,c_1447])).

tff(c_461,plain,(
    ! [A_152,B_153,D_154] :
      ( '#skF_5'(A_152,B_153,k2_zfmisc_1(A_152,B_153),D_154) = k1_mcart_1(D_154)
      | ~ r2_hidden(D_154,k2_zfmisc_1(A_152,B_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_34])).

tff(c_1459,plain,(
    '#skF_5'('#skF_19','#skF_20',k2_zfmisc_1('#skF_19','#skF_20'),k4_tarski('#skF_15','#skF_16')) = k1_mcart_1(k4_tarski('#skF_15','#skF_16')) ),
    inference(resolution,[status(thm)],[c_1452,c_461])).

tff(c_1463,plain,(
    '#skF_5'('#skF_19','#skF_20',k2_zfmisc_1('#skF_19','#skF_20'),k4_tarski('#skF_15','#skF_16')) = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1459])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1501,plain,
    ( r2_hidden('#skF_15','#skF_19')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k2_zfmisc_1('#skF_19','#skF_20')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_8])).

tff(c_1514,plain,(
    r2_hidden('#skF_15','#skF_19') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1501])).

tff(c_1516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_1514])).

tff(c_1518,plain,(
    r2_hidden('#skF_15','#skF_19') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1517,plain,
    ( ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_18','#skF_22')
    | r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1519,plain,(
    ~ r2_hidden('#skF_18','#skF_22') ),
    inference(splitLeft,[status(thm)],[c_1517])).

tff(c_36,plain,(
    ! [A_49,B_50] : k2_mcart_1(k4_tarski(A_49,B_50)) = B_50 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    ! [A_67,B_68,C_69,D_70] : k2_mcart_1(k4_mcart_1(A_67,B_68,C_69,D_70)) = D_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_36])).

tff(c_114,plain,(
    ! [A_64,B_65,C_66] : k2_zfmisc_1(k2_zfmisc_1(A_64,B_65),C_66) = k3_zfmisc_1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_38,B_39,C_40,C_66] : k3_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40,C_66) = k2_zfmisc_1(k3_zfmisc_1(A_38,B_39,C_40),C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_114])).

tff(c_178,plain,(
    ! [A_38,B_39,C_40,C_66] : k3_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40,C_66) = k4_zfmisc_1(A_38,B_39,C_40,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_123])).

tff(c_1631,plain,(
    ! [A_340,B_341,D_342] :
      ( k4_tarski('#skF_5'(A_340,B_341,k2_zfmisc_1(A_340,B_341),D_342),'#skF_6'(A_340,B_341,k2_zfmisc_1(A_340,B_341),D_342)) = D_342
      | ~ r2_hidden(D_342,k2_zfmisc_1(A_340,B_341)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1718,plain,(
    ! [A_346,B_347,D_348] :
      ( '#skF_6'(A_346,B_347,k2_zfmisc_1(A_346,B_347),D_348) = k2_mcart_1(D_348)
      | ~ r2_hidden(D_348,k2_zfmisc_1(A_346,B_347)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1631,c_36])).

tff(c_1744,plain,(
    ! [A_38,B_39,C_40,D_348] :
      ( '#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_348) = k2_mcart_1(D_348)
      | ~ r2_hidden(D_348,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1718])).

tff(c_1963,plain,(
    ! [A_385,B_386,C_387,D_388] :
      ( '#skF_6'(k2_zfmisc_1(A_385,B_386),C_387,k3_zfmisc_1(A_385,B_386,C_387),D_388) = k2_mcart_1(D_388)
      | ~ r2_hidden(D_388,k3_zfmisc_1(A_385,B_386,C_387)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1744])).

tff(c_250,plain,(
    ! [A_98,B_99,D_100] :
      ( r2_hidden('#skF_6'(A_98,B_99,k2_zfmisc_1(A_98,B_99),D_100),B_99)
      | ~ r2_hidden(D_100,k2_zfmisc_1(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,(
    ! [A_38,B_39,C_40,D_100] :
      ( r2_hidden('#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_100),C_40)
      | ~ r2_hidden(D_100,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_250])).

tff(c_258,plain,(
    ! [A_38,B_39,C_40,D_100] :
      ( r2_hidden('#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_100),C_40)
      | ~ r2_hidden(D_100,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_256])).

tff(c_1991,plain,(
    ! [D_389,C_390,A_391,B_392] :
      ( r2_hidden(k2_mcart_1(D_389),C_390)
      | ~ r2_hidden(D_389,k3_zfmisc_1(A_391,B_392,C_390))
      | ~ r2_hidden(D_389,k3_zfmisc_1(A_391,B_392,C_390)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_258])).

tff(c_2018,plain,(
    ! [B_39,A_38,C_66,C_40,D_389] :
      ( r2_hidden(k2_mcart_1(D_389),C_66)
      | ~ r2_hidden(D_389,k4_zfmisc_1(A_38,B_39,C_40,C_66))
      | ~ r2_hidden(D_389,k3_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40,C_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1991])).

tff(c_2032,plain,(
    ! [C_396,D_397,B_395,C_394,A_393] :
      ( r2_hidden(k2_mcart_1(D_397),C_394)
      | ~ r2_hidden(D_397,k4_zfmisc_1(A_393,B_395,C_396,C_394))
      | ~ r2_hidden(D_397,k4_zfmisc_1(A_393,B_395,C_396,C_394)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_2018])).

tff(c_2061,plain,
    ( r2_hidden(k2_mcart_1(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18')),'#skF_22')
    | ~ r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(resolution,[status(thm)],[c_165,c_2032])).

tff(c_2075,plain,(
    r2_hidden('#skF_18','#skF_22') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_141,c_2061])).

tff(c_2077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1519,c_2075])).

tff(c_2078,plain,
    ( ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_2080,plain,(
    ~ r2_hidden('#skF_16','#skF_20') ),
    inference(splitLeft,[status(thm)],[c_2078])).

tff(c_2193,plain,(
    ! [A_434,B_435,D_436] :
      ( k4_tarski('#skF_5'(A_434,B_435,k2_zfmisc_1(A_434,B_435),D_436),'#skF_6'(A_434,B_435,k2_zfmisc_1(A_434,B_435),D_436)) = D_436
      | ~ r2_hidden(D_436,k2_zfmisc_1(A_434,B_435)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2239,plain,(
    ! [A_437,B_438,D_439] :
      ( '#skF_5'(A_437,B_438,k2_zfmisc_1(A_437,B_438),D_439) = k1_mcart_1(D_439)
      | ~ r2_hidden(D_439,k2_zfmisc_1(A_437,B_438)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_34])).

tff(c_2263,plain,(
    ! [D_439,D_48,C_47,A_45,B_46] :
      ( '#skF_5'(k3_zfmisc_1(A_45,B_46,C_47),D_48,k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48),D_439) = k1_mcart_1(D_439)
      | ~ r2_hidden(D_439,k4_zfmisc_1(A_45,B_46,C_47,D_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2239])).

tff(c_2278,plain,(
    ! [D_439,D_48,C_47,A_45,B_46] :
      ( '#skF_5'(k3_zfmisc_1(A_45,B_46,C_47),D_48,k4_zfmisc_1(A_45,B_46,C_47,D_48),D_439) = k1_mcart_1(D_439)
      | ~ r2_hidden(D_439,k4_zfmisc_1(A_45,B_46,C_47,D_48)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2263])).

tff(c_3108,plain,(
    ! [B_576,D_578,C_579,A_577,D_580] :
      ( r2_hidden('#skF_5'(k3_zfmisc_1(A_577,B_576,C_579),D_578,k4_zfmisc_1(A_577,B_576,C_579,D_578),D_580),k3_zfmisc_1(A_577,B_576,C_579))
      | ~ r2_hidden(D_580,k4_zfmisc_1(A_577,B_576,C_579,D_578)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_243])).

tff(c_3240,plain,(
    ! [D_594,C_595,D_592,B_591,A_593] :
      ( r2_hidden(k1_mcart_1(D_592),k3_zfmisc_1(A_593,B_591,C_595))
      | ~ r2_hidden(D_592,k4_zfmisc_1(A_593,B_591,C_595,D_594))
      | ~ r2_hidden(D_592,k4_zfmisc_1(A_593,B_591,C_595,D_594)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2278,c_3108])).

tff(c_3280,plain,
    ( r2_hidden(k1_mcart_1(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18')),k3_zfmisc_1('#skF_19','#skF_20','#skF_21'))
    | ~ r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(resolution,[status(thm)],[c_165,c_3240])).

tff(c_3299,plain,(
    r2_hidden(k3_mcart_1('#skF_15','#skF_16','#skF_17'),k3_zfmisc_1('#skF_19','#skF_20','#skF_21')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_138,c_3280])).

tff(c_2265,plain,(
    ! [A_38,B_39,C_40,D_439] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_439) = k1_mcart_1(D_439)
      | ~ r2_hidden(D_439,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2239])).

tff(c_2279,plain,(
    ! [A_38,B_39,C_40,D_439] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_439) = k1_mcart_1(D_439)
      | ~ r2_hidden(D_439,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2265])).

tff(c_2747,plain,(
    ! [A_524,B_525,C_526,D_527] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_524,B_525),C_526,k3_zfmisc_1(A_524,B_525,C_526),D_527),k2_zfmisc_1(A_524,B_525))
      | ~ r2_hidden(D_527,k3_zfmisc_1(A_524,B_525,C_526)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_246])).

tff(c_2754,plain,(
    ! [D_439,A_38,B_39,C_40] :
      ( r2_hidden(k1_mcart_1(D_439),k2_zfmisc_1(A_38,B_39))
      | ~ r2_hidden(D_439,k3_zfmisc_1(A_38,B_39,C_40))
      | ~ r2_hidden(D_439,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2279,c_2747])).

tff(c_3301,plain,
    ( r2_hidden(k1_mcart_1(k3_mcart_1('#skF_15','#skF_16','#skF_17')),k2_zfmisc_1('#skF_19','#skF_20'))
    | ~ r2_hidden(k3_mcart_1('#skF_15','#skF_16','#skF_17'),k3_zfmisc_1('#skF_19','#skF_20','#skF_21')) ),
    inference(resolution,[status(thm)],[c_3299,c_2754])).

tff(c_3306,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k2_zfmisc_1('#skF_19','#skF_20')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3299,c_84,c_3301])).

tff(c_2217,plain,(
    ! [A_434,B_435,D_436] :
      ( '#skF_6'(A_434,B_435,k2_zfmisc_1(A_434,B_435),D_436) = k2_mcart_1(D_436)
      | ~ r2_hidden(D_436,k2_zfmisc_1(A_434,B_435)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_36])).

tff(c_3311,plain,(
    '#skF_6'('#skF_19','#skF_20',k2_zfmisc_1('#skF_19','#skF_20'),k4_tarski('#skF_15','#skF_16')) = k2_mcart_1(k4_tarski('#skF_15','#skF_16')) ),
    inference(resolution,[status(thm)],[c_3306,c_2217])).

tff(c_3315,plain,(
    '#skF_6'('#skF_19','#skF_20',k2_zfmisc_1('#skF_19','#skF_20'),k4_tarski('#skF_15','#skF_16')) = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3311])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3330,plain,
    ( r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k2_zfmisc_1('#skF_19','#skF_20')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3315,c_6])).

tff(c_3343,plain,(
    r2_hidden('#skF_16','#skF_20') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3306,c_3330])).

tff(c_3345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2080,c_3343])).

tff(c_3347,plain,(
    r2_hidden('#skF_16','#skF_20') ),
    inference(splitRight,[status(thm)],[c_2078])).

tff(c_3346,plain,
    ( ~ r2_hidden('#skF_17','#skF_21')
    | r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_2078])).

tff(c_3348,plain,(
    ~ r2_hidden('#skF_17','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_3346])).

tff(c_3460,plain,(
    ! [A_632,B_633,D_634] :
      ( k4_tarski('#skF_5'(A_632,B_633,k2_zfmisc_1(A_632,B_633),D_634),'#skF_6'(A_632,B_633,k2_zfmisc_1(A_632,B_633),D_634)) = D_634
      | ~ r2_hidden(D_634,k2_zfmisc_1(A_632,B_633)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3506,plain,(
    ! [A_635,B_636,D_637] :
      ( '#skF_5'(A_635,B_636,k2_zfmisc_1(A_635,B_636),D_637) = k1_mcart_1(D_637)
      | ~ r2_hidden(D_637,k2_zfmisc_1(A_635,B_636)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3460,c_34])).

tff(c_3530,plain,(
    ! [D_48,D_637,C_47,A_45,B_46] :
      ( '#skF_5'(k3_zfmisc_1(A_45,B_46,C_47),D_48,k2_zfmisc_1(k3_zfmisc_1(A_45,B_46,C_47),D_48),D_637) = k1_mcart_1(D_637)
      | ~ r2_hidden(D_637,k4_zfmisc_1(A_45,B_46,C_47,D_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3506])).

tff(c_4274,plain,(
    ! [D_767,C_768,B_765,A_766,D_769] :
      ( '#skF_5'(k3_zfmisc_1(A_766,B_765,C_768),D_767,k4_zfmisc_1(A_766,B_765,C_768,D_767),D_769) = k1_mcart_1(D_769)
      | ~ r2_hidden(D_769,k4_zfmisc_1(A_766,B_765,C_768,D_767)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3530])).

tff(c_4551,plain,(
    ! [D_793,C_797,A_795,D_796,B_794] :
      ( r2_hidden(k1_mcart_1(D_796),k3_zfmisc_1(A_795,B_794,C_797))
      | ~ r2_hidden(D_796,k4_zfmisc_1(A_795,B_794,C_797,D_793))
      | ~ r2_hidden(D_796,k4_zfmisc_1(A_795,B_794,C_797,D_793)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4274,c_247])).

tff(c_4591,plain,
    ( r2_hidden(k1_mcart_1(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18')),k3_zfmisc_1('#skF_19','#skF_20','#skF_21'))
    | ~ r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(resolution,[status(thm)],[c_165,c_4551])).

tff(c_4610,plain,(
    r2_hidden(k3_mcart_1('#skF_15','#skF_16','#skF_17'),k3_zfmisc_1('#skF_19','#skF_20','#skF_21')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_138,c_4591])).

tff(c_87,plain,(
    ! [A_55,B_56,C_57] : k2_mcart_1(k3_mcart_1(A_55,B_56,C_57)) = C_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_36])).

tff(c_3547,plain,(
    ! [A_638,B_639,D_640] :
      ( '#skF_6'(A_638,B_639,k2_zfmisc_1(A_638,B_639),D_640) = k2_mcart_1(D_640)
      | ~ r2_hidden(D_640,k2_zfmisc_1(A_638,B_639)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3460,c_36])).

tff(c_3573,plain,(
    ! [A_38,B_39,C_40,D_640] :
      ( '#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_640) = k2_mcart_1(D_640)
      | ~ r2_hidden(D_640,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3547])).

tff(c_3752,plain,(
    ! [A_679,B_680,C_681,D_682] :
      ( '#skF_6'(k2_zfmisc_1(A_679,B_680),C_681,k3_zfmisc_1(A_679,B_680,C_681),D_682) = k2_mcart_1(D_682)
      | ~ r2_hidden(D_682,k3_zfmisc_1(A_679,B_680,C_681)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3573])).

tff(c_3758,plain,(
    ! [D_682,C_681,A_679,B_680] :
      ( r2_hidden(k2_mcart_1(D_682),C_681)
      | ~ r2_hidden(D_682,k3_zfmisc_1(A_679,B_680,C_681))
      | ~ r2_hidden(D_682,k3_zfmisc_1(A_679,B_680,C_681)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3752,c_258])).

tff(c_4614,plain,
    ( r2_hidden(k2_mcart_1(k3_mcart_1('#skF_15','#skF_16','#skF_17')),'#skF_21')
    | ~ r2_hidden(k3_mcart_1('#skF_15','#skF_16','#skF_17'),k3_zfmisc_1('#skF_19','#skF_20','#skF_21')) ),
    inference(resolution,[status(thm)],[c_4610,c_3758])).

tff(c_4620,plain,(
    r2_hidden('#skF_17','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4610,c_87,c_4614])).

tff(c_4622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3348,c_4620])).

tff(c_4624,plain,(
    r2_hidden('#skF_17','#skF_21') ),
    inference(splitRight,[status(thm)],[c_3346])).

tff(c_2079,plain,(
    r2_hidden('#skF_18','#skF_22') ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_46,plain,
    ( r2_hidden('#skF_7','#skF_11')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4662,plain,(
    r2_hidden('#skF_7','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_3347,c_4624,c_2079,c_46])).

tff(c_4623,plain,(
    r2_hidden('#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_3346])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4626,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden('#skF_17','#skF_21') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_3347,c_2079,c_42])).

tff(c_4627,plain,(
    ~ r2_hidden('#skF_17','#skF_21') ),
    inference(splitLeft,[status(thm)],[c_4626])).

tff(c_4629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4624,c_4627])).

tff(c_4630,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(splitRight,[status(thm)],[c_4626])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k4_tarski(k4_tarski(A_35,B_36),C_37) = k3_mcart_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,(
    ! [E_91,F_92,A_93,B_94] :
      ( r2_hidden(k4_tarski(E_91,F_92),k2_zfmisc_1(A_93,B_94))
      | ~ r2_hidden(F_92,B_94)
      | ~ r2_hidden(E_91,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4666,plain,(
    ! [A_812,B_816,A_814,B_813,C_815] :
      ( r2_hidden(k3_mcart_1(A_812,B_816,C_815),k2_zfmisc_1(A_814,B_813))
      | ~ r2_hidden(C_815,B_813)
      | ~ r2_hidden(k4_tarski(A_812,B_816),A_814) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_225])).

tff(c_4678,plain,(
    ! [A_812,B_39,B_816,A_38,C_815,C_40] :
      ( r2_hidden(k3_mcart_1(A_812,B_816,C_815),k3_zfmisc_1(A_38,B_39,C_40))
      | ~ r2_hidden(C_815,C_40)
      | ~ r2_hidden(k4_tarski(A_812,B_816),k2_zfmisc_1(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4666])).

tff(c_40,plain,
    ( r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4634,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_3347,c_4624,c_2079,c_40])).

tff(c_30,plain,(
    ! [A_41,B_42,C_43,D_44] : k4_tarski(k3_mcart_1(A_41,B_42,C_43),D_44) = k4_mcart_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4954,plain,(
    ! [B_862,D_865,C_864,B_867,A_863,A_866] :
      ( r2_hidden(k4_mcart_1(A_863,B_867,C_864,D_865),k2_zfmisc_1(A_866,B_862))
      | ~ r2_hidden(D_865,B_862)
      | ~ r2_hidden(k3_mcart_1(A_863,B_867,C_864),A_866) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_225])).

tff(c_5940,plain,(
    ! [C_1008,A_1005,C_1007,B_1009,D_1004,B_1002,A_1003,D_1006] :
      ( r2_hidden(k4_mcart_1(A_1003,B_1009,C_1008,D_1004),k4_zfmisc_1(A_1005,B_1002,C_1007,D_1006))
      | ~ r2_hidden(D_1004,D_1006)
      | ~ r2_hidden(k3_mcart_1(A_1003,B_1009,C_1008),k3_zfmisc_1(A_1005,B_1002,C_1007)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4954])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14'))
    | ~ r2_hidden('#skF_18','#skF_22')
    | ~ r2_hidden('#skF_17','#skF_21')
    | ~ r2_hidden('#skF_16','#skF_20')
    | ~ r2_hidden('#skF_15','#skF_19') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4934,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_3347,c_4624,c_2079,c_38])).

tff(c_5947,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_5940,c_4934])).

tff(c_5966,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_5947])).

tff(c_5973,plain,
    ( ~ r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(resolution,[status(thm)],[c_4678,c_5966])).

tff(c_5976,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_5973])).

tff(c_5979,plain,
    ( ~ r2_hidden('#skF_8','#skF_12')
    | ~ r2_hidden('#skF_7','#skF_11') ),
    inference(resolution,[status(thm)],[c_2,c_5976])).

tff(c_5983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_4623,c_5979])).

tff(c_5985,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_56,plain,
    ( r2_hidden('#skF_7','#skF_11')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6058,plain,(
    r2_hidden('#skF_7','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_5985,c_56])).

tff(c_54,plain,
    ( r2_hidden('#skF_8','#skF_12')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6060,plain,(
    r2_hidden('#skF_8','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_5985,c_54])).

tff(c_52,plain,
    ( r2_hidden('#skF_9','#skF_13')
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6061,plain,(
    r2_hidden('#skF_9','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_5985,c_52])).

tff(c_5998,plain,(
    ! [E_1014,F_1015,A_1016,B_1017] :
      ( r2_hidden(k4_tarski(E_1014,F_1015),k2_zfmisc_1(A_1016,B_1017))
      | ~ r2_hidden(F_1015,B_1017)
      | ~ r2_hidden(E_1014,A_1016) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6202,plain,(
    ! [C_1069,B_1068,A_1066,A_1067,B_1070] :
      ( r2_hidden(k3_mcart_1(A_1066,B_1070,C_1069),k2_zfmisc_1(A_1067,B_1068))
      | ~ r2_hidden(C_1069,B_1068)
      | ~ r2_hidden(k4_tarski(A_1066,B_1070),A_1067) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5998])).

tff(c_6214,plain,(
    ! [C_1069,B_39,A_1066,A_38,B_1070,C_40] :
      ( r2_hidden(k3_mcart_1(A_1066,B_1070,C_1069),k3_zfmisc_1(A_38,B_39,C_40))
      | ~ r2_hidden(C_1069,C_40)
      | ~ r2_hidden(k4_tarski(A_1066,B_1070),k2_zfmisc_1(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6202])).

tff(c_5984,plain,(
    r2_hidden('#skF_10','#skF_14') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6489,plain,(
    ! [B_1107,A_1104,D_1106,A_1103,C_1105,B_1108] :
      ( r2_hidden(k4_mcart_1(A_1104,B_1108,C_1105,D_1106),k2_zfmisc_1(A_1103,B_1107))
      | ~ r2_hidden(D_1106,B_1107)
      | ~ r2_hidden(k3_mcart_1(A_1104,B_1108,C_1105),A_1103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5998])).

tff(c_7366,plain,(
    ! [C_1258,A_1253,A_1254,D_1251,C_1257,B_1255,D_1256,B_1252] :
      ( r2_hidden(k4_mcart_1(A_1253,B_1255,C_1258,D_1251),k4_zfmisc_1(A_1254,B_1252,C_1257,D_1256))
      | ~ r2_hidden(D_1251,D_1256)
      | ~ r2_hidden(k3_mcart_1(A_1253,B_1255,C_1258),k3_zfmisc_1(A_1254,B_1252,C_1257)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6489])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14'))
    | r2_hidden(k4_mcart_1('#skF_15','#skF_16','#skF_17','#skF_18'),k4_zfmisc_1('#skF_19','#skF_20','#skF_21','#skF_22')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6201,plain,(
    ~ r2_hidden(k4_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_5985,c_48])).

tff(c_7373,plain,
    ( ~ r2_hidden('#skF_10','#skF_14')
    | ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_7366,c_6201])).

tff(c_7395,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5984,c_7373])).

tff(c_7403,plain,
    ( ~ r2_hidden('#skF_9','#skF_13')
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(resolution,[status(thm)],[c_6214,c_7395])).

tff(c_7406,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6061,c_7403])).

tff(c_7409,plain,
    ( ~ r2_hidden('#skF_8','#skF_12')
    | ~ r2_hidden('#skF_7','#skF_11') ),
    inference(resolution,[status(thm)],[c_2,c_7406])).

tff(c_7413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6058,c_6060,c_7409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/2.80  
% 7.62/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/2.81  %$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_20 > #skF_18 > #skF_17 > #skF_11 > #skF_15 > #skF_19 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_21 > #skF_9 > #skF_8 > #skF_5 > #skF_22 > #skF_3 > #skF_12
% 7.62/2.81  
% 7.62/2.81  %Foreground sorts:
% 7.62/2.81  
% 7.62/2.81  
% 7.62/2.81  %Background operators:
% 7.62/2.81  
% 7.62/2.81  
% 7.62/2.81  %Foreground operators:
% 7.62/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_20', type, '#skF_20': $i).
% 7.62/2.81  tff('#skF_18', type, '#skF_18': $i).
% 7.62/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.81  tff('#skF_17', type, '#skF_17': $i).
% 7.62/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.62/2.81  tff('#skF_11', type, '#skF_11': $i).
% 7.62/2.81  tff('#skF_15', type, '#skF_15': $i).
% 7.62/2.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.62/2.81  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.62/2.81  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_19', type, '#skF_19': $i).
% 7.62/2.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_7', type, '#skF_7': $i).
% 7.62/2.81  tff('#skF_10', type, '#skF_10': $i).
% 7.62/2.81  tff('#skF_16', type, '#skF_16': $i).
% 7.62/2.81  tff('#skF_14', type, '#skF_14': $i).
% 7.62/2.81  tff('#skF_13', type, '#skF_13': $i).
% 7.62/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_21', type, '#skF_21': $i).
% 7.62/2.81  tff('#skF_9', type, '#skF_9': $i).
% 7.62/2.81  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_8', type, '#skF_8': $i).
% 7.62/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.81  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.62/2.81  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.62/2.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.62/2.81  tff('#skF_22', type, '#skF_22': $i).
% 7.62/2.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.62/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.81  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.62/2.81  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.62/2.81  tff('#skF_12', type, '#skF_12': $i).
% 7.62/2.81  
% 7.93/2.84  tff(f_60, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (r2_hidden(k4_mcart_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) <=> (((r2_hidden(A, E) & r2_hidden(B, F)) & r2_hidden(C, G)) & r2_hidden(D, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_mcart_1)).
% 7.93/2.84  tff(f_43, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 7.93/2.84  tff(f_49, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.93/2.84  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 7.93/2.84  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 7.93/2.84  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.93/2.84  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.93/2.84  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_12') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_332, plain, (~r2_hidden('#skF_15', '#skF_19')), inference(splitLeft, [status(thm)], [c_44])).
% 7.93/2.84  tff(c_50, plain, (r2_hidden('#skF_10', '#skF_14') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_165, plain, (r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(splitLeft, [status(thm)], [c_50])).
% 7.93/2.84  tff(c_129, plain, (![A_67, B_68, C_69, D_70]: (k4_tarski(k3_mcart_1(A_67, B_68, C_69), D_70)=k4_mcart_1(A_67, B_68, C_69, D_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.93/2.84  tff(c_34, plain, (![A_49, B_50]: (k1_mcart_1(k4_tarski(A_49, B_50))=A_49)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.93/2.84  tff(c_138, plain, (![A_67, B_68, C_69, D_70]: (k1_mcart_1(k4_mcart_1(A_67, B_68, C_69, D_70))=k3_mcart_1(A_67, B_68, C_69))), inference(superposition, [status(thm), theory('equality')], [c_129, c_34])).
% 7.93/2.84  tff(c_32, plain, (![A_45, B_46, C_47, D_48]: (k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48)=k4_zfmisc_1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.93/2.84  tff(c_440, plain, (![A_152, B_153, D_154]: (k4_tarski('#skF_5'(A_152, B_153, k2_zfmisc_1(A_152, B_153), D_154), '#skF_6'(A_152, B_153, k2_zfmisc_1(A_152, B_153), D_154))=D_154 | ~r2_hidden(D_154, k2_zfmisc_1(A_152, B_153)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_486, plain, (![A_155, B_156, D_157]: ('#skF_5'(A_155, B_156, k2_zfmisc_1(A_155, B_156), D_157)=k1_mcart_1(D_157) | ~r2_hidden(D_157, k2_zfmisc_1(A_155, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_34])).
% 7.93/2.84  tff(c_510, plain, (![D_48, D_157, C_47, A_45, B_46]: ('#skF_5'(k3_zfmisc_1(A_45, B_46, C_47), D_48, k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48), D_157)=k1_mcart_1(D_157) | ~r2_hidden(D_157, k4_zfmisc_1(A_45, B_46, C_47, D_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_486])).
% 7.93/2.84  tff(c_1192, plain, (![D_274, C_278, B_275, A_276, D_277]: ('#skF_5'(k3_zfmisc_1(A_276, B_275, C_278), D_277, k4_zfmisc_1(A_276, B_275, C_278, D_277), D_274)=k1_mcart_1(D_274) | ~r2_hidden(D_274, k4_zfmisc_1(A_276, B_275, C_278, D_277)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_510])).
% 7.93/2.84  tff(c_240, plain, (![A_95, B_96, D_97]: (r2_hidden('#skF_5'(A_95, B_96, k2_zfmisc_1(A_95, B_96), D_97), A_95) | ~r2_hidden(D_97, k2_zfmisc_1(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_243, plain, (![D_48, C_47, A_45, B_46, D_97]: (r2_hidden('#skF_5'(k3_zfmisc_1(A_45, B_46, C_47), D_48, k4_zfmisc_1(A_45, B_46, C_47, D_48), D_97), k3_zfmisc_1(A_45, B_46, C_47)) | ~r2_hidden(D_97, k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_240])).
% 7.93/2.84  tff(c_247, plain, (![D_48, C_47, A_45, B_46, D_97]: (r2_hidden('#skF_5'(k3_zfmisc_1(A_45, B_46, C_47), D_48, k4_zfmisc_1(A_45, B_46, C_47, D_48), D_97), k3_zfmisc_1(A_45, B_46, C_47)) | ~r2_hidden(D_97, k4_zfmisc_1(A_45, B_46, C_47, D_48)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_243])).
% 7.93/2.84  tff(c_1386, plain, (![D_303, B_302, D_299, C_300, A_301]: (r2_hidden(k1_mcart_1(D_303), k3_zfmisc_1(A_301, B_302, C_300)) | ~r2_hidden(D_303, k4_zfmisc_1(A_301, B_302, C_300, D_299)) | ~r2_hidden(D_303, k4_zfmisc_1(A_301, B_302, C_300, D_299)))), inference(superposition, [status(thm), theory('equality')], [c_1192, c_247])).
% 7.93/2.84  tff(c_1426, plain, (r2_hidden(k1_mcart_1(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18')), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21')) | ~r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(resolution, [status(thm)], [c_165, c_1386])).
% 7.93/2.84  tff(c_1445, plain, (r2_hidden(k3_mcart_1('#skF_15', '#skF_16', '#skF_17'), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_138, c_1426])).
% 7.93/2.84  tff(c_75, plain, (![A_55, B_56, C_57]: (k4_tarski(k4_tarski(A_55, B_56), C_57)=k3_mcart_1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.93/2.84  tff(c_84, plain, (![A_55, B_56, C_57]: (k1_mcart_1(k3_mcart_1(A_55, B_56, C_57))=k4_tarski(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_75, c_34])).
% 7.93/2.84  tff(c_28, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)=k3_zfmisc_1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.93/2.84  tff(c_512, plain, (![A_38, B_39, C_40, D_157]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_157)=k1_mcart_1(D_157) | ~r2_hidden(D_157, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_486])).
% 7.93/2.84  tff(c_526, plain, (![A_38, B_39, C_40, D_157]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_157)=k1_mcart_1(D_157) | ~r2_hidden(D_157, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_512])).
% 7.93/2.84  tff(c_246, plain, (![A_38, B_39, C_40, D_97]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_97), k2_zfmisc_1(A_38, B_39)) | ~r2_hidden(D_97, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_240])).
% 7.93/2.84  tff(c_991, plain, (![A_242, B_243, C_244, D_245]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_242, B_243), C_244, k3_zfmisc_1(A_242, B_243, C_244), D_245), k2_zfmisc_1(A_242, B_243)) | ~r2_hidden(D_245, k3_zfmisc_1(A_242, B_243, C_244)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_246])).
% 7.93/2.84  tff(c_998, plain, (![D_157, A_38, B_39, C_40]: (r2_hidden(k1_mcart_1(D_157), k2_zfmisc_1(A_38, B_39)) | ~r2_hidden(D_157, k3_zfmisc_1(A_38, B_39, C_40)) | ~r2_hidden(D_157, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_526, c_991])).
% 7.93/2.84  tff(c_1447, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_15', '#skF_16', '#skF_17')), k2_zfmisc_1('#skF_19', '#skF_20')) | ~r2_hidden(k3_mcart_1('#skF_15', '#skF_16', '#skF_17'), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21'))), inference(resolution, [status(thm)], [c_1445, c_998])).
% 7.93/2.84  tff(c_1452, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k2_zfmisc_1('#skF_19', '#skF_20'))), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_84, c_1447])).
% 7.93/2.84  tff(c_461, plain, (![A_152, B_153, D_154]: ('#skF_5'(A_152, B_153, k2_zfmisc_1(A_152, B_153), D_154)=k1_mcart_1(D_154) | ~r2_hidden(D_154, k2_zfmisc_1(A_152, B_153)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_34])).
% 7.93/2.84  tff(c_1459, plain, ('#skF_5'('#skF_19', '#skF_20', k2_zfmisc_1('#skF_19', '#skF_20'), k4_tarski('#skF_15', '#skF_16'))=k1_mcart_1(k4_tarski('#skF_15', '#skF_16'))), inference(resolution, [status(thm)], [c_1452, c_461])).
% 7.93/2.84  tff(c_1463, plain, ('#skF_5'('#skF_19', '#skF_20', k2_zfmisc_1('#skF_19', '#skF_20'), k4_tarski('#skF_15', '#skF_16'))='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1459])).
% 7.93/2.84  tff(c_8, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_1) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_1501, plain, (r2_hidden('#skF_15', '#skF_19') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k2_zfmisc_1('#skF_19', '#skF_20'))), inference(superposition, [status(thm), theory('equality')], [c_1463, c_8])).
% 7.93/2.84  tff(c_1514, plain, (r2_hidden('#skF_15', '#skF_19')), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_1501])).
% 7.93/2.84  tff(c_1516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_1514])).
% 7.93/2.84  tff(c_1518, plain, (r2_hidden('#skF_15', '#skF_19')), inference(splitRight, [status(thm)], [c_44])).
% 7.93/2.84  tff(c_1517, plain, (~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_18', '#skF_22') | r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_44])).
% 7.93/2.84  tff(c_1519, plain, (~r2_hidden('#skF_18', '#skF_22')), inference(splitLeft, [status(thm)], [c_1517])).
% 7.93/2.84  tff(c_36, plain, (![A_49, B_50]: (k2_mcart_1(k4_tarski(A_49, B_50))=B_50)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.93/2.84  tff(c_141, plain, (![A_67, B_68, C_69, D_70]: (k2_mcart_1(k4_mcart_1(A_67, B_68, C_69, D_70))=D_70)), inference(superposition, [status(thm), theory('equality')], [c_129, c_36])).
% 7.93/2.84  tff(c_114, plain, (![A_64, B_65, C_66]: (k2_zfmisc_1(k2_zfmisc_1(A_64, B_65), C_66)=k3_zfmisc_1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.93/2.84  tff(c_123, plain, (![A_38, B_39, C_40, C_66]: (k3_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40, C_66)=k2_zfmisc_1(k3_zfmisc_1(A_38, B_39, C_40), C_66))), inference(superposition, [status(thm), theory('equality')], [c_28, c_114])).
% 7.93/2.84  tff(c_178, plain, (![A_38, B_39, C_40, C_66]: (k3_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40, C_66)=k4_zfmisc_1(A_38, B_39, C_40, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_123])).
% 7.93/2.84  tff(c_1631, plain, (![A_340, B_341, D_342]: (k4_tarski('#skF_5'(A_340, B_341, k2_zfmisc_1(A_340, B_341), D_342), '#skF_6'(A_340, B_341, k2_zfmisc_1(A_340, B_341), D_342))=D_342 | ~r2_hidden(D_342, k2_zfmisc_1(A_340, B_341)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_1718, plain, (![A_346, B_347, D_348]: ('#skF_6'(A_346, B_347, k2_zfmisc_1(A_346, B_347), D_348)=k2_mcart_1(D_348) | ~r2_hidden(D_348, k2_zfmisc_1(A_346, B_347)))), inference(superposition, [status(thm), theory('equality')], [c_1631, c_36])).
% 7.93/2.84  tff(c_1744, plain, (![A_38, B_39, C_40, D_348]: ('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_348)=k2_mcart_1(D_348) | ~r2_hidden(D_348, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1718])).
% 7.93/2.84  tff(c_1963, plain, (![A_385, B_386, C_387, D_388]: ('#skF_6'(k2_zfmisc_1(A_385, B_386), C_387, k3_zfmisc_1(A_385, B_386, C_387), D_388)=k2_mcart_1(D_388) | ~r2_hidden(D_388, k3_zfmisc_1(A_385, B_386, C_387)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1744])).
% 7.93/2.84  tff(c_250, plain, (![A_98, B_99, D_100]: (r2_hidden('#skF_6'(A_98, B_99, k2_zfmisc_1(A_98, B_99), D_100), B_99) | ~r2_hidden(D_100, k2_zfmisc_1(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_256, plain, (![A_38, B_39, C_40, D_100]: (r2_hidden('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_100), C_40) | ~r2_hidden(D_100, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_250])).
% 7.93/2.84  tff(c_258, plain, (![A_38, B_39, C_40, D_100]: (r2_hidden('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_100), C_40) | ~r2_hidden(D_100, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_256])).
% 7.93/2.84  tff(c_1991, plain, (![D_389, C_390, A_391, B_392]: (r2_hidden(k2_mcart_1(D_389), C_390) | ~r2_hidden(D_389, k3_zfmisc_1(A_391, B_392, C_390)) | ~r2_hidden(D_389, k3_zfmisc_1(A_391, B_392, C_390)))), inference(superposition, [status(thm), theory('equality')], [c_1963, c_258])).
% 7.93/2.84  tff(c_2018, plain, (![B_39, A_38, C_66, C_40, D_389]: (r2_hidden(k2_mcart_1(D_389), C_66) | ~r2_hidden(D_389, k4_zfmisc_1(A_38, B_39, C_40, C_66)) | ~r2_hidden(D_389, k3_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_1991])).
% 7.93/2.84  tff(c_2032, plain, (![C_396, D_397, B_395, C_394, A_393]: (r2_hidden(k2_mcart_1(D_397), C_394) | ~r2_hidden(D_397, k4_zfmisc_1(A_393, B_395, C_396, C_394)) | ~r2_hidden(D_397, k4_zfmisc_1(A_393, B_395, C_396, C_394)))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_2018])).
% 7.93/2.84  tff(c_2061, plain, (r2_hidden(k2_mcart_1(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18')), '#skF_22') | ~r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(resolution, [status(thm)], [c_165, c_2032])).
% 7.93/2.84  tff(c_2075, plain, (r2_hidden('#skF_18', '#skF_22')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_141, c_2061])).
% 7.93/2.84  tff(c_2077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1519, c_2075])).
% 7.93/2.84  tff(c_2078, plain, (~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_1517])).
% 7.93/2.84  tff(c_2080, plain, (~r2_hidden('#skF_16', '#skF_20')), inference(splitLeft, [status(thm)], [c_2078])).
% 7.93/2.84  tff(c_2193, plain, (![A_434, B_435, D_436]: (k4_tarski('#skF_5'(A_434, B_435, k2_zfmisc_1(A_434, B_435), D_436), '#skF_6'(A_434, B_435, k2_zfmisc_1(A_434, B_435), D_436))=D_436 | ~r2_hidden(D_436, k2_zfmisc_1(A_434, B_435)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_2239, plain, (![A_437, B_438, D_439]: ('#skF_5'(A_437, B_438, k2_zfmisc_1(A_437, B_438), D_439)=k1_mcart_1(D_439) | ~r2_hidden(D_439, k2_zfmisc_1(A_437, B_438)))), inference(superposition, [status(thm), theory('equality')], [c_2193, c_34])).
% 7.93/2.84  tff(c_2263, plain, (![D_439, D_48, C_47, A_45, B_46]: ('#skF_5'(k3_zfmisc_1(A_45, B_46, C_47), D_48, k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48), D_439)=k1_mcart_1(D_439) | ~r2_hidden(D_439, k4_zfmisc_1(A_45, B_46, C_47, D_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2239])).
% 7.93/2.84  tff(c_2278, plain, (![D_439, D_48, C_47, A_45, B_46]: ('#skF_5'(k3_zfmisc_1(A_45, B_46, C_47), D_48, k4_zfmisc_1(A_45, B_46, C_47, D_48), D_439)=k1_mcart_1(D_439) | ~r2_hidden(D_439, k4_zfmisc_1(A_45, B_46, C_47, D_48)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2263])).
% 7.93/2.84  tff(c_3108, plain, (![B_576, D_578, C_579, A_577, D_580]: (r2_hidden('#skF_5'(k3_zfmisc_1(A_577, B_576, C_579), D_578, k4_zfmisc_1(A_577, B_576, C_579, D_578), D_580), k3_zfmisc_1(A_577, B_576, C_579)) | ~r2_hidden(D_580, k4_zfmisc_1(A_577, B_576, C_579, D_578)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_243])).
% 7.93/2.84  tff(c_3240, plain, (![D_594, C_595, D_592, B_591, A_593]: (r2_hidden(k1_mcart_1(D_592), k3_zfmisc_1(A_593, B_591, C_595)) | ~r2_hidden(D_592, k4_zfmisc_1(A_593, B_591, C_595, D_594)) | ~r2_hidden(D_592, k4_zfmisc_1(A_593, B_591, C_595, D_594)))), inference(superposition, [status(thm), theory('equality')], [c_2278, c_3108])).
% 7.93/2.84  tff(c_3280, plain, (r2_hidden(k1_mcart_1(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18')), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21')) | ~r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(resolution, [status(thm)], [c_165, c_3240])).
% 7.93/2.84  tff(c_3299, plain, (r2_hidden(k3_mcart_1('#skF_15', '#skF_16', '#skF_17'), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_138, c_3280])).
% 7.93/2.84  tff(c_2265, plain, (![A_38, B_39, C_40, D_439]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_439)=k1_mcart_1(D_439) | ~r2_hidden(D_439, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2239])).
% 7.93/2.84  tff(c_2279, plain, (![A_38, B_39, C_40, D_439]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_439)=k1_mcart_1(D_439) | ~r2_hidden(D_439, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2265])).
% 7.93/2.84  tff(c_2747, plain, (![A_524, B_525, C_526, D_527]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_524, B_525), C_526, k3_zfmisc_1(A_524, B_525, C_526), D_527), k2_zfmisc_1(A_524, B_525)) | ~r2_hidden(D_527, k3_zfmisc_1(A_524, B_525, C_526)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_246])).
% 7.93/2.84  tff(c_2754, plain, (![D_439, A_38, B_39, C_40]: (r2_hidden(k1_mcart_1(D_439), k2_zfmisc_1(A_38, B_39)) | ~r2_hidden(D_439, k3_zfmisc_1(A_38, B_39, C_40)) | ~r2_hidden(D_439, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_2279, c_2747])).
% 7.93/2.84  tff(c_3301, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_15', '#skF_16', '#skF_17')), k2_zfmisc_1('#skF_19', '#skF_20')) | ~r2_hidden(k3_mcart_1('#skF_15', '#skF_16', '#skF_17'), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21'))), inference(resolution, [status(thm)], [c_3299, c_2754])).
% 7.93/2.84  tff(c_3306, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k2_zfmisc_1('#skF_19', '#skF_20'))), inference(demodulation, [status(thm), theory('equality')], [c_3299, c_84, c_3301])).
% 7.93/2.84  tff(c_2217, plain, (![A_434, B_435, D_436]: ('#skF_6'(A_434, B_435, k2_zfmisc_1(A_434, B_435), D_436)=k2_mcart_1(D_436) | ~r2_hidden(D_436, k2_zfmisc_1(A_434, B_435)))), inference(superposition, [status(thm), theory('equality')], [c_2193, c_36])).
% 7.93/2.84  tff(c_3311, plain, ('#skF_6'('#skF_19', '#skF_20', k2_zfmisc_1('#skF_19', '#skF_20'), k4_tarski('#skF_15', '#skF_16'))=k2_mcart_1(k4_tarski('#skF_15', '#skF_16'))), inference(resolution, [status(thm)], [c_3306, c_2217])).
% 7.93/2.84  tff(c_3315, plain, ('#skF_6'('#skF_19', '#skF_20', k2_zfmisc_1('#skF_19', '#skF_20'), k4_tarski('#skF_15', '#skF_16'))='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3311])).
% 7.93/2.84  tff(c_6, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_2) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_3330, plain, (r2_hidden('#skF_16', '#skF_20') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k2_zfmisc_1('#skF_19', '#skF_20'))), inference(superposition, [status(thm), theory('equality')], [c_3315, c_6])).
% 7.93/2.84  tff(c_3343, plain, (r2_hidden('#skF_16', '#skF_20')), inference(demodulation, [status(thm), theory('equality')], [c_3306, c_3330])).
% 7.93/2.84  tff(c_3345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2080, c_3343])).
% 7.93/2.84  tff(c_3347, plain, (r2_hidden('#skF_16', '#skF_20')), inference(splitRight, [status(thm)], [c_2078])).
% 7.93/2.84  tff(c_3346, plain, (~r2_hidden('#skF_17', '#skF_21') | r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_2078])).
% 7.93/2.84  tff(c_3348, plain, (~r2_hidden('#skF_17', '#skF_21')), inference(splitLeft, [status(thm)], [c_3346])).
% 7.93/2.84  tff(c_3460, plain, (![A_632, B_633, D_634]: (k4_tarski('#skF_5'(A_632, B_633, k2_zfmisc_1(A_632, B_633), D_634), '#skF_6'(A_632, B_633, k2_zfmisc_1(A_632, B_633), D_634))=D_634 | ~r2_hidden(D_634, k2_zfmisc_1(A_632, B_633)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_3506, plain, (![A_635, B_636, D_637]: ('#skF_5'(A_635, B_636, k2_zfmisc_1(A_635, B_636), D_637)=k1_mcart_1(D_637) | ~r2_hidden(D_637, k2_zfmisc_1(A_635, B_636)))), inference(superposition, [status(thm), theory('equality')], [c_3460, c_34])).
% 7.93/2.84  tff(c_3530, plain, (![D_48, D_637, C_47, A_45, B_46]: ('#skF_5'(k3_zfmisc_1(A_45, B_46, C_47), D_48, k2_zfmisc_1(k3_zfmisc_1(A_45, B_46, C_47), D_48), D_637)=k1_mcart_1(D_637) | ~r2_hidden(D_637, k4_zfmisc_1(A_45, B_46, C_47, D_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3506])).
% 7.93/2.84  tff(c_4274, plain, (![D_767, C_768, B_765, A_766, D_769]: ('#skF_5'(k3_zfmisc_1(A_766, B_765, C_768), D_767, k4_zfmisc_1(A_766, B_765, C_768, D_767), D_769)=k1_mcart_1(D_769) | ~r2_hidden(D_769, k4_zfmisc_1(A_766, B_765, C_768, D_767)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3530])).
% 7.93/2.84  tff(c_4551, plain, (![D_793, C_797, A_795, D_796, B_794]: (r2_hidden(k1_mcart_1(D_796), k3_zfmisc_1(A_795, B_794, C_797)) | ~r2_hidden(D_796, k4_zfmisc_1(A_795, B_794, C_797, D_793)) | ~r2_hidden(D_796, k4_zfmisc_1(A_795, B_794, C_797, D_793)))), inference(superposition, [status(thm), theory('equality')], [c_4274, c_247])).
% 7.93/2.84  tff(c_4591, plain, (r2_hidden(k1_mcart_1(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18')), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21')) | ~r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(resolution, [status(thm)], [c_165, c_4551])).
% 7.93/2.84  tff(c_4610, plain, (r2_hidden(k3_mcart_1('#skF_15', '#skF_16', '#skF_17'), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_138, c_4591])).
% 7.93/2.84  tff(c_87, plain, (![A_55, B_56, C_57]: (k2_mcart_1(k3_mcart_1(A_55, B_56, C_57))=C_57)), inference(superposition, [status(thm), theory('equality')], [c_75, c_36])).
% 7.93/2.84  tff(c_3547, plain, (![A_638, B_639, D_640]: ('#skF_6'(A_638, B_639, k2_zfmisc_1(A_638, B_639), D_640)=k2_mcart_1(D_640) | ~r2_hidden(D_640, k2_zfmisc_1(A_638, B_639)))), inference(superposition, [status(thm), theory('equality')], [c_3460, c_36])).
% 7.93/2.84  tff(c_3573, plain, (![A_38, B_39, C_40, D_640]: ('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_640)=k2_mcart_1(D_640) | ~r2_hidden(D_640, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3547])).
% 7.93/2.84  tff(c_3752, plain, (![A_679, B_680, C_681, D_682]: ('#skF_6'(k2_zfmisc_1(A_679, B_680), C_681, k3_zfmisc_1(A_679, B_680, C_681), D_682)=k2_mcart_1(D_682) | ~r2_hidden(D_682, k3_zfmisc_1(A_679, B_680, C_681)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3573])).
% 7.93/2.84  tff(c_3758, plain, (![D_682, C_681, A_679, B_680]: (r2_hidden(k2_mcart_1(D_682), C_681) | ~r2_hidden(D_682, k3_zfmisc_1(A_679, B_680, C_681)) | ~r2_hidden(D_682, k3_zfmisc_1(A_679, B_680, C_681)))), inference(superposition, [status(thm), theory('equality')], [c_3752, c_258])).
% 7.93/2.84  tff(c_4614, plain, (r2_hidden(k2_mcart_1(k3_mcart_1('#skF_15', '#skF_16', '#skF_17')), '#skF_21') | ~r2_hidden(k3_mcart_1('#skF_15', '#skF_16', '#skF_17'), k3_zfmisc_1('#skF_19', '#skF_20', '#skF_21'))), inference(resolution, [status(thm)], [c_4610, c_3758])).
% 7.93/2.84  tff(c_4620, plain, (r2_hidden('#skF_17', '#skF_21')), inference(demodulation, [status(thm), theory('equality')], [c_4610, c_87, c_4614])).
% 7.93/2.84  tff(c_4622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3348, c_4620])).
% 7.93/2.84  tff(c_4624, plain, (r2_hidden('#skF_17', '#skF_21')), inference(splitRight, [status(thm)], [c_3346])).
% 7.93/2.84  tff(c_2079, plain, (r2_hidden('#skF_18', '#skF_22')), inference(splitRight, [status(thm)], [c_1517])).
% 7.93/2.84  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_11') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_4662, plain, (r2_hidden('#skF_7', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_3347, c_4624, c_2079, c_46])).
% 7.93/2.84  tff(c_4623, plain, (r2_hidden('#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_3346])).
% 7.93/2.84  tff(c_2, plain, (![E_33, F_34, A_1, B_2]: (r2_hidden(k4_tarski(E_33, F_34), k2_zfmisc_1(A_1, B_2)) | ~r2_hidden(F_34, B_2) | ~r2_hidden(E_33, A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_4626, plain, (r2_hidden('#skF_9', '#skF_13') | ~r2_hidden('#skF_17', '#skF_21')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_3347, c_2079, c_42])).
% 7.93/2.84  tff(c_4627, plain, (~r2_hidden('#skF_17', '#skF_21')), inference(splitLeft, [status(thm)], [c_4626])).
% 7.93/2.84  tff(c_4629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4624, c_4627])).
% 7.93/2.84  tff(c_4630, plain, (r2_hidden('#skF_9', '#skF_13')), inference(splitRight, [status(thm)], [c_4626])).
% 7.93/2.84  tff(c_26, plain, (![A_35, B_36, C_37]: (k4_tarski(k4_tarski(A_35, B_36), C_37)=k3_mcart_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.93/2.84  tff(c_225, plain, (![E_91, F_92, A_93, B_94]: (r2_hidden(k4_tarski(E_91, F_92), k2_zfmisc_1(A_93, B_94)) | ~r2_hidden(F_92, B_94) | ~r2_hidden(E_91, A_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_4666, plain, (![A_812, B_816, A_814, B_813, C_815]: (r2_hidden(k3_mcart_1(A_812, B_816, C_815), k2_zfmisc_1(A_814, B_813)) | ~r2_hidden(C_815, B_813) | ~r2_hidden(k4_tarski(A_812, B_816), A_814))), inference(superposition, [status(thm), theory('equality')], [c_26, c_225])).
% 7.93/2.84  tff(c_4678, plain, (![A_812, B_39, B_816, A_38, C_815, C_40]: (r2_hidden(k3_mcart_1(A_812, B_816, C_815), k3_zfmisc_1(A_38, B_39, C_40)) | ~r2_hidden(C_815, C_40) | ~r2_hidden(k4_tarski(A_812, B_816), k2_zfmisc_1(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4666])).
% 7.93/2.84  tff(c_40, plain, (r2_hidden('#skF_10', '#skF_14') | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_4634, plain, (r2_hidden('#skF_10', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_3347, c_4624, c_2079, c_40])).
% 7.93/2.84  tff(c_30, plain, (![A_41, B_42, C_43, D_44]: (k4_tarski(k3_mcart_1(A_41, B_42, C_43), D_44)=k4_mcart_1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.93/2.84  tff(c_4954, plain, (![B_862, D_865, C_864, B_867, A_863, A_866]: (r2_hidden(k4_mcart_1(A_863, B_867, C_864, D_865), k2_zfmisc_1(A_866, B_862)) | ~r2_hidden(D_865, B_862) | ~r2_hidden(k3_mcart_1(A_863, B_867, C_864), A_866))), inference(superposition, [status(thm), theory('equality')], [c_30, c_225])).
% 7.93/2.84  tff(c_5940, plain, (![C_1008, A_1005, C_1007, B_1009, D_1004, B_1002, A_1003, D_1006]: (r2_hidden(k4_mcart_1(A_1003, B_1009, C_1008, D_1004), k4_zfmisc_1(A_1005, B_1002, C_1007, D_1006)) | ~r2_hidden(D_1004, D_1006) | ~r2_hidden(k3_mcart_1(A_1003, B_1009, C_1008), k3_zfmisc_1(A_1005, B_1002, C_1007)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4954])).
% 7.93/2.84  tff(c_38, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14')) | ~r2_hidden('#skF_18', '#skF_22') | ~r2_hidden('#skF_17', '#skF_21') | ~r2_hidden('#skF_16', '#skF_20') | ~r2_hidden('#skF_15', '#skF_19')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_4934, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_3347, c_4624, c_2079, c_38])).
% 7.93/2.84  tff(c_5947, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_5940, c_4934])).
% 7.93/2.84  tff(c_5966, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_4634, c_5947])).
% 7.93/2.84  tff(c_5973, plain, (~r2_hidden('#skF_9', '#skF_13') | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(resolution, [status(thm)], [c_4678, c_5966])).
% 7.93/2.84  tff(c_5976, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_5973])).
% 7.93/2.84  tff(c_5979, plain, (~r2_hidden('#skF_8', '#skF_12') | ~r2_hidden('#skF_7', '#skF_11')), inference(resolution, [status(thm)], [c_2, c_5976])).
% 7.93/2.84  tff(c_5983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4662, c_4623, c_5979])).
% 7.93/2.84  tff(c_5985, plain, (~r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(splitRight, [status(thm)], [c_50])).
% 7.93/2.84  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_11') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_6058, plain, (r2_hidden('#skF_7', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_5985, c_56])).
% 7.93/2.84  tff(c_54, plain, (r2_hidden('#skF_8', '#skF_12') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_6060, plain, (r2_hidden('#skF_8', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_5985, c_54])).
% 7.93/2.84  tff(c_52, plain, (r2_hidden('#skF_9', '#skF_13') | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_6061, plain, (r2_hidden('#skF_9', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_5985, c_52])).
% 7.93/2.84  tff(c_5998, plain, (![E_1014, F_1015, A_1016, B_1017]: (r2_hidden(k4_tarski(E_1014, F_1015), k2_zfmisc_1(A_1016, B_1017)) | ~r2_hidden(F_1015, B_1017) | ~r2_hidden(E_1014, A_1016))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.93/2.84  tff(c_6202, plain, (![C_1069, B_1068, A_1066, A_1067, B_1070]: (r2_hidden(k3_mcart_1(A_1066, B_1070, C_1069), k2_zfmisc_1(A_1067, B_1068)) | ~r2_hidden(C_1069, B_1068) | ~r2_hidden(k4_tarski(A_1066, B_1070), A_1067))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5998])).
% 7.93/2.84  tff(c_6214, plain, (![C_1069, B_39, A_1066, A_38, B_1070, C_40]: (r2_hidden(k3_mcart_1(A_1066, B_1070, C_1069), k3_zfmisc_1(A_38, B_39, C_40)) | ~r2_hidden(C_1069, C_40) | ~r2_hidden(k4_tarski(A_1066, B_1070), k2_zfmisc_1(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6202])).
% 7.93/2.84  tff(c_5984, plain, (r2_hidden('#skF_10', '#skF_14')), inference(splitRight, [status(thm)], [c_50])).
% 7.93/2.84  tff(c_6489, plain, (![B_1107, A_1104, D_1106, A_1103, C_1105, B_1108]: (r2_hidden(k4_mcart_1(A_1104, B_1108, C_1105, D_1106), k2_zfmisc_1(A_1103, B_1107)) | ~r2_hidden(D_1106, B_1107) | ~r2_hidden(k3_mcart_1(A_1104, B_1108, C_1105), A_1103))), inference(superposition, [status(thm), theory('equality')], [c_30, c_5998])).
% 7.93/2.84  tff(c_7366, plain, (![C_1258, A_1253, A_1254, D_1251, C_1257, B_1255, D_1256, B_1252]: (r2_hidden(k4_mcart_1(A_1253, B_1255, C_1258, D_1251), k4_zfmisc_1(A_1254, B_1252, C_1257, D_1256)) | ~r2_hidden(D_1251, D_1256) | ~r2_hidden(k3_mcart_1(A_1253, B_1255, C_1258), k3_zfmisc_1(A_1254, B_1252, C_1257)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6489])).
% 7.93/2.84  tff(c_48, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14')) | r2_hidden(k4_mcart_1('#skF_15', '#skF_16', '#skF_17', '#skF_18'), k4_zfmisc_1('#skF_19', '#skF_20', '#skF_21', '#skF_22'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.93/2.84  tff(c_6201, plain, (~r2_hidden(k4_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k4_zfmisc_1('#skF_11', '#skF_12', '#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_5985, c_48])).
% 7.93/2.84  tff(c_7373, plain, (~r2_hidden('#skF_10', '#skF_14') | ~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_7366, c_6201])).
% 7.93/2.84  tff(c_7395, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_11', '#skF_12', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_5984, c_7373])).
% 7.93/2.84  tff(c_7403, plain, (~r2_hidden('#skF_9', '#skF_13') | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(resolution, [status(thm)], [c_6214, c_7395])).
% 7.93/2.84  tff(c_7406, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_6061, c_7403])).
% 7.93/2.84  tff(c_7409, plain, (~r2_hidden('#skF_8', '#skF_12') | ~r2_hidden('#skF_7', '#skF_11')), inference(resolution, [status(thm)], [c_2, c_7406])).
% 7.93/2.84  tff(c_7413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6058, c_6060, c_7409])).
% 7.93/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.84  
% 7.93/2.84  Inference rules
% 7.93/2.84  ----------------------
% 7.93/2.84  #Ref     : 0
% 7.93/2.84  #Sup     : 1874
% 7.93/2.84  #Fact    : 0
% 7.93/2.84  #Define  : 0
% 7.93/2.84  #Split   : 6
% 7.93/2.84  #Chain   : 0
% 7.93/2.84  #Close   : 0
% 7.93/2.84  
% 7.93/2.84  Ordering : KBO
% 7.93/2.84  
% 7.93/2.84  Simplification rules
% 7.93/2.84  ----------------------
% 7.93/2.84  #Subsume      : 379
% 7.93/2.84  #Demod        : 1535
% 7.93/2.84  #Tautology    : 516
% 7.93/2.84  #SimpNegUnit  : 8
% 7.93/2.84  #BackRed      : 0
% 7.93/2.84  
% 7.93/2.84  #Partial instantiations: 0
% 7.93/2.84  #Strategies tried      : 1
% 7.93/2.84  
% 7.93/2.84  Timing (in seconds)
% 7.93/2.84  ----------------------
% 7.93/2.85  Preprocessing        : 0.34
% 7.93/2.85  Parsing              : 0.17
% 7.93/2.85  CNF conversion       : 0.03
% 7.93/2.85  Main loop            : 1.67
% 7.93/2.85  Inferencing          : 0.66
% 7.93/2.85  Reduction            : 0.55
% 7.93/2.85  Demodulation         : 0.41
% 7.93/2.85  BG Simplification    : 0.10
% 7.93/2.85  Subsumption          : 0.24
% 7.93/2.85  Abstraction          : 0.14
% 7.93/2.85  MUC search           : 0.00
% 7.93/2.85  Cooper               : 0.00
% 7.93/2.85  Total                : 2.07
% 7.93/2.85  Index Insertion      : 0.00
% 7.93/2.85  Index Deletion       : 0.00
% 7.93/2.85  Index Matching       : 0.00
% 7.93/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
