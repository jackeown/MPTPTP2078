%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:08 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 411 expanded)
%              Number of leaves         :   33 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 834 expanded)
%              Number of equality atoms :   31 ( 185 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_18 > #skF_17 > #skF_11 > #skF_15 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
      <=> ( r2_hidden(A,D)
          & r2_hidden(B,E)
          & r2_hidden(C,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

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

tff(c_40,plain,
    ( r2_hidden('#skF_7','#skF_10')
    | ~ r2_hidden('#skF_15','#skF_18')
    | ~ r2_hidden('#skF_14','#skF_17')
    | ~ r2_hidden('#skF_13','#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_13','#skF_16') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r2_hidden('#skF_9','#skF_12')
    | r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_82,plain,(
    ! [A_50,B_51,C_52] : k4_tarski(k4_tarski(A_50,B_51),C_52) = k3_mcart_1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_41,B_42] : k1_mcart_1(k4_tarski(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [A_50,B_51,C_52] : k1_mcart_1(k3_mcart_1(A_50,B_51,C_52)) = k4_tarski(A_50,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_30])).

tff(c_28,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40) = k3_zfmisc_1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    ! [A_100,B_101,D_102] :
      ( k4_tarski('#skF_5'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102),'#skF_6'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102)) = D_102
      | ~ r2_hidden(D_102,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_242,plain,(
    ! [A_103,B_104,D_105] :
      ( '#skF_5'(A_103,B_104,k2_zfmisc_1(A_103,B_104),D_105) = k1_mcart_1(D_105)
      | ~ r2_hidden(D_105,k2_zfmisc_1(A_103,B_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_30])).

tff(c_269,plain,(
    ! [A_38,B_39,C_40,D_105] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_105) = k1_mcart_1(D_105)
      | ~ r2_hidden(D_105,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_242])).

tff(c_283,plain,(
    ! [A_38,B_39,C_40,D_105] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_105) = k1_mcart_1(D_105)
      | ~ r2_hidden(D_105,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_269])).

tff(c_168,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_hidden('#skF_5'(A_71,B_72,k2_zfmisc_1(A_71,B_72),D_73),A_71)
      | ~ r2_hidden(D_73,k2_zfmisc_1(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [A_38,B_39,C_40,D_73] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_73),k2_zfmisc_1(A_38,B_39))
      | ~ r2_hidden(D_73,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_168])).

tff(c_493,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_150,B_151),C_152,k3_zfmisc_1(A_150,B_151,C_152),D_153),k2_zfmisc_1(A_150,B_151))
      | ~ r2_hidden(D_153,k3_zfmisc_1(A_150,B_151,C_152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_171])).

tff(c_550,plain,(
    ! [D_157,A_158,B_159,C_160] :
      ( r2_hidden(k1_mcart_1(D_157),k2_zfmisc_1(A_158,B_159))
      | ~ r2_hidden(D_157,k3_zfmisc_1(A_158,B_159,C_160))
      | ~ r2_hidden(D_157,k3_zfmisc_1(A_158,B_159,C_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_493])).

tff(c_579,plain,
    ( r2_hidden(k1_mcart_1(k3_mcart_1('#skF_13','#skF_14','#skF_15')),k2_zfmisc_1('#skF_16','#skF_17'))
    | ~ r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(resolution,[status(thm)],[c_122,c_550])).

tff(c_594,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_14'),k2_zfmisc_1('#skF_16','#skF_17')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_91,c_579])).

tff(c_225,plain,(
    ! [A_100,B_101,D_102] :
      ( '#skF_5'(A_100,B_101,k2_zfmisc_1(A_100,B_101),D_102) = k1_mcart_1(D_102)
      | ~ r2_hidden(D_102,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_30])).

tff(c_598,plain,(
    '#skF_5'('#skF_16','#skF_17',k2_zfmisc_1('#skF_16','#skF_17'),k4_tarski('#skF_13','#skF_14')) = k1_mcart_1(k4_tarski('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_594,c_225])).

tff(c_602,plain,(
    '#skF_5'('#skF_16','#skF_17',k2_zfmisc_1('#skF_16','#skF_17'),k4_tarski('#skF_13','#skF_14')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_598])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_632,plain,
    ( r2_hidden('#skF_13','#skF_16')
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k2_zfmisc_1('#skF_16','#skF_17')) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_8])).

tff(c_641,plain,(
    r2_hidden('#skF_13','#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_632])).

tff(c_643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_641])).

tff(c_645,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( r2_hidden('#skF_7','#skF_10')
    | r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_648,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_48])).

tff(c_46,plain,
    ( r2_hidden('#skF_8','#skF_11')
    | r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_646,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_46])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_644,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k4_tarski(k4_tarski(A_35,B_36),C_37) = k3_mcart_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_649,plain,(
    ! [E_161,F_162,A_163,B_164] :
      ( r2_hidden(k4_tarski(E_161,F_162),k2_zfmisc_1(A_163,B_164))
      | ~ r2_hidden(F_162,B_164)
      | ~ r2_hidden(E_161,A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_705,plain,(
    ! [F_192,B_189,E_190,A_188,C_191] :
      ( r2_hidden(k4_tarski(E_190,F_192),k3_zfmisc_1(A_188,B_189,C_191))
      | ~ r2_hidden(F_192,C_191)
      | ~ r2_hidden(E_190,k2_zfmisc_1(A_188,B_189)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_649])).

tff(c_977,plain,(
    ! [C_244,A_241,B_243,A_245,C_242,B_246] :
      ( r2_hidden(k3_mcart_1(A_241,B_246,C_244),k3_zfmisc_1(A_245,B_243,C_242))
      | ~ r2_hidden(C_244,C_242)
      | ~ r2_hidden(k4_tarski(A_241,B_246),k2_zfmisc_1(A_245,B_243)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_705])).

tff(c_42,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12'))
    | r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_721,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_42])).

tff(c_982,plain,
    ( ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_977,c_721])).

tff(c_996,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_982])).

tff(c_1002,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(resolution,[status(thm)],[c_2,c_996])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_646,c_1002])).

tff(c_1007,plain,
    ( ~ r2_hidden('#skF_14','#skF_17')
    | ~ r2_hidden('#skF_15','#skF_18')
    | r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1018,plain,(
    ~ r2_hidden('#skF_15','#skF_18') ),
    inference(splitLeft,[status(thm)],[c_1007])).

tff(c_1021,plain,(
    r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_32,plain,(
    ! [A_41,B_42] : k2_mcart_1(k4_tarski(A_41,B_42)) = B_42 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_50,B_51,C_52] : k2_mcart_1(k3_mcart_1(A_50,B_51,C_52)) = C_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_32])).

tff(c_1119,plain,(
    ! [A_297,B_298,D_299] :
      ( k4_tarski('#skF_5'(A_297,B_298,k2_zfmisc_1(A_297,B_298),D_299),'#skF_6'(A_297,B_298,k2_zfmisc_1(A_297,B_298),D_299)) = D_299
      | ~ r2_hidden(D_299,k2_zfmisc_1(A_297,B_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1196,plain,(
    ! [A_303,B_304,D_305] :
      ( '#skF_6'(A_303,B_304,k2_zfmisc_1(A_303,B_304),D_305) = k2_mcart_1(D_305)
      | ~ r2_hidden(D_305,k2_zfmisc_1(A_303,B_304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_32])).

tff(c_1223,plain,(
    ! [A_38,B_39,C_40,D_305] :
      ( '#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_305) = k2_mcart_1(D_305)
      | ~ r2_hidden(D_305,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1196])).

tff(c_1336,plain,(
    ! [A_321,B_322,C_323,D_324] :
      ( '#skF_6'(k2_zfmisc_1(A_321,B_322),C_323,k3_zfmisc_1(A_321,B_322,C_323),D_324) = k2_mcart_1(D_324)
      | ~ r2_hidden(D_324,k3_zfmisc_1(A_321,B_322,C_323)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1223])).

tff(c_1074,plain,(
    ! [A_265,B_266,D_267] :
      ( r2_hidden('#skF_6'(A_265,B_266,k2_zfmisc_1(A_265,B_266),D_267),B_266)
      | ~ r2_hidden(D_267,k2_zfmisc_1(A_265,B_266)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1077,plain,(
    ! [A_38,B_39,C_40,D_267] :
      ( r2_hidden('#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_267),C_40)
      | ~ r2_hidden(D_267,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1074])).

tff(c_1078,plain,(
    ! [A_38,B_39,C_40,D_267] :
      ( r2_hidden('#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_267),C_40)
      | ~ r2_hidden(D_267,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1077])).

tff(c_1356,plain,(
    ! [D_325,C_326,A_327,B_328] :
      ( r2_hidden(k2_mcart_1(D_325),C_326)
      | ~ r2_hidden(D_325,k3_zfmisc_1(A_327,B_328,C_326))
      | ~ r2_hidden(D_325,k3_zfmisc_1(A_327,B_328,C_326)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_1078])).

tff(c_1385,plain,
    ( r2_hidden(k2_mcart_1(k3_mcart_1('#skF_13','#skF_14','#skF_15')),'#skF_18')
    | ~ r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(resolution,[status(thm)],[c_1021,c_1356])).

tff(c_1400,plain,(
    r2_hidden('#skF_15','#skF_18') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_94,c_1385])).

tff(c_1402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1018,c_1400])).

tff(c_1404,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1411,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_1404,c_48])).

tff(c_1405,plain,(
    r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1404,c_1405])).

tff(c_1407,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1403,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1450,plain,(
    ! [E_337,F_338,A_339,B_340] :
      ( r2_hidden(k4_tarski(E_337,F_338),k2_zfmisc_1(A_339,B_340))
      | ~ r2_hidden(F_338,B_340)
      | ~ r2_hidden(E_337,A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1470,plain,(
    ! [B_357,A_356,B_360,A_359,C_358] :
      ( r2_hidden(k3_mcart_1(A_356,B_360,C_358),k2_zfmisc_1(A_359,B_357))
      | ~ r2_hidden(C_358,B_357)
      | ~ r2_hidden(k4_tarski(A_356,B_360),A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1450])).

tff(c_1496,plain,(
    ! [C_375,B_372,A_370,B_371,A_373,C_374] :
      ( r2_hidden(k3_mcart_1(A_373,B_371,C_374),k3_zfmisc_1(A_370,B_372,C_375))
      | ~ r2_hidden(C_374,C_375)
      | ~ r2_hidden(k4_tarski(A_373,B_371),k2_zfmisc_1(A_370,B_372)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1470])).

tff(c_1478,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_1404,c_42])).

tff(c_1499,plain,
    ( ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_1496,c_1478])).

tff(c_1511,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1499])).

tff(c_1517,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(resolution,[status(thm)],[c_2,c_1511])).

tff(c_1521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1411,c_1407,c_1517])).

tff(c_1522,plain,
    ( ~ r2_hidden('#skF_14','#skF_17')
    | r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1007])).

tff(c_1524,plain,(
    ~ r2_hidden('#skF_14','#skF_17') ),
    inference(splitLeft,[status(thm)],[c_1522])).

tff(c_1527,plain,(
    r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1617,plain,(
    ! [A_417,B_418,D_419] :
      ( k4_tarski('#skF_5'(A_417,B_418,k2_zfmisc_1(A_417,B_418),D_419),'#skF_6'(A_417,B_418,k2_zfmisc_1(A_417,B_418),D_419)) = D_419
      | ~ r2_hidden(D_419,k2_zfmisc_1(A_417,B_418)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1652,plain,(
    ! [A_420,B_421,D_422] :
      ( '#skF_5'(A_420,B_421,k2_zfmisc_1(A_420,B_421),D_422) = k1_mcart_1(D_422)
      | ~ r2_hidden(D_422,k2_zfmisc_1(A_420,B_421)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_30])).

tff(c_1679,plain,(
    ! [A_38,B_39,C_40,D_422] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40),D_422) = k1_mcart_1(D_422)
      | ~ r2_hidden(D_422,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1652])).

tff(c_1693,plain,(
    ! [A_38,B_39,C_40,D_422] :
      ( '#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_422) = k1_mcart_1(D_422)
      | ~ r2_hidden(D_422,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1679])).

tff(c_1578,plain,(
    ! [A_388,B_389,D_390] :
      ( r2_hidden('#skF_5'(A_388,B_389,k2_zfmisc_1(A_388,B_389),D_390),A_388)
      | ~ r2_hidden(D_390,k2_zfmisc_1(A_388,B_389)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1581,plain,(
    ! [A_38,B_39,C_40,D_390] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_390),k2_zfmisc_1(A_38,B_39))
      | ~ r2_hidden(D_390,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1578])).

tff(c_1903,plain,(
    ! [A_467,B_468,C_469,D_470] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_467,B_468),C_469,k3_zfmisc_1(A_467,B_468,C_469),D_470),k2_zfmisc_1(A_467,B_468))
      | ~ r2_hidden(D_470,k3_zfmisc_1(A_467,B_468,C_469)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1581])).

tff(c_1925,plain,(
    ! [D_471,A_472,B_473,C_474] :
      ( r2_hidden(k1_mcart_1(D_471),k2_zfmisc_1(A_472,B_473))
      | ~ r2_hidden(D_471,k3_zfmisc_1(A_472,B_473,C_474))
      | ~ r2_hidden(D_471,k3_zfmisc_1(A_472,B_473,C_474)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1693,c_1903])).

tff(c_1954,plain,
    ( r2_hidden(k1_mcart_1(k3_mcart_1('#skF_13','#skF_14','#skF_15')),k2_zfmisc_1('#skF_16','#skF_17'))
    | ~ r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(resolution,[status(thm)],[c_1527,c_1925])).

tff(c_1969,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_14'),k2_zfmisc_1('#skF_16','#skF_17')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_91,c_1954])).

tff(c_1638,plain,(
    ! [A_417,B_418,D_419] :
      ( '#skF_6'(A_417,B_418,k2_zfmisc_1(A_417,B_418),D_419) = k2_mcart_1(D_419)
      | ~ r2_hidden(D_419,k2_zfmisc_1(A_417,B_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_32])).

tff(c_2006,plain,(
    '#skF_6'('#skF_16','#skF_17',k2_zfmisc_1('#skF_16','#skF_17'),k4_tarski('#skF_13','#skF_14')) = k2_mcart_1(k4_tarski('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_1969,c_1638])).

tff(c_2010,plain,(
    '#skF_6'('#skF_16','#skF_17',k2_zfmisc_1('#skF_16','#skF_17'),k4_tarski('#skF_13','#skF_14')) = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2006])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2022,plain,
    ( r2_hidden('#skF_14','#skF_17')
    | ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k2_zfmisc_1('#skF_16','#skF_17')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2010,c_6])).

tff(c_2033,plain,(
    r2_hidden('#skF_14','#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_2022])).

tff(c_2035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1524,c_2033])).

tff(c_2036,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2037,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2038,plain,(
    r2_hidden(k3_mcart_1('#skF_13','#skF_14','#skF_15'),k3_zfmisc_1('#skF_16','#skF_17','#skF_18')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2037,c_2038])).

tff(c_2040,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2042,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_2037,c_44])).

tff(c_2083,plain,(
    ! [E_486,F_487,A_488,B_489] :
      ( r2_hidden(k4_tarski(E_486,F_487),k2_zfmisc_1(A_488,B_489))
      | ~ r2_hidden(F_487,B_489)
      | ~ r2_hidden(E_486,A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2103,plain,(
    ! [A_506,A_505,B_507,C_508,B_509] :
      ( r2_hidden(k3_mcart_1(A_505,B_509,C_508),k2_zfmisc_1(A_506,B_507))
      | ~ r2_hidden(C_508,B_507)
      | ~ r2_hidden(k4_tarski(A_505,B_509),A_506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2083])).

tff(c_2129,plain,(
    ! [C_524,B_521,A_523,C_522,A_519,B_520] :
      ( r2_hidden(k3_mcart_1(A_523,B_521,C_522),k3_zfmisc_1(A_519,B_520,C_524))
      | ~ r2_hidden(C_522,C_524)
      | ~ r2_hidden(k4_tarski(A_523,B_521),k2_zfmisc_1(A_519,B_520)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2103])).

tff(c_2111,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_2037,c_42])).

tff(c_2132,plain,
    ( ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_2129,c_2111])).

tff(c_2144,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2042,c_2132])).

tff(c_2152,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(resolution,[status(thm)],[c_2,c_2144])).

tff(c_2156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_2040,c_2152])).

tff(c_2157,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1522])).

tff(c_1008,plain,(
    r2_hidden('#skF_13','#skF_16') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2158,plain,(
    r2_hidden('#skF_14','#skF_17') ),
    inference(splitRight,[status(thm)],[c_1522])).

tff(c_1523,plain,(
    r2_hidden('#skF_15','#skF_18') ),
    inference(splitRight,[status(thm)],[c_1007])).

tff(c_38,plain,
    ( r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_15','#skF_18')
    | ~ r2_hidden('#skF_14','#skF_17')
    | ~ r2_hidden('#skF_13','#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2162,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2158,c_1523,c_38])).

tff(c_36,plain,
    ( r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden('#skF_15','#skF_18')
    | ~ r2_hidden('#skF_14','#skF_17')
    | ~ r2_hidden('#skF_13','#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2160,plain,(
    r2_hidden('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2158,c_1523,c_36])).

tff(c_2202,plain,(
    ! [E_533,F_534,A_535,B_536] :
      ( r2_hidden(k4_tarski(E_533,F_534),k2_zfmisc_1(A_535,B_536))
      | ~ r2_hidden(F_534,B_536)
      | ~ r2_hidden(E_533,A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2232,plain,(
    ! [B_558,F_561,C_559,E_560,A_557] :
      ( r2_hidden(k4_tarski(E_560,F_561),k3_zfmisc_1(A_557,B_558,C_559))
      | ~ r2_hidden(F_561,C_559)
      | ~ r2_hidden(E_560,k2_zfmisc_1(A_557,B_558)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2202])).

tff(c_2549,plain,(
    ! [C_612,A_611,B_613,C_609,A_610,B_614] :
      ( r2_hidden(k3_mcart_1(A_610,B_613,C_612),k3_zfmisc_1(A_611,B_614,C_609))
      | ~ r2_hidden(C_612,C_609)
      | ~ r2_hidden(k4_tarski(A_610,B_613),k2_zfmisc_1(A_611,B_614)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2232])).

tff(c_34,plain,
    ( ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12'))
    | ~ r2_hidden('#skF_15','#skF_18')
    | ~ r2_hidden('#skF_14','#skF_17')
    | ~ r2_hidden('#skF_13','#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2221,plain,(
    ~ r2_hidden(k3_mcart_1('#skF_7','#skF_8','#skF_9'),k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_2158,c_1523,c_34])).

tff(c_2554,plain,
    ( ~ r2_hidden('#skF_9','#skF_12')
    | ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_2549,c_2221])).

tff(c_2565,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_2554])).

tff(c_2570,plain,
    ( ~ r2_hidden('#skF_8','#skF_11')
    | ~ r2_hidden('#skF_7','#skF_10') ),
    inference(resolution,[status(thm)],[c_2,c_2565])).

tff(c_2574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2157,c_2162,c_2570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.84  
% 4.44/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.84  %$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_18 > #skF_17 > #skF_11 > #skF_15 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_12
% 4.44/1.84  
% 4.44/1.84  %Foreground sorts:
% 4.44/1.84  
% 4.44/1.84  
% 4.44/1.84  %Background operators:
% 4.44/1.84  
% 4.44/1.84  
% 4.44/1.84  %Foreground operators:
% 4.44/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.44/1.84  tff('#skF_18', type, '#skF_18': $i).
% 4.44/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.84  tff('#skF_17', type, '#skF_17': $i).
% 4.44/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.44/1.84  tff('#skF_11', type, '#skF_11': $i).
% 4.44/1.84  tff('#skF_15', type, '#skF_15': $i).
% 4.44/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.44/1.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.44/1.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.44/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.44/1.84  tff('#skF_10', type, '#skF_10': $i).
% 4.44/1.84  tff('#skF_16', type, '#skF_16': $i).
% 4.44/1.84  tff('#skF_14', type, '#skF_14': $i).
% 4.44/1.84  tff('#skF_13', type, '#skF_13': $i).
% 4.44/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.44/1.84  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.44/1.84  tff('#skF_9', type, '#skF_9': $i).
% 4.44/1.84  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.44/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.44/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.44/1.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.44/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.44/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.44/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.44/1.84  tff('#skF_12', type, '#skF_12': $i).
% 4.44/1.84  
% 4.44/1.87  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F]: (r2_hidden(k3_mcart_1(A, B, C), k3_zfmisc_1(D, E, F)) <=> ((r2_hidden(A, D) & r2_hidden(B, E)) & r2_hidden(C, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_mcart_1)).
% 4.44/1.87  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.44/1.87  tff(f_45, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.44/1.87  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.44/1.87  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.44/1.87  tff(c_40, plain, (r2_hidden('#skF_7', '#skF_10') | ~r2_hidden('#skF_15', '#skF_18') | ~r2_hidden('#skF_14', '#skF_17') | ~r2_hidden('#skF_13', '#skF_16')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_112, plain, (~r2_hidden('#skF_13', '#skF_16')), inference(splitLeft, [status(thm)], [c_40])).
% 4.44/1.87  tff(c_44, plain, (r2_hidden('#skF_9', '#skF_12') | r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_122, plain, (r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.44/1.87  tff(c_82, plain, (![A_50, B_51, C_52]: (k4_tarski(k4_tarski(A_50, B_51), C_52)=k3_mcart_1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.87  tff(c_30, plain, (![A_41, B_42]: (k1_mcart_1(k4_tarski(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.44/1.87  tff(c_91, plain, (![A_50, B_51, C_52]: (k1_mcart_1(k3_mcart_1(A_50, B_51, C_52))=k4_tarski(A_50, B_51))), inference(superposition, [status(thm), theory('equality')], [c_82, c_30])).
% 4.44/1.87  tff(c_28, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)=k3_zfmisc_1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.44/1.87  tff(c_207, plain, (![A_100, B_101, D_102]: (k4_tarski('#skF_5'(A_100, B_101, k2_zfmisc_1(A_100, B_101), D_102), '#skF_6'(A_100, B_101, k2_zfmisc_1(A_100, B_101), D_102))=D_102 | ~r2_hidden(D_102, k2_zfmisc_1(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_242, plain, (![A_103, B_104, D_105]: ('#skF_5'(A_103, B_104, k2_zfmisc_1(A_103, B_104), D_105)=k1_mcart_1(D_105) | ~r2_hidden(D_105, k2_zfmisc_1(A_103, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_30])).
% 4.44/1.87  tff(c_269, plain, (![A_38, B_39, C_40, D_105]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_105)=k1_mcart_1(D_105) | ~r2_hidden(D_105, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_242])).
% 4.44/1.87  tff(c_283, plain, (![A_38, B_39, C_40, D_105]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_105)=k1_mcart_1(D_105) | ~r2_hidden(D_105, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_269])).
% 4.44/1.87  tff(c_168, plain, (![A_71, B_72, D_73]: (r2_hidden('#skF_5'(A_71, B_72, k2_zfmisc_1(A_71, B_72), D_73), A_71) | ~r2_hidden(D_73, k2_zfmisc_1(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_171, plain, (![A_38, B_39, C_40, D_73]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_73), k2_zfmisc_1(A_38, B_39)) | ~r2_hidden(D_73, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_168])).
% 4.44/1.87  tff(c_493, plain, (![A_150, B_151, C_152, D_153]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_150, B_151), C_152, k3_zfmisc_1(A_150, B_151, C_152), D_153), k2_zfmisc_1(A_150, B_151)) | ~r2_hidden(D_153, k3_zfmisc_1(A_150, B_151, C_152)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_171])).
% 4.44/1.87  tff(c_550, plain, (![D_157, A_158, B_159, C_160]: (r2_hidden(k1_mcart_1(D_157), k2_zfmisc_1(A_158, B_159)) | ~r2_hidden(D_157, k3_zfmisc_1(A_158, B_159, C_160)) | ~r2_hidden(D_157, k3_zfmisc_1(A_158, B_159, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_493])).
% 4.44/1.87  tff(c_579, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_13', '#skF_14', '#skF_15')), k2_zfmisc_1('#skF_16', '#skF_17')) | ~r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(resolution, [status(thm)], [c_122, c_550])).
% 4.44/1.87  tff(c_594, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_14'), k2_zfmisc_1('#skF_16', '#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_91, c_579])).
% 4.44/1.87  tff(c_225, plain, (![A_100, B_101, D_102]: ('#skF_5'(A_100, B_101, k2_zfmisc_1(A_100, B_101), D_102)=k1_mcart_1(D_102) | ~r2_hidden(D_102, k2_zfmisc_1(A_100, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_30])).
% 4.44/1.87  tff(c_598, plain, ('#skF_5'('#skF_16', '#skF_17', k2_zfmisc_1('#skF_16', '#skF_17'), k4_tarski('#skF_13', '#skF_14'))=k1_mcart_1(k4_tarski('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_594, c_225])).
% 4.44/1.87  tff(c_602, plain, ('#skF_5'('#skF_16', '#skF_17', k2_zfmisc_1('#skF_16', '#skF_17'), k4_tarski('#skF_13', '#skF_14'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_598])).
% 4.44/1.87  tff(c_8, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_1) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_632, plain, (r2_hidden('#skF_13', '#skF_16') | ~r2_hidden(k4_tarski('#skF_13', '#skF_14'), k2_zfmisc_1('#skF_16', '#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_602, c_8])).
% 4.44/1.87  tff(c_641, plain, (r2_hidden('#skF_13', '#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_632])).
% 4.44/1.87  tff(c_643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_641])).
% 4.44/1.87  tff(c_645, plain, (~r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitRight, [status(thm)], [c_44])).
% 4.44/1.87  tff(c_48, plain, (r2_hidden('#skF_7', '#skF_10') | r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_648, plain, (r2_hidden('#skF_7', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_645, c_48])).
% 4.44/1.87  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_11') | r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_646, plain, (r2_hidden('#skF_8', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_645, c_46])).
% 4.44/1.87  tff(c_2, plain, (![E_33, F_34, A_1, B_2]: (r2_hidden(k4_tarski(E_33, F_34), k2_zfmisc_1(A_1, B_2)) | ~r2_hidden(F_34, B_2) | ~r2_hidden(E_33, A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_644, plain, (r2_hidden('#skF_9', '#skF_12')), inference(splitRight, [status(thm)], [c_44])).
% 4.44/1.87  tff(c_26, plain, (![A_35, B_36, C_37]: (k4_tarski(k4_tarski(A_35, B_36), C_37)=k3_mcart_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.87  tff(c_649, plain, (![E_161, F_162, A_163, B_164]: (r2_hidden(k4_tarski(E_161, F_162), k2_zfmisc_1(A_163, B_164)) | ~r2_hidden(F_162, B_164) | ~r2_hidden(E_161, A_163))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_705, plain, (![F_192, B_189, E_190, A_188, C_191]: (r2_hidden(k4_tarski(E_190, F_192), k3_zfmisc_1(A_188, B_189, C_191)) | ~r2_hidden(F_192, C_191) | ~r2_hidden(E_190, k2_zfmisc_1(A_188, B_189)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_649])).
% 4.44/1.87  tff(c_977, plain, (![C_244, A_241, B_243, A_245, C_242, B_246]: (r2_hidden(k3_mcart_1(A_241, B_246, C_244), k3_zfmisc_1(A_245, B_243, C_242)) | ~r2_hidden(C_244, C_242) | ~r2_hidden(k4_tarski(A_241, B_246), k2_zfmisc_1(A_245, B_243)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_705])).
% 4.44/1.87  tff(c_42, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12')) | r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_721, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_645, c_42])).
% 4.44/1.87  tff(c_982, plain, (~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_977, c_721])).
% 4.44/1.87  tff(c_996, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_644, c_982])).
% 4.44/1.87  tff(c_1002, plain, (~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(resolution, [status(thm)], [c_2, c_996])).
% 4.44/1.87  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_648, c_646, c_1002])).
% 4.44/1.87  tff(c_1007, plain, (~r2_hidden('#skF_14', '#skF_17') | ~r2_hidden('#skF_15', '#skF_18') | r2_hidden('#skF_7', '#skF_10')), inference(splitRight, [status(thm)], [c_40])).
% 4.44/1.87  tff(c_1018, plain, (~r2_hidden('#skF_15', '#skF_18')), inference(splitLeft, [status(thm)], [c_1007])).
% 4.44/1.87  tff(c_1021, plain, (r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.44/1.87  tff(c_32, plain, (![A_41, B_42]: (k2_mcart_1(k4_tarski(A_41, B_42))=B_42)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.44/1.87  tff(c_94, plain, (![A_50, B_51, C_52]: (k2_mcart_1(k3_mcart_1(A_50, B_51, C_52))=C_52)), inference(superposition, [status(thm), theory('equality')], [c_82, c_32])).
% 4.44/1.87  tff(c_1119, plain, (![A_297, B_298, D_299]: (k4_tarski('#skF_5'(A_297, B_298, k2_zfmisc_1(A_297, B_298), D_299), '#skF_6'(A_297, B_298, k2_zfmisc_1(A_297, B_298), D_299))=D_299 | ~r2_hidden(D_299, k2_zfmisc_1(A_297, B_298)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_1196, plain, (![A_303, B_304, D_305]: ('#skF_6'(A_303, B_304, k2_zfmisc_1(A_303, B_304), D_305)=k2_mcart_1(D_305) | ~r2_hidden(D_305, k2_zfmisc_1(A_303, B_304)))), inference(superposition, [status(thm), theory('equality')], [c_1119, c_32])).
% 4.44/1.87  tff(c_1223, plain, (![A_38, B_39, C_40, D_305]: ('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_305)=k2_mcart_1(D_305) | ~r2_hidden(D_305, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1196])).
% 4.44/1.87  tff(c_1336, plain, (![A_321, B_322, C_323, D_324]: ('#skF_6'(k2_zfmisc_1(A_321, B_322), C_323, k3_zfmisc_1(A_321, B_322, C_323), D_324)=k2_mcart_1(D_324) | ~r2_hidden(D_324, k3_zfmisc_1(A_321, B_322, C_323)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1223])).
% 4.44/1.87  tff(c_1074, plain, (![A_265, B_266, D_267]: (r2_hidden('#skF_6'(A_265, B_266, k2_zfmisc_1(A_265, B_266), D_267), B_266) | ~r2_hidden(D_267, k2_zfmisc_1(A_265, B_266)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_1077, plain, (![A_38, B_39, C_40, D_267]: (r2_hidden('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_267), C_40) | ~r2_hidden(D_267, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1074])).
% 4.44/1.87  tff(c_1078, plain, (![A_38, B_39, C_40, D_267]: (r2_hidden('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_267), C_40) | ~r2_hidden(D_267, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1077])).
% 4.44/1.87  tff(c_1356, plain, (![D_325, C_326, A_327, B_328]: (r2_hidden(k2_mcart_1(D_325), C_326) | ~r2_hidden(D_325, k3_zfmisc_1(A_327, B_328, C_326)) | ~r2_hidden(D_325, k3_zfmisc_1(A_327, B_328, C_326)))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_1078])).
% 4.44/1.87  tff(c_1385, plain, (r2_hidden(k2_mcart_1(k3_mcart_1('#skF_13', '#skF_14', '#skF_15')), '#skF_18') | ~r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(resolution, [status(thm)], [c_1021, c_1356])).
% 4.44/1.87  tff(c_1400, plain, (r2_hidden('#skF_15', '#skF_18')), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_94, c_1385])).
% 4.44/1.87  tff(c_1402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1018, c_1400])).
% 4.44/1.87  tff(c_1404, plain, (~r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitRight, [status(thm)], [c_44])).
% 4.44/1.87  tff(c_1411, plain, (r2_hidden('#skF_7', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_1404, c_48])).
% 4.44/1.87  tff(c_1405, plain, (r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.44/1.87  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1404, c_1405])).
% 4.44/1.87  tff(c_1407, plain, (r2_hidden('#skF_8', '#skF_11')), inference(splitRight, [status(thm)], [c_46])).
% 4.44/1.87  tff(c_1403, plain, (r2_hidden('#skF_9', '#skF_12')), inference(splitRight, [status(thm)], [c_44])).
% 4.44/1.87  tff(c_1450, plain, (![E_337, F_338, A_339, B_340]: (r2_hidden(k4_tarski(E_337, F_338), k2_zfmisc_1(A_339, B_340)) | ~r2_hidden(F_338, B_340) | ~r2_hidden(E_337, A_339))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_1470, plain, (![B_357, A_356, B_360, A_359, C_358]: (r2_hidden(k3_mcart_1(A_356, B_360, C_358), k2_zfmisc_1(A_359, B_357)) | ~r2_hidden(C_358, B_357) | ~r2_hidden(k4_tarski(A_356, B_360), A_359))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1450])).
% 4.44/1.87  tff(c_1496, plain, (![C_375, B_372, A_370, B_371, A_373, C_374]: (r2_hidden(k3_mcart_1(A_373, B_371, C_374), k3_zfmisc_1(A_370, B_372, C_375)) | ~r2_hidden(C_374, C_375) | ~r2_hidden(k4_tarski(A_373, B_371), k2_zfmisc_1(A_370, B_372)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1470])).
% 4.44/1.87  tff(c_1478, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1404, c_42])).
% 4.44/1.87  tff(c_1499, plain, (~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_1496, c_1478])).
% 4.44/1.87  tff(c_1511, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1499])).
% 4.44/1.87  tff(c_1517, plain, (~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(resolution, [status(thm)], [c_2, c_1511])).
% 4.44/1.87  tff(c_1521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1411, c_1407, c_1517])).
% 4.44/1.87  tff(c_1522, plain, (~r2_hidden('#skF_14', '#skF_17') | r2_hidden('#skF_7', '#skF_10')), inference(splitRight, [status(thm)], [c_1007])).
% 4.44/1.87  tff(c_1524, plain, (~r2_hidden('#skF_14', '#skF_17')), inference(splitLeft, [status(thm)], [c_1522])).
% 4.44/1.87  tff(c_1527, plain, (r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.44/1.87  tff(c_1617, plain, (![A_417, B_418, D_419]: (k4_tarski('#skF_5'(A_417, B_418, k2_zfmisc_1(A_417, B_418), D_419), '#skF_6'(A_417, B_418, k2_zfmisc_1(A_417, B_418), D_419))=D_419 | ~r2_hidden(D_419, k2_zfmisc_1(A_417, B_418)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_1652, plain, (![A_420, B_421, D_422]: ('#skF_5'(A_420, B_421, k2_zfmisc_1(A_420, B_421), D_422)=k1_mcart_1(D_422) | ~r2_hidden(D_422, k2_zfmisc_1(A_420, B_421)))), inference(superposition, [status(thm), theory('equality')], [c_1617, c_30])).
% 4.44/1.87  tff(c_1679, plain, (![A_38, B_39, C_40, D_422]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40), D_422)=k1_mcart_1(D_422) | ~r2_hidden(D_422, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1652])).
% 4.44/1.87  tff(c_1693, plain, (![A_38, B_39, C_40, D_422]: ('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_422)=k1_mcart_1(D_422) | ~r2_hidden(D_422, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1679])).
% 4.44/1.87  tff(c_1578, plain, (![A_388, B_389, D_390]: (r2_hidden('#skF_5'(A_388, B_389, k2_zfmisc_1(A_388, B_389), D_390), A_388) | ~r2_hidden(D_390, k2_zfmisc_1(A_388, B_389)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_1581, plain, (![A_38, B_39, C_40, D_390]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_390), k2_zfmisc_1(A_38, B_39)) | ~r2_hidden(D_390, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1578])).
% 4.44/1.87  tff(c_1903, plain, (![A_467, B_468, C_469, D_470]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_467, B_468), C_469, k3_zfmisc_1(A_467, B_468, C_469), D_470), k2_zfmisc_1(A_467, B_468)) | ~r2_hidden(D_470, k3_zfmisc_1(A_467, B_468, C_469)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1581])).
% 4.44/1.87  tff(c_1925, plain, (![D_471, A_472, B_473, C_474]: (r2_hidden(k1_mcart_1(D_471), k2_zfmisc_1(A_472, B_473)) | ~r2_hidden(D_471, k3_zfmisc_1(A_472, B_473, C_474)) | ~r2_hidden(D_471, k3_zfmisc_1(A_472, B_473, C_474)))), inference(superposition, [status(thm), theory('equality')], [c_1693, c_1903])).
% 4.44/1.87  tff(c_1954, plain, (r2_hidden(k1_mcart_1(k3_mcart_1('#skF_13', '#skF_14', '#skF_15')), k2_zfmisc_1('#skF_16', '#skF_17')) | ~r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(resolution, [status(thm)], [c_1527, c_1925])).
% 4.44/1.87  tff(c_1969, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_14'), k2_zfmisc_1('#skF_16', '#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_91, c_1954])).
% 4.44/1.87  tff(c_1638, plain, (![A_417, B_418, D_419]: ('#skF_6'(A_417, B_418, k2_zfmisc_1(A_417, B_418), D_419)=k2_mcart_1(D_419) | ~r2_hidden(D_419, k2_zfmisc_1(A_417, B_418)))), inference(superposition, [status(thm), theory('equality')], [c_1617, c_32])).
% 4.44/1.87  tff(c_2006, plain, ('#skF_6'('#skF_16', '#skF_17', k2_zfmisc_1('#skF_16', '#skF_17'), k4_tarski('#skF_13', '#skF_14'))=k2_mcart_1(k4_tarski('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_1969, c_1638])).
% 4.44/1.87  tff(c_2010, plain, ('#skF_6'('#skF_16', '#skF_17', k2_zfmisc_1('#skF_16', '#skF_17'), k4_tarski('#skF_13', '#skF_14'))='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2006])).
% 4.44/1.87  tff(c_6, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_2) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_2022, plain, (r2_hidden('#skF_14', '#skF_17') | ~r2_hidden(k4_tarski('#skF_13', '#skF_14'), k2_zfmisc_1('#skF_16', '#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_2010, c_6])).
% 4.44/1.87  tff(c_2033, plain, (r2_hidden('#skF_14', '#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_2022])).
% 4.44/1.87  tff(c_2035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1524, c_2033])).
% 4.44/1.87  tff(c_2036, plain, (r2_hidden('#skF_7', '#skF_10')), inference(splitRight, [status(thm)], [c_48])).
% 4.44/1.87  tff(c_2037, plain, (~r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitRight, [status(thm)], [c_48])).
% 4.44/1.87  tff(c_2038, plain, (r2_hidden(k3_mcart_1('#skF_13', '#skF_14', '#skF_15'), k3_zfmisc_1('#skF_16', '#skF_17', '#skF_18'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.44/1.87  tff(c_2039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2037, c_2038])).
% 4.44/1.87  tff(c_2040, plain, (r2_hidden('#skF_8', '#skF_11')), inference(splitRight, [status(thm)], [c_46])).
% 4.44/1.87  tff(c_2042, plain, (r2_hidden('#skF_9', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_2037, c_44])).
% 4.44/1.87  tff(c_2083, plain, (![E_486, F_487, A_488, B_489]: (r2_hidden(k4_tarski(E_486, F_487), k2_zfmisc_1(A_488, B_489)) | ~r2_hidden(F_487, B_489) | ~r2_hidden(E_486, A_488))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_2103, plain, (![A_506, A_505, B_507, C_508, B_509]: (r2_hidden(k3_mcart_1(A_505, B_509, C_508), k2_zfmisc_1(A_506, B_507)) | ~r2_hidden(C_508, B_507) | ~r2_hidden(k4_tarski(A_505, B_509), A_506))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2083])).
% 4.44/1.87  tff(c_2129, plain, (![C_524, B_521, A_523, C_522, A_519, B_520]: (r2_hidden(k3_mcart_1(A_523, B_521, C_522), k3_zfmisc_1(A_519, B_520, C_524)) | ~r2_hidden(C_522, C_524) | ~r2_hidden(k4_tarski(A_523, B_521), k2_zfmisc_1(A_519, B_520)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2103])).
% 4.44/1.87  tff(c_2111, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_2037, c_42])).
% 4.44/1.87  tff(c_2132, plain, (~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_2129, c_2111])).
% 4.44/1.87  tff(c_2144, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2042, c_2132])).
% 4.44/1.87  tff(c_2152, plain, (~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(resolution, [status(thm)], [c_2, c_2144])).
% 4.44/1.87  tff(c_2156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2036, c_2040, c_2152])).
% 4.44/1.87  tff(c_2157, plain, (r2_hidden('#skF_7', '#skF_10')), inference(splitRight, [status(thm)], [c_1522])).
% 4.44/1.87  tff(c_1008, plain, (r2_hidden('#skF_13', '#skF_16')), inference(splitRight, [status(thm)], [c_40])).
% 4.44/1.87  tff(c_2158, plain, (r2_hidden('#skF_14', '#skF_17')), inference(splitRight, [status(thm)], [c_1522])).
% 4.44/1.87  tff(c_1523, plain, (r2_hidden('#skF_15', '#skF_18')), inference(splitRight, [status(thm)], [c_1007])).
% 4.44/1.87  tff(c_38, plain, (r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_15', '#skF_18') | ~r2_hidden('#skF_14', '#skF_17') | ~r2_hidden('#skF_13', '#skF_16')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_2162, plain, (r2_hidden('#skF_8', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2158, c_1523, c_38])).
% 4.44/1.87  tff(c_36, plain, (r2_hidden('#skF_9', '#skF_12') | ~r2_hidden('#skF_15', '#skF_18') | ~r2_hidden('#skF_14', '#skF_17') | ~r2_hidden('#skF_13', '#skF_16')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_2160, plain, (r2_hidden('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2158, c_1523, c_36])).
% 4.44/1.87  tff(c_2202, plain, (![E_533, F_534, A_535, B_536]: (r2_hidden(k4_tarski(E_533, F_534), k2_zfmisc_1(A_535, B_536)) | ~r2_hidden(F_534, B_536) | ~r2_hidden(E_533, A_535))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.44/1.87  tff(c_2232, plain, (![B_558, F_561, C_559, E_560, A_557]: (r2_hidden(k4_tarski(E_560, F_561), k3_zfmisc_1(A_557, B_558, C_559)) | ~r2_hidden(F_561, C_559) | ~r2_hidden(E_560, k2_zfmisc_1(A_557, B_558)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2202])).
% 4.44/1.87  tff(c_2549, plain, (![C_612, A_611, B_613, C_609, A_610, B_614]: (r2_hidden(k3_mcart_1(A_610, B_613, C_612), k3_zfmisc_1(A_611, B_614, C_609)) | ~r2_hidden(C_612, C_609) | ~r2_hidden(k4_tarski(A_610, B_613), k2_zfmisc_1(A_611, B_614)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2232])).
% 4.44/1.87  tff(c_34, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12')) | ~r2_hidden('#skF_15', '#skF_18') | ~r2_hidden('#skF_14', '#skF_17') | ~r2_hidden('#skF_13', '#skF_16')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.87  tff(c_2221, plain, (~r2_hidden(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'), k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_2158, c_1523, c_34])).
% 4.44/1.87  tff(c_2554, plain, (~r2_hidden('#skF_9', '#skF_12') | ~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_2549, c_2221])).
% 4.44/1.87  tff(c_2565, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_2554])).
% 4.44/1.87  tff(c_2570, plain, (~r2_hidden('#skF_8', '#skF_11') | ~r2_hidden('#skF_7', '#skF_10')), inference(resolution, [status(thm)], [c_2, c_2565])).
% 4.44/1.87  tff(c_2574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2157, c_2162, c_2570])).
% 4.44/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.87  
% 4.44/1.87  Inference rules
% 4.44/1.87  ----------------------
% 4.44/1.87  #Ref     : 0
% 4.44/1.87  #Sup     : 611
% 4.44/1.87  #Fact    : 0
% 4.44/1.87  #Define  : 0
% 4.44/1.87  #Split   : 9
% 4.44/1.87  #Chain   : 0
% 4.44/1.87  #Close   : 0
% 4.44/1.87  
% 4.44/1.87  Ordering : KBO
% 4.44/1.87  
% 4.44/1.87  Simplification rules
% 4.44/1.87  ----------------------
% 4.44/1.87  #Subsume      : 98
% 4.44/1.87  #Demod        : 381
% 4.44/1.87  #Tautology    : 190
% 4.44/1.87  #SimpNegUnit  : 12
% 4.44/1.87  #BackRed      : 0
% 4.44/1.87  
% 4.44/1.87  #Partial instantiations: 0
% 4.44/1.87  #Strategies tried      : 1
% 4.44/1.87  
% 4.44/1.87  Timing (in seconds)
% 4.44/1.87  ----------------------
% 4.44/1.87  Preprocessing        : 0.30
% 4.44/1.87  Parsing              : 0.14
% 4.44/1.87  CNF conversion       : 0.03
% 4.44/1.87  Main loop            : 0.74
% 4.44/1.87  Inferencing          : 0.31
% 4.44/1.87  Reduction            : 0.23
% 4.44/1.87  Demodulation         : 0.17
% 4.44/1.87  BG Simplification    : 0.05
% 4.44/1.87  Subsumption          : 0.11
% 4.44/1.87  Abstraction          : 0.06
% 4.44/1.87  MUC search           : 0.00
% 4.44/1.87  Cooper               : 0.00
% 4.44/1.87  Total                : 1.11
% 4.44/1.87  Index Insertion      : 0.00
% 4.44/1.87  Index Deletion       : 0.00
% 4.44/1.87  Index Matching       : 0.00
% 4.44/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
