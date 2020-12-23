%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:15 EST 2020

% Result     : Theorem 16.90s
% Output     : CNFRefutation 16.99s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 312 expanded)
%              Number of leaves         :   39 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 456 expanded)
%              Number of equality atoms :   81 ( 196 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_108,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_10','#skF_11')
    | r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_250,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_106,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_10','#skF_11')
    | r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_169,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_2690,plain,(
    ! [A_206,C_207,B_208] :
      ( r1_xboole_0(k2_tarski(A_206,C_207),B_208)
      | r2_hidden(C_207,B_208)
      | r2_hidden(A_206,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = A_33
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59089,plain,(
    ! [A_893,C_894,B_895] :
      ( k4_xboole_0(k2_tarski(A_893,C_894),B_895) = k2_tarski(A_893,C_894)
      | r2_hidden(C_894,B_895)
      | r2_hidden(A_893,B_895) ) ),
    inference(resolution,[status(thm)],[c_2690,c_54])).

tff(c_104,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k2_tarski('#skF_6','#skF_7')
    | r2_hidden('#skF_10','#skF_11')
    | r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_737,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k2_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_59487,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_59089,c_737])).

tff(c_59696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_169,c_59487])).

tff(c_59697,plain,
    ( r2_hidden('#skF_9','#skF_11')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_59699,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_59697])).

tff(c_74,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),k1_tarski(B_45)) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [C_43] : r2_hidden(C_43,k1_tarski(C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_170,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k2_xboole_0(A_77,B_78)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_183,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_170])).

tff(c_261,plain,(
    ! [B_91,A_92] :
      ( ~ r2_hidden(B_91,A_92)
      | k4_xboole_0(A_92,k1_tarski(B_91)) != A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_265,plain,(
    ! [B_91] :
      ( ~ r2_hidden(B_91,k1_tarski(B_91))
      | k1_tarski(B_91) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_261])).

tff(c_271,plain,(
    ! [B_91] : k1_tarski(B_91) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_265])).

tff(c_60,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_115,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58])).

tff(c_229,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = A_83
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60396,plain,(
    ! [A_935,B_936] : k4_xboole_0(k4_xboole_0(A_935,B_936),B_936) = k4_xboole_0(A_935,B_936) ),
    inference(resolution,[status(thm)],[c_115,c_229])).

tff(c_60416,plain,(
    ! [B_936,A_935] : k5_xboole_0(B_936,k4_xboole_0(A_935,B_936)) = k2_xboole_0(B_936,k4_xboole_0(A_935,B_936)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60396,c_60])).

tff(c_60489,plain,(
    ! [B_936,A_935] : k2_xboole_0(B_936,k4_xboole_0(A_935,B_936)) = k2_xboole_0(B_936,A_935) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60416])).

tff(c_62449,plain,(
    ! [A_1006,B_1007,C_1008] : k4_xboole_0(k4_xboole_0(A_1006,B_1007),C_1008) = k4_xboole_0(A_1006,k2_xboole_0(B_1007,C_1008)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62526,plain,(
    ! [A_1006,B_1007] : k4_xboole_0(A_1006,k2_xboole_0(B_1007,k4_xboole_0(A_1006,B_1007))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62449,c_183])).

tff(c_62636,plain,(
    ! [A_1009,B_1010] : k4_xboole_0(A_1009,k2_xboole_0(B_1010,A_1009)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60489,c_62526])).

tff(c_621,plain,(
    ! [A_118,B_119] : k2_xboole_0(k1_tarski(A_118),k1_tarski(B_119)) = k2_tarski(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_634,plain,(
    ! [B_119] : k2_tarski(B_119,B_119) = k1_tarski(B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_20])).

tff(c_100,plain,(
    ! [B_64,C_65] :
      ( k4_xboole_0(k2_tarski(B_64,B_64),C_65) = k1_tarski(B_64)
      | r2_hidden(B_64,C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_61389,plain,(
    ! [B_64,C_65] :
      ( k4_xboole_0(k1_tarski(B_64),C_65) = k1_tarski(B_64)
      | r2_hidden(B_64,C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_100])).

tff(c_62666,plain,(
    ! [B_64,B_1010] :
      ( k1_tarski(B_64) = k1_xboole_0
      | r2_hidden(B_64,k2_xboole_0(B_1010,k1_tarski(B_64))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62636,c_61389])).

tff(c_62782,plain,(
    ! [B_1011,B_1012] : r2_hidden(B_1011,k2_xboole_0(B_1012,k1_tarski(B_1011))) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_62666])).

tff(c_62803,plain,(
    ! [B_1013,A_1014] : r2_hidden(B_1013,k2_tarski(A_1014,B_1013)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_62782])).

tff(c_110,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k2_tarski('#skF_6','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_59710,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k2_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_59698,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k2_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_59946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59710,c_59698])).

tff(c_59947,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_60255,plain,(
    r1_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_59947,c_115])).

tff(c_60831,plain,(
    ! [A_950,B_951,C_952] :
      ( ~ r1_xboole_0(A_950,B_951)
      | ~ r2_hidden(C_952,B_951)
      | ~ r2_hidden(C_952,A_950) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60850,plain,(
    ! [C_952] :
      ( ~ r2_hidden(C_952,'#skF_11')
      | ~ r2_hidden(C_952,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_60255,c_60831])).

tff(c_62811,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_62803,c_60850])).

tff(c_62819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59699,c_62811])).

tff(c_62820,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_59697])).

tff(c_62994,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k2_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_63068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62994,c_59698])).

tff(c_63069,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_63214,plain,(
    r1_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_63069,c_115])).

tff(c_78,plain,(
    ! [A_49,C_51,B_50] :
      ( ~ r2_hidden(A_49,C_51)
      | ~ r1_xboole_0(k2_tarski(A_49,B_50),C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_63221,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_63214,c_78])).

tff(c_63228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62820,c_63221])).

tff(c_63229,plain,
    ( r2_hidden('#skF_9','#skF_11')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_63231,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_63229])).

tff(c_63977,plain,(
    ! [B_1085,A_1086] :
      ( ~ r2_hidden(B_1085,A_1086)
      | k4_xboole_0(A_1086,k1_tarski(B_1085)) != A_1086 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_63988,plain,(
    ! [B_1085] :
      ( ~ r2_hidden(B_1085,k1_tarski(B_1085))
      | k1_tarski(B_1085) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_63977])).

tff(c_63995,plain,(
    ! [B_1085] : k1_tarski(B_1085) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63988])).

tff(c_63695,plain,(
    ! [A_1071,B_1072] : k2_xboole_0(k1_tarski(A_1071),k1_tarski(B_1072)) = k2_tarski(A_1071,B_1072) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_63711,plain,(
    ! [B_1072] : k2_tarski(B_1072,B_1072) = k1_tarski(B_1072) ),
    inference(superposition,[status(thm),theory(equality)],[c_63695,c_20])).

tff(c_65764,plain,(
    ! [B_1156,C_1157] :
      ( k4_xboole_0(k1_tarski(B_1156),C_1157) = k1_tarski(B_1156)
      | r2_hidden(B_1156,C_1157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63711,c_100])).

tff(c_64133,plain,(
    ! [A_1095,B_1096] : k4_xboole_0(k4_xboole_0(A_1095,B_1096),B_1096) = k4_xboole_0(A_1095,B_1096) ),
    inference(resolution,[status(thm)],[c_115,c_229])).

tff(c_64149,plain,(
    ! [B_1096,A_1095] : k5_xboole_0(B_1096,k4_xboole_0(A_1095,B_1096)) = k2_xboole_0(B_1096,k4_xboole_0(A_1095,B_1096)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64133,c_60])).

tff(c_64218,plain,(
    ! [B_1096,A_1095] : k2_xboole_0(B_1096,k4_xboole_0(A_1095,B_1096)) = k2_xboole_0(B_1096,A_1095) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64149])).

tff(c_65049,plain,(
    ! [A_1138,B_1139,C_1140] : k4_xboole_0(k4_xboole_0(A_1138,B_1139),C_1140) = k4_xboole_0(A_1138,k2_xboole_0(B_1139,C_1140)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_65117,plain,(
    ! [A_1138,B_1139] : k4_xboole_0(A_1138,k2_xboole_0(B_1139,k4_xboole_0(A_1138,B_1139))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_65049,c_183])).

tff(c_65217,plain,(
    ! [A_1141,B_1142] : k4_xboole_0(A_1141,k2_xboole_0(B_1142,A_1141)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64218,c_65117])).

tff(c_65287,plain,(
    ! [B_45,A_44] : k4_xboole_0(k1_tarski(B_45),k2_tarski(A_44,B_45)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_65217])).

tff(c_65775,plain,(
    ! [B_1156,A_44] :
      ( k1_tarski(B_1156) = k1_xboole_0
      | r2_hidden(B_1156,k2_tarski(A_44,B_1156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65764,c_65287])).

tff(c_65933,plain,(
    ! [B_1160,A_1161] : r2_hidden(B_1160,k2_tarski(A_1161,B_1160)) ),
    inference(negUnitSimplification,[status(thm)],[c_63995,c_65775])).

tff(c_63230,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_114,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_63465,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63230,c_114])).

tff(c_63475,plain,(
    r1_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_63465,c_115])).

tff(c_64872,plain,(
    ! [A_1119,B_1120,C_1121] :
      ( ~ r1_xboole_0(A_1119,B_1120)
      | ~ r2_hidden(C_1121,B_1120)
      | ~ r2_hidden(C_1121,A_1119) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64891,plain,(
    ! [C_1121] :
      ( ~ r2_hidden(C_1121,'#skF_11')
      | ~ r2_hidden(C_1121,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_63475,c_64872])).

tff(c_65937,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_65933,c_64891])).

tff(c_65944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63231,c_65937])).

tff(c_65945,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_63229])).

tff(c_65948,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63230,c_114])).

tff(c_65952,plain,(
    r1_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_65948,c_115])).

tff(c_65983,plain,(
    ! [A_1166,C_1167,B_1168] :
      ( ~ r2_hidden(A_1166,C_1167)
      | ~ r1_xboole_0(k2_tarski(A_1166,B_1168),C_1167) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_65986,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_65952,c_65983])).

tff(c_65998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65945,c_65986])).

tff(c_65999,plain,
    ( r2_hidden('#skF_9','#skF_11')
    | r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_66061,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_65999])).

tff(c_66001,plain,(
    ! [A_1169,B_1170] : k4_xboole_0(A_1169,k2_xboole_0(A_1169,B_1170)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66014,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_66001])).

tff(c_66093,plain,(
    ! [B_1183,A_1184] :
      ( ~ r2_hidden(B_1183,A_1184)
      | k4_xboole_0(A_1184,k1_tarski(B_1183)) != A_1184 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_66097,plain,(
    ! [B_1183] :
      ( ~ r2_hidden(B_1183,k1_tarski(B_1183))
      | k1_tarski(B_1183) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66014,c_66093])).

tff(c_66103,plain,(
    ! [B_1183] : k1_tarski(B_1183) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66097])).

tff(c_66074,plain,(
    ! [A_1181,B_1182] :
      ( k4_xboole_0(A_1181,B_1182) = A_1181
      | ~ r1_xboole_0(A_1181,B_1182) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_67278,plain,(
    ! [A_1252,B_1253] : k4_xboole_0(k4_xboole_0(A_1252,B_1253),B_1253) = k4_xboole_0(A_1252,B_1253) ),
    inference(resolution,[status(thm)],[c_115,c_66074])).

tff(c_67296,plain,(
    ! [B_1253,A_1252] : k5_xboole_0(B_1253,k4_xboole_0(A_1252,B_1253)) = k2_xboole_0(B_1253,k4_xboole_0(A_1252,B_1253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67278,c_60])).

tff(c_67367,plain,(
    ! [B_1253,A_1252] : k2_xboole_0(B_1253,k4_xboole_0(A_1252,B_1253)) = k2_xboole_0(B_1253,A_1252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_67296])).

tff(c_68949,plain,(
    ! [A_1304,B_1305,C_1306] : k4_xboole_0(k4_xboole_0(A_1304,B_1305),C_1306) = k4_xboole_0(A_1304,k2_xboole_0(B_1305,C_1306)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_69022,plain,(
    ! [A_1304,B_1305] : k4_xboole_0(A_1304,k2_xboole_0(B_1305,k4_xboole_0(A_1304,B_1305))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68949,c_66014])).

tff(c_69133,plain,(
    ! [A_1307,B_1308] : k4_xboole_0(A_1307,k2_xboole_0(B_1308,A_1307)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67367,c_69022])).

tff(c_66911,plain,(
    ! [A_1234,B_1235] : k2_xboole_0(k1_tarski(A_1234),k1_tarski(B_1235)) = k2_tarski(A_1234,B_1235) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66927,plain,(
    ! [B_1235] : k2_tarski(B_1235,B_1235) = k1_tarski(B_1235) ),
    inference(superposition,[status(thm),theory(equality)],[c_66911,c_20])).

tff(c_68143,plain,(
    ! [B_64,C_65] :
      ( k4_xboole_0(k1_tarski(B_64),C_65) = k1_tarski(B_64)
      | r2_hidden(B_64,C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66927,c_100])).

tff(c_69154,plain,(
    ! [B_64,B_1308] :
      ( k1_tarski(B_64) = k1_xboole_0
      | r2_hidden(B_64,k2_xboole_0(B_1308,k1_tarski(B_64))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69133,c_68143])).

tff(c_69271,plain,(
    ! [B_1309,B_1310] : r2_hidden(B_1309,k2_xboole_0(B_1310,k1_tarski(B_1309))) ),
    inference(negUnitSimplification,[status(thm)],[c_66103,c_69154])).

tff(c_69385,plain,(
    ! [B_1312,A_1313] : r2_hidden(B_1312,k2_tarski(A_1313,B_1312)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_69271])).

tff(c_66000,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_112,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_66242,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66000,c_112])).

tff(c_66246,plain,(
    r1_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_66242,c_115])).

tff(c_67194,plain,(
    ! [A_1247,B_1248,C_1249] :
      ( ~ r1_xboole_0(A_1247,B_1248)
      | ~ r2_hidden(C_1249,B_1248)
      | ~ r2_hidden(C_1249,A_1247) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67213,plain,(
    ! [C_1249] :
      ( ~ r2_hidden(C_1249,'#skF_11')
      | ~ r2_hidden(C_1249,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_66246,c_67194])).

tff(c_69389,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_69385,c_67213])).

tff(c_69396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66061,c_69389])).

tff(c_69397,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_65999])).

tff(c_69577,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66000,c_112])).

tff(c_69584,plain,(
    r1_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_69577,c_115])).

tff(c_69590,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_69584,c_78])).

tff(c_69597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69397,c_69590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n001.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 18:29:00 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.90/8.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.90/8.37  
% 16.90/8.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.90/8.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 16.90/8.37  
% 16.90/8.37  %Foreground sorts:
% 16.90/8.37  
% 16.90/8.37  
% 16.90/8.37  %Background operators:
% 16.90/8.37  
% 16.90/8.37  
% 16.90/8.37  %Foreground operators:
% 16.90/8.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.90/8.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.90/8.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.90/8.37  tff('#skF_11', type, '#skF_11': $i).
% 16.90/8.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.90/8.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.90/8.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.90/8.37  tff('#skF_7', type, '#skF_7': $i).
% 16.90/8.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.90/8.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.90/8.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.90/8.37  tff('#skF_10', type, '#skF_10': $i).
% 16.90/8.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.90/8.37  tff('#skF_6', type, '#skF_6': $i).
% 16.90/8.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.90/8.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.90/8.37  tff('#skF_9', type, '#skF_9': $i).
% 16.90/8.37  tff('#skF_8', type, '#skF_8': $i).
% 16.90/8.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.90/8.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.90/8.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.90/8.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.90/8.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.90/8.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.90/8.37  
% 16.99/8.40  tff(f_157, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 16.99/8.40  tff(f_118, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 16.99/8.40  tff(f_84, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 16.99/8.40  tff(f_97, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 16.99/8.40  tff(f_95, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 16.99/8.40  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 16.99/8.40  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 16.99/8.40  tff(f_139, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 16.99/8.40  tff(f_88, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 16.99/8.40  tff(f_76, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 16.99/8.40  tff(f_86, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 16.99/8.40  tff(f_72, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 16.99/8.40  tff(f_148, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 16.99/8.40  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.99/8.40  tff(f_108, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 16.99/8.40  tff(c_108, plain, (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_10', '#skF_11') | r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_157])).
% 16.99/8.40  tff(c_250, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_108])).
% 16.99/8.40  tff(c_106, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_10', '#skF_11') | r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_157])).
% 16.99/8.40  tff(c_169, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_106])).
% 16.99/8.40  tff(c_2690, plain, (![A_206, C_207, B_208]: (r1_xboole_0(k2_tarski(A_206, C_207), B_208) | r2_hidden(C_207, B_208) | r2_hidden(A_206, B_208))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.99/8.40  tff(c_54, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=A_33 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.99/8.40  tff(c_59089, plain, (![A_893, C_894, B_895]: (k4_xboole_0(k2_tarski(A_893, C_894), B_895)=k2_tarski(A_893, C_894) | r2_hidden(C_894, B_895) | r2_hidden(A_893, B_895))), inference(resolution, [status(thm)], [c_2690, c_54])).
% 16.99/8.40  tff(c_104, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k2_tarski('#skF_6', '#skF_7') | r2_hidden('#skF_10', '#skF_11') | r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_157])).
% 16.99/8.40  tff(c_737, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k2_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_104])).
% 16.99/8.40  tff(c_59487, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_59089, c_737])).
% 16.99/8.40  tff(c_59696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_169, c_59487])).
% 16.99/8.40  tff(c_59697, plain, (r2_hidden('#skF_9', '#skF_11') | r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_104])).
% 16.99/8.40  tff(c_59699, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_59697])).
% 16.99/8.40  tff(c_74, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), k1_tarski(B_45))=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.99/8.40  tff(c_64, plain, (![C_43]: (r2_hidden(C_43, k1_tarski(C_43)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 16.99/8.40  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.99/8.40  tff(c_170, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k2_xboole_0(A_77, B_78))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.99/8.40  tff(c_183, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_170])).
% 16.99/8.40  tff(c_261, plain, (![B_91, A_92]: (~r2_hidden(B_91, A_92) | k4_xboole_0(A_92, k1_tarski(B_91))!=A_92)), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.99/8.40  tff(c_265, plain, (![B_91]: (~r2_hidden(B_91, k1_tarski(B_91)) | k1_tarski(B_91)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_261])).
% 16.99/8.40  tff(c_271, plain, (![B_91]: (k1_tarski(B_91)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_265])).
% 16.99/8.40  tff(c_60, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.99/8.40  tff(c_48, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.99/8.40  tff(c_58, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, k3_xboole_0(A_35, B_36)), B_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.99/8.40  tff(c_115, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58])).
% 16.99/8.40  tff(c_229, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=A_83 | ~r1_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.99/8.40  tff(c_60396, plain, (![A_935, B_936]: (k4_xboole_0(k4_xboole_0(A_935, B_936), B_936)=k4_xboole_0(A_935, B_936))), inference(resolution, [status(thm)], [c_115, c_229])).
% 16.99/8.40  tff(c_60416, plain, (![B_936, A_935]: (k5_xboole_0(B_936, k4_xboole_0(A_935, B_936))=k2_xboole_0(B_936, k4_xboole_0(A_935, B_936)))), inference(superposition, [status(thm), theory('equality')], [c_60396, c_60])).
% 16.99/8.40  tff(c_60489, plain, (![B_936, A_935]: (k2_xboole_0(B_936, k4_xboole_0(A_935, B_936))=k2_xboole_0(B_936, A_935))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60416])).
% 16.99/8.40  tff(c_62449, plain, (![A_1006, B_1007, C_1008]: (k4_xboole_0(k4_xboole_0(A_1006, B_1007), C_1008)=k4_xboole_0(A_1006, k2_xboole_0(B_1007, C_1008)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.99/8.40  tff(c_62526, plain, (![A_1006, B_1007]: (k4_xboole_0(A_1006, k2_xboole_0(B_1007, k4_xboole_0(A_1006, B_1007)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62449, c_183])).
% 16.99/8.40  tff(c_62636, plain, (![A_1009, B_1010]: (k4_xboole_0(A_1009, k2_xboole_0(B_1010, A_1009))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60489, c_62526])).
% 16.99/8.40  tff(c_621, plain, (![A_118, B_119]: (k2_xboole_0(k1_tarski(A_118), k1_tarski(B_119))=k2_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.99/8.40  tff(c_634, plain, (![B_119]: (k2_tarski(B_119, B_119)=k1_tarski(B_119))), inference(superposition, [status(thm), theory('equality')], [c_621, c_20])).
% 16.99/8.40  tff(c_100, plain, (![B_64, C_65]: (k4_xboole_0(k2_tarski(B_64, B_64), C_65)=k1_tarski(B_64) | r2_hidden(B_64, C_65))), inference(cnfTransformation, [status(thm)], [f_148])).
% 16.99/8.40  tff(c_61389, plain, (![B_64, C_65]: (k4_xboole_0(k1_tarski(B_64), C_65)=k1_tarski(B_64) | r2_hidden(B_64, C_65))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_100])).
% 16.99/8.40  tff(c_62666, plain, (![B_64, B_1010]: (k1_tarski(B_64)=k1_xboole_0 | r2_hidden(B_64, k2_xboole_0(B_1010, k1_tarski(B_64))))), inference(superposition, [status(thm), theory('equality')], [c_62636, c_61389])).
% 16.99/8.40  tff(c_62782, plain, (![B_1011, B_1012]: (r2_hidden(B_1011, k2_xboole_0(B_1012, k1_tarski(B_1011))))), inference(negUnitSimplification, [status(thm)], [c_271, c_62666])).
% 16.99/8.40  tff(c_62803, plain, (![B_1013, A_1014]: (r2_hidden(B_1013, k2_tarski(A_1014, B_1013)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_62782])).
% 16.99/8.40  tff(c_110, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k2_tarski('#skF_6', '#skF_7') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_157])).
% 16.99/8.40  tff(c_59710, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k2_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_110])).
% 16.99/8.40  tff(c_59698, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k2_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_104])).
% 16.99/8.40  tff(c_59946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59710, c_59698])).
% 16.99/8.40  tff(c_59947, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_110])).
% 16.99/8.40  tff(c_60255, plain, (r1_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_59947, c_115])).
% 16.99/8.40  tff(c_60831, plain, (![A_950, B_951, C_952]: (~r1_xboole_0(A_950, B_951) | ~r2_hidden(C_952, B_951) | ~r2_hidden(C_952, A_950))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.99/8.40  tff(c_60850, plain, (![C_952]: (~r2_hidden(C_952, '#skF_11') | ~r2_hidden(C_952, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_60255, c_60831])).
% 16.99/8.40  tff(c_62811, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_62803, c_60850])).
% 16.99/8.40  tff(c_62819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59699, c_62811])).
% 16.99/8.40  tff(c_62820, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_59697])).
% 16.99/8.40  tff(c_62994, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k2_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_110])).
% 16.99/8.40  tff(c_63068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62994, c_59698])).
% 16.99/8.40  tff(c_63069, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_110])).
% 16.99/8.40  tff(c_63214, plain, (r1_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_63069, c_115])).
% 16.99/8.40  tff(c_78, plain, (![A_49, C_51, B_50]: (~r2_hidden(A_49, C_51) | ~r1_xboole_0(k2_tarski(A_49, B_50), C_51))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.99/8.40  tff(c_63221, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_63214, c_78])).
% 16.99/8.40  tff(c_63228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62820, c_63221])).
% 16.99/8.40  tff(c_63229, plain, (r2_hidden('#skF_9', '#skF_11') | r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_108])).
% 16.99/8.40  tff(c_63231, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_63229])).
% 16.99/8.40  tff(c_63977, plain, (![B_1085, A_1086]: (~r2_hidden(B_1085, A_1086) | k4_xboole_0(A_1086, k1_tarski(B_1085))!=A_1086)), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.99/8.40  tff(c_63988, plain, (![B_1085]: (~r2_hidden(B_1085, k1_tarski(B_1085)) | k1_tarski(B_1085)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_63977])).
% 16.99/8.40  tff(c_63995, plain, (![B_1085]: (k1_tarski(B_1085)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63988])).
% 16.99/8.40  tff(c_63695, plain, (![A_1071, B_1072]: (k2_xboole_0(k1_tarski(A_1071), k1_tarski(B_1072))=k2_tarski(A_1071, B_1072))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.99/8.40  tff(c_63711, plain, (![B_1072]: (k2_tarski(B_1072, B_1072)=k1_tarski(B_1072))), inference(superposition, [status(thm), theory('equality')], [c_63695, c_20])).
% 16.99/8.40  tff(c_65764, plain, (![B_1156, C_1157]: (k4_xboole_0(k1_tarski(B_1156), C_1157)=k1_tarski(B_1156) | r2_hidden(B_1156, C_1157))), inference(demodulation, [status(thm), theory('equality')], [c_63711, c_100])).
% 16.99/8.40  tff(c_64133, plain, (![A_1095, B_1096]: (k4_xboole_0(k4_xboole_0(A_1095, B_1096), B_1096)=k4_xboole_0(A_1095, B_1096))), inference(resolution, [status(thm)], [c_115, c_229])).
% 16.99/8.40  tff(c_64149, plain, (![B_1096, A_1095]: (k5_xboole_0(B_1096, k4_xboole_0(A_1095, B_1096))=k2_xboole_0(B_1096, k4_xboole_0(A_1095, B_1096)))), inference(superposition, [status(thm), theory('equality')], [c_64133, c_60])).
% 16.99/8.40  tff(c_64218, plain, (![B_1096, A_1095]: (k2_xboole_0(B_1096, k4_xboole_0(A_1095, B_1096))=k2_xboole_0(B_1096, A_1095))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64149])).
% 16.99/8.40  tff(c_65049, plain, (![A_1138, B_1139, C_1140]: (k4_xboole_0(k4_xboole_0(A_1138, B_1139), C_1140)=k4_xboole_0(A_1138, k2_xboole_0(B_1139, C_1140)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.99/8.40  tff(c_65117, plain, (![A_1138, B_1139]: (k4_xboole_0(A_1138, k2_xboole_0(B_1139, k4_xboole_0(A_1138, B_1139)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65049, c_183])).
% 16.99/8.40  tff(c_65217, plain, (![A_1141, B_1142]: (k4_xboole_0(A_1141, k2_xboole_0(B_1142, A_1141))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64218, c_65117])).
% 16.99/8.40  tff(c_65287, plain, (![B_45, A_44]: (k4_xboole_0(k1_tarski(B_45), k2_tarski(A_44, B_45))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_65217])).
% 16.99/8.40  tff(c_65775, plain, (![B_1156, A_44]: (k1_tarski(B_1156)=k1_xboole_0 | r2_hidden(B_1156, k2_tarski(A_44, B_1156)))), inference(superposition, [status(thm), theory('equality')], [c_65764, c_65287])).
% 16.99/8.40  tff(c_65933, plain, (![B_1160, A_1161]: (r2_hidden(B_1160, k2_tarski(A_1161, B_1160)))), inference(negUnitSimplification, [status(thm)], [c_63995, c_65775])).
% 16.99/8.40  tff(c_63230, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_108])).
% 16.99/8.40  tff(c_114, plain, (~r2_hidden('#skF_6', '#skF_8') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_157])).
% 16.99/8.40  tff(c_63465, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_63230, c_114])).
% 16.99/8.40  tff(c_63475, plain, (r1_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_63465, c_115])).
% 16.99/8.40  tff(c_64872, plain, (![A_1119, B_1120, C_1121]: (~r1_xboole_0(A_1119, B_1120) | ~r2_hidden(C_1121, B_1120) | ~r2_hidden(C_1121, A_1119))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.99/8.40  tff(c_64891, plain, (![C_1121]: (~r2_hidden(C_1121, '#skF_11') | ~r2_hidden(C_1121, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_63475, c_64872])).
% 16.99/8.40  tff(c_65937, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_65933, c_64891])).
% 16.99/8.40  tff(c_65944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63231, c_65937])).
% 16.99/8.40  tff(c_65945, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_63229])).
% 16.99/8.40  tff(c_65948, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_63230, c_114])).
% 16.99/8.40  tff(c_65952, plain, (r1_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_65948, c_115])).
% 16.99/8.40  tff(c_65983, plain, (![A_1166, C_1167, B_1168]: (~r2_hidden(A_1166, C_1167) | ~r1_xboole_0(k2_tarski(A_1166, B_1168), C_1167))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.99/8.40  tff(c_65986, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_65952, c_65983])).
% 16.99/8.40  tff(c_65998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65945, c_65986])).
% 16.99/8.40  tff(c_65999, plain, (r2_hidden('#skF_9', '#skF_11') | r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_106])).
% 16.99/8.40  tff(c_66061, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_65999])).
% 16.99/8.40  tff(c_66001, plain, (![A_1169, B_1170]: (k4_xboole_0(A_1169, k2_xboole_0(A_1169, B_1170))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.99/8.40  tff(c_66014, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_66001])).
% 16.99/8.40  tff(c_66093, plain, (![B_1183, A_1184]: (~r2_hidden(B_1183, A_1184) | k4_xboole_0(A_1184, k1_tarski(B_1183))!=A_1184)), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.99/8.40  tff(c_66097, plain, (![B_1183]: (~r2_hidden(B_1183, k1_tarski(B_1183)) | k1_tarski(B_1183)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66014, c_66093])).
% 16.99/8.40  tff(c_66103, plain, (![B_1183]: (k1_tarski(B_1183)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66097])).
% 16.99/8.40  tff(c_66074, plain, (![A_1181, B_1182]: (k4_xboole_0(A_1181, B_1182)=A_1181 | ~r1_xboole_0(A_1181, B_1182))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.99/8.40  tff(c_67278, plain, (![A_1252, B_1253]: (k4_xboole_0(k4_xboole_0(A_1252, B_1253), B_1253)=k4_xboole_0(A_1252, B_1253))), inference(resolution, [status(thm)], [c_115, c_66074])).
% 16.99/8.40  tff(c_67296, plain, (![B_1253, A_1252]: (k5_xboole_0(B_1253, k4_xboole_0(A_1252, B_1253))=k2_xboole_0(B_1253, k4_xboole_0(A_1252, B_1253)))), inference(superposition, [status(thm), theory('equality')], [c_67278, c_60])).
% 16.99/8.40  tff(c_67367, plain, (![B_1253, A_1252]: (k2_xboole_0(B_1253, k4_xboole_0(A_1252, B_1253))=k2_xboole_0(B_1253, A_1252))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_67296])).
% 16.99/8.40  tff(c_68949, plain, (![A_1304, B_1305, C_1306]: (k4_xboole_0(k4_xboole_0(A_1304, B_1305), C_1306)=k4_xboole_0(A_1304, k2_xboole_0(B_1305, C_1306)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.99/8.40  tff(c_69022, plain, (![A_1304, B_1305]: (k4_xboole_0(A_1304, k2_xboole_0(B_1305, k4_xboole_0(A_1304, B_1305)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68949, c_66014])).
% 16.99/8.40  tff(c_69133, plain, (![A_1307, B_1308]: (k4_xboole_0(A_1307, k2_xboole_0(B_1308, A_1307))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67367, c_69022])).
% 16.99/8.40  tff(c_66911, plain, (![A_1234, B_1235]: (k2_xboole_0(k1_tarski(A_1234), k1_tarski(B_1235))=k2_tarski(A_1234, B_1235))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.99/8.40  tff(c_66927, plain, (![B_1235]: (k2_tarski(B_1235, B_1235)=k1_tarski(B_1235))), inference(superposition, [status(thm), theory('equality')], [c_66911, c_20])).
% 16.99/8.40  tff(c_68143, plain, (![B_64, C_65]: (k4_xboole_0(k1_tarski(B_64), C_65)=k1_tarski(B_64) | r2_hidden(B_64, C_65))), inference(demodulation, [status(thm), theory('equality')], [c_66927, c_100])).
% 16.99/8.40  tff(c_69154, plain, (![B_64, B_1308]: (k1_tarski(B_64)=k1_xboole_0 | r2_hidden(B_64, k2_xboole_0(B_1308, k1_tarski(B_64))))), inference(superposition, [status(thm), theory('equality')], [c_69133, c_68143])).
% 16.99/8.40  tff(c_69271, plain, (![B_1309, B_1310]: (r2_hidden(B_1309, k2_xboole_0(B_1310, k1_tarski(B_1309))))), inference(negUnitSimplification, [status(thm)], [c_66103, c_69154])).
% 16.99/8.40  tff(c_69385, plain, (![B_1312, A_1313]: (r2_hidden(B_1312, k2_tarski(A_1313, B_1312)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_69271])).
% 16.99/8.40  tff(c_66000, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_106])).
% 16.99/8.40  tff(c_112, plain, (~r2_hidden('#skF_7', '#skF_8') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_157])).
% 16.99/8.40  tff(c_66242, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_66000, c_112])).
% 16.99/8.40  tff(c_66246, plain, (r1_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_66242, c_115])).
% 16.99/8.40  tff(c_67194, plain, (![A_1247, B_1248, C_1249]: (~r1_xboole_0(A_1247, B_1248) | ~r2_hidden(C_1249, B_1248) | ~r2_hidden(C_1249, A_1247))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.99/8.40  tff(c_67213, plain, (![C_1249]: (~r2_hidden(C_1249, '#skF_11') | ~r2_hidden(C_1249, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_66246, c_67194])).
% 16.99/8.40  tff(c_69389, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_69385, c_67213])).
% 16.99/8.40  tff(c_69396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66061, c_69389])).
% 16.99/8.40  tff(c_69397, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_65999])).
% 16.99/8.40  tff(c_69577, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_66000, c_112])).
% 16.99/8.40  tff(c_69584, plain, (r1_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_69577, c_115])).
% 16.99/8.40  tff(c_69590, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_69584, c_78])).
% 16.99/8.40  tff(c_69597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69397, c_69590])).
% 16.99/8.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.99/8.40  
% 16.99/8.40  Inference rules
% 16.99/8.40  ----------------------
% 16.99/8.40  #Ref     : 0
% 16.99/8.40  #Sup     : 17093
% 16.99/8.40  #Fact    : 0
% 16.99/8.40  #Define  : 0
% 16.99/8.40  #Split   : 9
% 16.99/8.40  #Chain   : 0
% 16.99/8.40  #Close   : 0
% 16.99/8.40  
% 16.99/8.40  Ordering : KBO
% 16.99/8.40  
% 16.99/8.40  Simplification rules
% 16.99/8.40  ----------------------
% 16.99/8.40  #Subsume      : 2096
% 16.99/8.40  #Demod        : 14068
% 16.99/8.40  #Tautology    : 9733
% 16.99/8.40  #SimpNegUnit  : 483
% 16.99/8.40  #BackRed      : 50
% 16.99/8.40  
% 16.99/8.40  #Partial instantiations: 0
% 16.99/8.40  #Strategies tried      : 1
% 16.99/8.40  
% 16.99/8.40  Timing (in seconds)
% 16.99/8.40  ----------------------
% 16.99/8.40  Preprocessing        : 0.34
% 16.99/8.40  Parsing              : 0.18
% 16.99/8.40  CNF conversion       : 0.03
% 16.99/8.40  Main loop            : 7.29
% 16.99/8.40  Inferencing          : 1.41
% 16.99/8.40  Reduction            : 3.69
% 16.99/8.40  Demodulation         : 3.08
% 16.99/8.40  BG Simplification    : 0.17
% 16.99/8.40  Subsumption          : 1.64
% 16.99/8.40  Abstraction          : 0.26
% 16.99/8.40  MUC search           : 0.00
% 16.99/8.40  Cooper               : 0.00
% 16.99/8.40  Total                : 7.69
% 16.99/8.40  Index Insertion      : 0.00
% 16.99/8.40  Index Deletion       : 0.00
% 16.99/8.40  Index Matching       : 0.00
% 16.99/8.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
