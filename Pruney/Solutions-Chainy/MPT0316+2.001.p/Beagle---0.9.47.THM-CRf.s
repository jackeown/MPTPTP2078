%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 179 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 323 expanded)
%              Number of equality atoms :   37 ( 124 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ~ ( k2_tarski(A,B) = k2_tarski(C,D)
        & A != C
        & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2007,plain,(
    ! [A_237,B_238] :
      ( r2_hidden(A_237,B_238)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_237),B_238),B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2131,plain,(
    ! [A_271,B_272] :
      ( r2_hidden(A_271,k1_tarski(B_272))
      | ~ r1_tarski(k2_tarski(A_271,B_272),k1_tarski(B_272)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2007])).

tff(c_2140,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,k1_tarski(A_7))
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2131])).

tff(c_2142,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2140])).

tff(c_557,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(A_79,B_80)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_79),B_80),B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_682,plain,(
    ! [A_113,B_114] :
      ( r2_hidden(A_113,k1_tarski(B_114))
      | ~ r1_tarski(k2_tarski(A_113,B_114),k1_tarski(B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_557])).

tff(c_691,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,k1_tarski(A_7))
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_682])).

tff(c_693,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_691])).

tff(c_46,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_97,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_156,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_334,plain,(
    ! [A_60,C_61,B_62,D_63] :
      ( r2_hidden(A_60,C_61)
      | ~ r2_hidden(k4_tarski(A_60,B_62),k2_zfmisc_1(C_61,D_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_338,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_156,c_334])).

tff(c_121,plain,(
    ! [A_38,B_39] : k2_xboole_0(k1_tarski(A_38),k1_tarski(B_39)) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(k1_tarski(A_30),B_31) = B_31
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_127,plain,(
    ! [A_38,B_39] :
      ( k2_tarski(A_38,B_39) = k1_tarski(B_39)
      | ~ r2_hidden(A_38,k1_tarski(B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_40])).

tff(c_346,plain,(
    k2_tarski('#skF_5','#skF_7') = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_338,c_127])).

tff(c_376,plain,(
    ! [D_64,A_65,C_66,B_67] :
      ( D_64 = A_65
      | C_66 = A_65
      | k2_tarski(C_66,D_64) != k2_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_407,plain,(
    ! [A_69,A_68,B_70] :
      ( A_69 = A_68
      | A_69 = A_68
      | k2_tarski(A_69,B_70) != k1_tarski(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_376])).

tff(c_413,plain,(
    ! [A_68] :
      ( A_68 = '#skF_5'
      | A_68 = '#skF_5'
      | k1_tarski(A_68) != k1_tarski('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_407])).

tff(c_430,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_5' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_413])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_97,c_430])).

tff(c_434,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_522,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_50])).

tff(c_1060,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( r2_hidden(k4_tarski(A_134,B_135),k2_zfmisc_1(C_136,D_137))
      | ~ r2_hidden(B_135,D_137)
      | ~ r2_hidden(A_134,C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_433,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_658,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_48])).

tff(c_659,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_658])).

tff(c_1069,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1060,c_659])).

tff(c_1090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_522,c_1069])).

tff(c_1092,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1196,plain,(
    ! [A_146,B_147] :
      ( r2_hidden(A_146,B_147)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_146),B_147),B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1464,plain,(
    ! [A_198,B_199] :
      ( r2_hidden(A_198,k1_tarski(B_199))
      | ~ r1_tarski(k2_tarski(A_198,B_199),k1_tarski(B_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1196])).

tff(c_1473,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,k1_tarski(A_7))
      | ~ r1_tarski(k1_tarski(A_7),k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1464])).

tff(c_1475,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1473])).

tff(c_1091,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1097,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1091])).

tff(c_1298,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_52])).

tff(c_1299,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1298])).

tff(c_1345,plain,(
    ! [B_162,D_163,A_164,C_165] :
      ( r2_hidden(B_162,D_163)
      | ~ r2_hidden(k4_tarski(A_164,B_162),k2_zfmisc_1(C_165,D_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1348,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_1299,c_1345])).

tff(c_1352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1097,c_1348])).

tff(c_1354,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1298])).

tff(c_1359,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_50])).

tff(c_1360,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1354,c_1359])).

tff(c_1794,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( r2_hidden(k4_tarski(A_221,B_222),k2_zfmisc_1(C_223,D_224))
      | ~ r2_hidden(B_222,D_224)
      | ~ r2_hidden(A_221,C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1353,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1298])).

tff(c_1441,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1353,c_48])).

tff(c_1442,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1354,c_1441])).

tff(c_1800,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1794,c_1442])).

tff(c_1820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_1360,c_1800])).

tff(c_1822,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_44,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1828,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1822,c_44])).

tff(c_2765,plain,(
    ! [A_300,B_301,C_302,D_303] :
      ( r2_hidden(k4_tarski(A_300,B_301),k2_zfmisc_1(C_302,D_303))
      | ~ r2_hidden(B_301,D_303)
      | ~ r2_hidden(A_300,C_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1821,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1091])).

tff(c_42,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2060,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1822,c_1821,c_42])).

tff(c_2771,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2765,c_2060])).

tff(c_2800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_1828,c_2771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.68  
% 3.97/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.68  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.97/1.68  
% 3.97/1.68  %Foreground sorts:
% 3.97/1.68  
% 3.97/1.68  
% 3.97/1.68  %Background operators:
% 3.97/1.68  
% 3.97/1.68  
% 3.97/1.68  %Foreground operators:
% 3.97/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.97/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.97/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.97/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.97/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.97/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.97/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.97/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.97/1.68  
% 4.10/1.70  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.10/1.70  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.10/1.70  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.10/1.70  tff(f_74, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 4.10/1.70  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 4.10/1.70  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 4.10/1.70  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.10/1.70  tff(f_62, axiom, (![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 4.10/1.70  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.10/1.70  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.10/1.70  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.10/1.70  tff(c_2007, plain, (![A_237, B_238]: (r2_hidden(A_237, B_238) | ~r1_tarski(k2_xboole_0(k1_tarski(A_237), B_238), B_238))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.70  tff(c_2131, plain, (![A_271, B_272]: (r2_hidden(A_271, k1_tarski(B_272)) | ~r1_tarski(k2_tarski(A_271, B_272), k1_tarski(B_272)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2007])).
% 4.10/1.70  tff(c_2140, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)) | ~r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2131])).
% 4.10/1.70  tff(c_2142, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2140])).
% 4.10/1.70  tff(c_557, plain, (![A_79, B_80]: (r2_hidden(A_79, B_80) | ~r1_tarski(k2_xboole_0(k1_tarski(A_79), B_80), B_80))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.70  tff(c_682, plain, (![A_113, B_114]: (r2_hidden(A_113, k1_tarski(B_114)) | ~r1_tarski(k2_tarski(A_113, B_114), k1_tarski(B_114)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_557])).
% 4.10/1.70  tff(c_691, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)) | ~r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_682])).
% 4.10/1.70  tff(c_693, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_691])).
% 4.10/1.70  tff(c_46, plain, ('#skF_3'='#skF_1' | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.70  tff(c_97, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_46])).
% 4.10/1.70  tff(c_52, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.70  tff(c_156, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 4.10/1.70  tff(c_334, plain, (![A_60, C_61, B_62, D_63]: (r2_hidden(A_60, C_61) | ~r2_hidden(k4_tarski(A_60, B_62), k2_zfmisc_1(C_61, D_63)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.70  tff(c_338, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_156, c_334])).
% 4.10/1.70  tff(c_121, plain, (![A_38, B_39]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(B_39))=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.10/1.70  tff(c_40, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), B_31)=B_31 | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.10/1.70  tff(c_127, plain, (![A_38, B_39]: (k2_tarski(A_38, B_39)=k1_tarski(B_39) | ~r2_hidden(A_38, k1_tarski(B_39)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_40])).
% 4.10/1.70  tff(c_346, plain, (k2_tarski('#skF_5', '#skF_7')=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_338, c_127])).
% 4.10/1.70  tff(c_376, plain, (![D_64, A_65, C_66, B_67]: (D_64=A_65 | C_66=A_65 | k2_tarski(C_66, D_64)!=k2_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.10/1.70  tff(c_407, plain, (![A_69, A_68, B_70]: (A_69=A_68 | A_69=A_68 | k2_tarski(A_69, B_70)!=k1_tarski(A_68))), inference(superposition, [status(thm), theory('equality')], [c_12, c_376])).
% 4.10/1.70  tff(c_413, plain, (![A_68]: (A_68='#skF_5' | A_68='#skF_5' | k1_tarski(A_68)!=k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_407])).
% 4.10/1.70  tff(c_430, plain, ('#skF_7'='#skF_5' | '#skF_7'='#skF_5'), inference(reflexivity, [status(thm), theory('equality')], [c_413])).
% 4.10/1.70  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_97, c_430])).
% 4.10/1.70  tff(c_434, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 4.10/1.70  tff(c_50, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.70  tff(c_522, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_434, c_50])).
% 4.10/1.70  tff(c_1060, plain, (![A_134, B_135, C_136, D_137]: (r2_hidden(k4_tarski(A_134, B_135), k2_zfmisc_1(C_136, D_137)) | ~r2_hidden(B_135, D_137) | ~r2_hidden(A_134, C_136))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.70  tff(c_433, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 4.10/1.70  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.70  tff(c_658, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_48])).
% 4.10/1.70  tff(c_659, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_434, c_658])).
% 4.10/1.70  tff(c_1069, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_1060, c_659])).
% 4.10/1.70  tff(c_1090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_693, c_522, c_1069])).
% 4.10/1.70  tff(c_1092, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 4.10/1.70  tff(c_1196, plain, (![A_146, B_147]: (r2_hidden(A_146, B_147) | ~r1_tarski(k2_xboole_0(k1_tarski(A_146), B_147), B_147))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.70  tff(c_1464, plain, (![A_198, B_199]: (r2_hidden(A_198, k1_tarski(B_199)) | ~r1_tarski(k2_tarski(A_198, B_199), k1_tarski(B_199)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1196])).
% 4.10/1.70  tff(c_1473, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)) | ~r1_tarski(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1464])).
% 4.10/1.70  tff(c_1475, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1473])).
% 4.10/1.70  tff(c_1091, plain, (~r2_hidden('#skF_6', '#skF_8') | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 4.10/1.70  tff(c_1097, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_1091])).
% 4.10/1.70  tff(c_1298, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_52])).
% 4.10/1.70  tff(c_1299, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_1298])).
% 4.10/1.70  tff(c_1345, plain, (![B_162, D_163, A_164, C_165]: (r2_hidden(B_162, D_163) | ~r2_hidden(k4_tarski(A_164, B_162), k2_zfmisc_1(C_165, D_163)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.70  tff(c_1348, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_1299, c_1345])).
% 4.10/1.70  tff(c_1352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1097, c_1348])).
% 4.10/1.70  tff(c_1354, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitRight, [status(thm)], [c_1298])).
% 4.10/1.70  tff(c_1359, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_50])).
% 4.10/1.70  tff(c_1360, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1354, c_1359])).
% 4.10/1.70  tff(c_1794, plain, (![A_221, B_222, C_223, D_224]: (r2_hidden(k4_tarski(A_221, B_222), k2_zfmisc_1(C_223, D_224)) | ~r2_hidden(B_222, D_224) | ~r2_hidden(A_221, C_223))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.70  tff(c_1353, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1298])).
% 4.10/1.70  tff(c_1441, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1353, c_48])).
% 4.10/1.70  tff(c_1442, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1354, c_1441])).
% 4.10/1.70  tff(c_1800, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_1794, c_1442])).
% 4.10/1.70  tff(c_1820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1475, c_1360, c_1800])).
% 4.10/1.70  tff(c_1822, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_1091])).
% 4.10/1.70  tff(c_44, plain, (r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.70  tff(c_1828, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1822, c_44])).
% 4.10/1.70  tff(c_2765, plain, (![A_300, B_301, C_302, D_303]: (r2_hidden(k4_tarski(A_300, B_301), k2_zfmisc_1(C_302, D_303)) | ~r2_hidden(B_301, D_303) | ~r2_hidden(A_300, C_302))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.70  tff(c_1821, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1091])).
% 4.10/1.70  tff(c_42, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.10/1.70  tff(c_2060, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1822, c_1821, c_42])).
% 4.10/1.70  tff(c_2771, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_2765, c_2060])).
% 4.10/1.70  tff(c_2800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2142, c_1828, c_2771])).
% 4.10/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.70  
% 4.10/1.70  Inference rules
% 4.10/1.70  ----------------------
% 4.10/1.70  #Ref     : 13
% 4.10/1.70  #Sup     : 687
% 4.10/1.70  #Fact    : 0
% 4.10/1.70  #Define  : 0
% 4.10/1.70  #Split   : 4
% 4.10/1.70  #Chain   : 0
% 4.10/1.70  #Close   : 0
% 4.10/1.70  
% 4.10/1.70  Ordering : KBO
% 4.10/1.70  
% 4.10/1.70  Simplification rules
% 4.10/1.70  ----------------------
% 4.10/1.70  #Subsume      : 151
% 4.10/1.70  #Demod        : 192
% 4.10/1.70  #Tautology    : 250
% 4.10/1.70  #SimpNegUnit  : 6
% 4.10/1.70  #BackRed      : 0
% 4.10/1.70  
% 4.10/1.70  #Partial instantiations: 0
% 4.10/1.70  #Strategies tried      : 1
% 4.10/1.70  
% 4.10/1.70  Timing (in seconds)
% 4.10/1.70  ----------------------
% 4.10/1.70  Preprocessing        : 0.31
% 4.10/1.70  Parsing              : 0.17
% 4.10/1.70  CNF conversion       : 0.02
% 4.10/1.70  Main loop            : 0.60
% 4.10/1.70  Inferencing          : 0.21
% 4.10/1.70  Reduction            : 0.21
% 4.10/1.70  Demodulation         : 0.17
% 4.10/1.70  BG Simplification    : 0.03
% 4.10/1.70  Subsumption          : 0.11
% 4.10/1.70  Abstraction          : 0.03
% 4.10/1.70  MUC search           : 0.00
% 4.10/1.70  Cooper               : 0.00
% 4.10/1.70  Total                : 0.95
% 4.10/1.70  Index Insertion      : 0.00
% 4.10/1.70  Index Deletion       : 0.00
% 4.10/1.70  Index Matching       : 0.00
% 4.10/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
