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
% DateTime   : Thu Dec  3 09:53:39 EST 2020

% Result     : Theorem 10.21s
% Output     : CNFRefutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 433 expanded)
%              Number of leaves         :   18 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          :  181 (1390 expanded)
%              Number of equality atoms :   59 ( 425 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ! [E,F] :
            ( r2_hidden(k4_tarski(E,F),k2_zfmisc_1(A,B))
          <=> r2_hidden(k4_tarski(E,F),k2_zfmisc_1(C,D)) )
       => k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_zfmisc_1)).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_64,B_65,D_66] :
      ( k4_tarski('#skF_5'(A_64,B_65,k2_zfmisc_1(A_64,B_65),D_66),'#skF_6'(A_64,B_65,k2_zfmisc_1(A_64,B_65),D_66)) = D_66
      | ~ r2_hidden(D_66,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [E_37,F_38] :
      ( r2_hidden(k4_tarski(E_37,F_38),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_37,F_38),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_181,plain,(
    ! [D_112,A_113,B_114] :
      ( r2_hidden(D_112,k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(k4_tarski('#skF_5'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_112),'#skF_6'(A_113,B_114,k2_zfmisc_1(A_113,B_114),D_112)),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(D_112,k2_zfmisc_1(A_113,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_30])).

tff(c_582,plain,(
    ! [D_153,A_154,B_155] :
      ( r2_hidden(D_153,k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(D_153,k2_zfmisc_1(A_154,B_155))
      | ~ r2_hidden('#skF_6'(A_154,B_155,k2_zfmisc_1(A_154,B_155),D_153),'#skF_10')
      | ~ r2_hidden('#skF_5'(A_154,B_155,k2_zfmisc_1(A_154,B_155),D_153),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2,c_181])).

tff(c_588,plain,(
    ! [D_156,A_157] :
      ( r2_hidden(D_156,k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden('#skF_5'(A_157,'#skF_10',k2_zfmisc_1(A_157,'#skF_10'),D_156),'#skF_9')
      | ~ r2_hidden(D_156,k2_zfmisc_1(A_157,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_6,c_582])).

tff(c_593,plain,(
    ! [D_28] :
      ( r2_hidden(D_28,k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(D_28,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_8,c_588])).

tff(c_4,plain,(
    ! [A_1,B_2,D_28] :
      ( k4_tarski('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),'#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28)) = D_28
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_4'(A_1,B_2,C_3),C_3)
      | k2_zfmisc_1(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [E_80,F_81,B_82,C_83,A_84] :
      ( r2_hidden('#skF_2'(A_84,B_82,C_83),A_84)
      | k4_tarski(E_80,F_81) != '#skF_4'(A_84,B_82,C_83)
      | ~ r2_hidden(F_81,B_82)
      | ~ r2_hidden(E_80,A_84)
      | k2_zfmisc_1(A_84,B_82) = C_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [B_2,A_1,B_82,C_83,A_84,D_28] :
      ( r2_hidden('#skF_2'(A_84,B_82,C_83),A_84)
      | D_28 != '#skF_4'(A_84,B_82,C_83)
      | ~ r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_82)
      | ~ r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_84)
      | k2_zfmisc_1(A_84,B_82) = C_83
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_97])).

tff(c_1772,plain,(
    ! [B_315,C_312,A_314,A_311,B_313] :
      ( r2_hidden('#skF_2'(A_311,B_315,C_312),A_311)
      | ~ r2_hidden('#skF_6'(A_314,B_313,k2_zfmisc_1(A_314,B_313),'#skF_4'(A_311,B_315,C_312)),B_315)
      | ~ r2_hidden('#skF_5'(A_314,B_313,k2_zfmisc_1(A_314,B_313),'#skF_4'(A_311,B_315,C_312)),A_311)
      | k2_zfmisc_1(A_311,B_315) = C_312
      | ~ r2_hidden('#skF_4'(A_311,B_315,C_312),k2_zfmisc_1(A_314,B_313)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_101])).

tff(c_3145,plain,(
    ! [A_363,B_364,C_365,A_366] :
      ( r2_hidden('#skF_2'(A_363,B_364,C_365),A_363)
      | ~ r2_hidden('#skF_5'(A_366,B_364,k2_zfmisc_1(A_366,B_364),'#skF_4'(A_363,B_364,C_365)),A_363)
      | k2_zfmisc_1(A_363,B_364) = C_365
      | ~ r2_hidden('#skF_4'(A_363,B_364,C_365),k2_zfmisc_1(A_366,B_364)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1772])).

tff(c_3246,plain,(
    ! [A_367,B_368,C_369] :
      ( r2_hidden('#skF_2'(A_367,B_368,C_369),A_367)
      | k2_zfmisc_1(A_367,B_368) = C_369
      | ~ r2_hidden('#skF_4'(A_367,B_368,C_369),k2_zfmisc_1(A_367,B_368)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3145])).

tff(c_3687,plain,(
    ! [C_377] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_8',C_377),'#skF_7')
      | k2_zfmisc_1('#skF_7','#skF_8') = C_377
      | ~ r2_hidden('#skF_4'('#skF_7','#skF_8',C_377),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_593,c_3246])).

tff(c_3725,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_7')
    | k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_24,c_3687])).

tff(c_3745,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_3725])).

tff(c_22,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_3'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_4'(A_1,B_2,C_3),C_3)
      | k2_zfmisc_1(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [B_77,C_78,F_76,E_75,A_79] :
      ( r2_hidden('#skF_3'(A_79,B_77,C_78),B_77)
      | k4_tarski(E_75,F_76) != '#skF_4'(A_79,B_77,C_78)
      | ~ r2_hidden(F_76,B_77)
      | ~ r2_hidden(E_75,A_79)
      | k2_zfmisc_1(A_79,B_77) = C_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [B_77,C_78,B_2,A_1,D_28,A_79] :
      ( r2_hidden('#skF_3'(A_79,B_77,C_78),B_77)
      | D_28 != '#skF_4'(A_79,B_77,C_78)
      | ~ r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_77)
      | ~ r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_79)
      | k2_zfmisc_1(A_79,B_77) = C_78
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_2289,plain,(
    ! [C_334,B_330,A_331,A_333,B_332] :
      ( r2_hidden('#skF_3'(A_331,B_330,C_334),B_330)
      | ~ r2_hidden('#skF_6'(A_333,B_332,k2_zfmisc_1(A_333,B_332),'#skF_4'(A_331,B_330,C_334)),B_330)
      | ~ r2_hidden('#skF_5'(A_333,B_332,k2_zfmisc_1(A_333,B_332),'#skF_4'(A_331,B_330,C_334)),A_331)
      | k2_zfmisc_1(A_331,B_330) = C_334
      | ~ r2_hidden('#skF_4'(A_331,B_330,C_334),k2_zfmisc_1(A_333,B_332)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_96])).

tff(c_3416,plain,(
    ! [A_370,B_371,C_372,A_373] :
      ( r2_hidden('#skF_3'(A_370,B_371,C_372),B_371)
      | ~ r2_hidden('#skF_5'(A_373,B_371,k2_zfmisc_1(A_373,B_371),'#skF_4'(A_370,B_371,C_372)),A_370)
      | k2_zfmisc_1(A_370,B_371) = C_372
      | ~ r2_hidden('#skF_4'(A_370,B_371,C_372),k2_zfmisc_1(A_373,B_371)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2289])).

tff(c_3517,plain,(
    ! [A_374,B_375,C_376] :
      ( r2_hidden('#skF_3'(A_374,B_375,C_376),B_375)
      | k2_zfmisc_1(A_374,B_375) = C_376
      | ~ r2_hidden('#skF_4'(A_374,B_375,C_376),k2_zfmisc_1(A_374,B_375)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3416])).

tff(c_3747,plain,(
    ! [C_378] :
      ( r2_hidden('#skF_3'('#skF_7','#skF_8',C_378),'#skF_8')
      | k2_zfmisc_1('#skF_7','#skF_8') = C_378
      | ~ r2_hidden('#skF_4'('#skF_7','#skF_8',C_378),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_593,c_3517])).

tff(c_3781,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_8')
    | k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_3747])).

tff(c_3803,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_3781])).

tff(c_71,plain,(
    ! [A_72,B_73,C_74] :
      ( k4_tarski('#skF_2'(A_72,B_73,C_74),'#skF_3'(A_72,B_73,C_74)) = '#skF_1'(A_72,B_73,C_74)
      | r2_hidden('#skF_4'(A_72,B_73,C_74),C_74)
      | k2_zfmisc_1(A_72,B_73) = C_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [E_43,F_44] :
      ( r2_hidden(k4_tarski(E_43,F_44),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(k4_tarski(E_43,F_44),k2_zfmisc_1('#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ! [E_33,F_34] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(F_34,'#skF_8')
      | ~ r2_hidden(E_33,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_804,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden('#skF_1'(A_191,B_192,C_193),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_3'(A_191,B_192,C_193),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_191,B_192,C_193),'#skF_7')
      | r2_hidden('#skF_4'(A_191,B_192,C_193),C_193)
      | k2_zfmisc_1(A_191,B_192) = C_193 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_37])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_4'(A_1,B_2,C_3),C_3)
      | k2_zfmisc_1(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_832,plain,(
    ! [A_191,B_192] :
      ( ~ r2_hidden('#skF_3'(A_191,B_192,k2_zfmisc_1('#skF_9','#skF_10')),'#skF_8')
      | ~ r2_hidden('#skF_2'(A_191,B_192,k2_zfmisc_1('#skF_9','#skF_10')),'#skF_7')
      | r2_hidden('#skF_4'(A_191,B_192,k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10'))
      | k2_zfmisc_1(A_191,B_192) = k2_zfmisc_1('#skF_9','#skF_10') ) ),
    inference(resolution,[status(thm)],[c_804,c_18])).

tff(c_102,plain,(
    ! [B_87,F_86,E_85,A_89,C_88] :
      ( k4_tarski('#skF_2'(A_89,B_87,C_88),'#skF_3'(A_89,B_87,C_88)) = '#skF_1'(A_89,B_87,C_88)
      | k4_tarski(E_85,F_86) != '#skF_4'(A_89,B_87,C_88)
      | ~ r2_hidden(F_86,B_87)
      | ~ r2_hidden(E_85,A_89)
      | k2_zfmisc_1(A_89,B_87) = C_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [B_87,B_2,A_1,A_89,D_28,C_88] :
      ( k4_tarski('#skF_2'(A_89,B_87,C_88),'#skF_3'(A_89,B_87,C_88)) = '#skF_1'(A_89,B_87,C_88)
      | D_28 != '#skF_4'(A_89,B_87,C_88)
      | ~ r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_87)
      | ~ r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_89)
      | k2_zfmisc_1(A_89,B_87) = C_88
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_3045,plain,(
    ! [C_357,A_358,B_356,B_359,A_360] :
      ( k4_tarski('#skF_2'(A_358,B_356,C_357),'#skF_3'(A_358,B_356,C_357)) = '#skF_1'(A_358,B_356,C_357)
      | ~ r2_hidden('#skF_6'(A_360,B_359,k2_zfmisc_1(A_360,B_359),'#skF_4'(A_358,B_356,C_357)),B_356)
      | ~ r2_hidden('#skF_5'(A_360,B_359,k2_zfmisc_1(A_360,B_359),'#skF_4'(A_358,B_356,C_357)),A_358)
      | k2_zfmisc_1(A_358,B_356) = C_357
      | ~ r2_hidden('#skF_4'(A_358,B_356,C_357),k2_zfmisc_1(A_360,B_359)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_106])).

tff(c_3809,plain,(
    ! [A_379,B_380,C_381,A_382] :
      ( k4_tarski('#skF_2'(A_379,B_380,C_381),'#skF_3'(A_379,B_380,C_381)) = '#skF_1'(A_379,B_380,C_381)
      | ~ r2_hidden('#skF_5'(A_382,B_380,k2_zfmisc_1(A_382,B_380),'#skF_4'(A_379,B_380,C_381)),A_379)
      | k2_zfmisc_1(A_379,B_380) = C_381
      | ~ r2_hidden('#skF_4'(A_379,B_380,C_381),k2_zfmisc_1(A_382,B_380)) ) ),
    inference(resolution,[status(thm)],[c_6,c_3045])).

tff(c_3892,plain,(
    ! [A_383,B_384,C_385] :
      ( k4_tarski('#skF_2'(A_383,B_384,C_385),'#skF_3'(A_383,B_384,C_385)) = '#skF_1'(A_383,B_384,C_385)
      | k2_zfmisc_1(A_383,B_384) = C_385
      | ~ r2_hidden('#skF_4'(A_383,B_384,C_385),k2_zfmisc_1(A_383,B_384)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3809])).

tff(c_4116,plain,(
    ! [C_386] :
      ( k4_tarski('#skF_2'('#skF_7','#skF_8',C_386),'#skF_3'('#skF_7','#skF_8',C_386)) = '#skF_1'('#skF_7','#skF_8',C_386)
      | k2_zfmisc_1('#skF_7','#skF_8') = C_386
      | ~ r2_hidden('#skF_4'('#skF_7','#skF_8',C_386),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_593,c_3892])).

tff(c_4128,plain,
    ( k4_tarski('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))) = '#skF_1'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_8')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_7')
    | k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_832,c_4116])).

tff(c_4153,plain,
    ( k4_tarski('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))) = '#skF_1'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
    | k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3745,c_3803,c_4128])).

tff(c_4154,plain,(
    k4_tarski('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))) = '#skF_1'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4153])).

tff(c_4233,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10'))
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_8')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4154,c_37])).

tff(c_4247,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3745,c_3803,c_4233])).

tff(c_10,plain,(
    ! [E_26,F_27,B_2,C_3,A_1] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | k4_tarski(E_26,F_27) != '#skF_4'(A_1,B_2,C_3)
      | ~ r2_hidden(F_27,B_2)
      | ~ r2_hidden(E_26,A_1)
      | k2_zfmisc_1(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4252,plain,(
    ! [E_26,F_27] :
      ( k4_tarski(E_26,F_27) != '#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(F_27,'#skF_8')
      | ~ r2_hidden(E_26,'#skF_7')
      | k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4247,c_10])).

tff(c_4279,plain,(
    ! [E_387,F_388] :
      ( k4_tarski(E_387,F_388) != '#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(F_388,'#skF_8')
      | ~ r2_hidden(E_387,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4252])).

tff(c_5143,plain,(
    ! [D_416,A_417,B_418] :
      ( D_416 != '#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_6'(A_417,B_418,k2_zfmisc_1(A_417,B_418),D_416),'#skF_8')
      | ~ r2_hidden('#skF_5'(A_417,B_418,k2_zfmisc_1(A_417,B_418),D_416),'#skF_7')
      | ~ r2_hidden(D_416,k2_zfmisc_1(A_417,B_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4279])).

tff(c_5150,plain,(
    ! [D_419,A_420] :
      ( D_419 != '#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_5'(A_420,'#skF_8',k2_zfmisc_1(A_420,'#skF_8'),D_419),'#skF_7')
      | ~ r2_hidden(D_419,k2_zfmisc_1(A_420,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_6,c_5143])).

tff(c_5157,plain,(
    ! [D_421] :
      ( D_421 != '#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(D_421,k2_zfmisc_1('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_8,c_5150])).

tff(c_5274,plain,(
    ~ r2_hidden('#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_593,c_5157])).

tff(c_4255,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10'))
    | k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_4247,c_18])).

tff(c_4261,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8',k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4255])).

tff(c_5276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5274,c_4261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.21/3.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/3.67  
% 10.54/3.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/3.68  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 10.54/3.68  
% 10.54/3.68  %Foreground sorts:
% 10.54/3.68  
% 10.54/3.68  
% 10.54/3.68  %Background operators:
% 10.54/3.68  
% 10.54/3.68  
% 10.54/3.68  %Foreground operators:
% 10.54/3.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.54/3.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.54/3.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.54/3.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.54/3.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.54/3.68  tff('#skF_7', type, '#skF_7': $i).
% 10.54/3.68  tff('#skF_10', type, '#skF_10': $i).
% 10.54/3.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.54/3.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 10.54/3.68  tff('#skF_9', type, '#skF_9': $i).
% 10.54/3.68  tff('#skF_8', type, '#skF_8': $i).
% 10.54/3.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.54/3.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 10.54/3.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.54/3.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.54/3.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.54/3.68  
% 10.59/3.71  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 10.59/3.71  tff(f_45, negated_conjecture, ~(![A, B, C, D]: ((![E, F]: (r2_hidden(k4_tarski(E, F), k2_zfmisc_1(A, B)) <=> r2_hidden(k4_tarski(E, F), k2_zfmisc_1(C, D)))) => (k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_zfmisc_1)).
% 10.59/3.71  tff(c_8, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_1) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_6, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_2) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_2, plain, (![E_33, F_34, A_1, B_2]: (r2_hidden(k4_tarski(E_33, F_34), k2_zfmisc_1(A_1, B_2)) | ~r2_hidden(F_34, B_2) | ~r2_hidden(E_33, A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_49, plain, (![A_64, B_65, D_66]: (k4_tarski('#skF_5'(A_64, B_65, k2_zfmisc_1(A_64, B_65), D_66), '#skF_6'(A_64, B_65, k2_zfmisc_1(A_64, B_65), D_66))=D_66 | ~r2_hidden(D_66, k2_zfmisc_1(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_30, plain, (![E_37, F_38]: (r2_hidden(k4_tarski(E_37, F_38), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(k4_tarski(E_37, F_38), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.59/3.71  tff(c_181, plain, (![D_112, A_113, B_114]: (r2_hidden(D_112, k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(k4_tarski('#skF_5'(A_113, B_114, k2_zfmisc_1(A_113, B_114), D_112), '#skF_6'(A_113, B_114, k2_zfmisc_1(A_113, B_114), D_112)), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(D_112, k2_zfmisc_1(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_30])).
% 10.59/3.71  tff(c_582, plain, (![D_153, A_154, B_155]: (r2_hidden(D_153, k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(D_153, k2_zfmisc_1(A_154, B_155)) | ~r2_hidden('#skF_6'(A_154, B_155, k2_zfmisc_1(A_154, B_155), D_153), '#skF_10') | ~r2_hidden('#skF_5'(A_154, B_155, k2_zfmisc_1(A_154, B_155), D_153), '#skF_9'))), inference(resolution, [status(thm)], [c_2, c_181])).
% 10.59/3.71  tff(c_588, plain, (![D_156, A_157]: (r2_hidden(D_156, k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden('#skF_5'(A_157, '#skF_10', k2_zfmisc_1(A_157, '#skF_10'), D_156), '#skF_9') | ~r2_hidden(D_156, k2_zfmisc_1(A_157, '#skF_10')))), inference(resolution, [status(thm)], [c_6, c_582])).
% 10.59/3.71  tff(c_593, plain, (![D_28]: (r2_hidden(D_28, k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(D_28, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_8, c_588])).
% 10.59/3.71  tff(c_4, plain, (![A_1, B_2, D_28]: (k4_tarski('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), '#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28))=D_28 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_26, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.59/3.71  tff(c_24, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_4'(A_1, B_2, C_3), C_3) | k2_zfmisc_1(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_97, plain, (![E_80, F_81, B_82, C_83, A_84]: (r2_hidden('#skF_2'(A_84, B_82, C_83), A_84) | k4_tarski(E_80, F_81)!='#skF_4'(A_84, B_82, C_83) | ~r2_hidden(F_81, B_82) | ~r2_hidden(E_80, A_84) | k2_zfmisc_1(A_84, B_82)=C_83)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_101, plain, (![B_2, A_1, B_82, C_83, A_84, D_28]: (r2_hidden('#skF_2'(A_84, B_82, C_83), A_84) | D_28!='#skF_4'(A_84, B_82, C_83) | ~r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_82) | ~r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_84) | k2_zfmisc_1(A_84, B_82)=C_83 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_97])).
% 10.59/3.71  tff(c_1772, plain, (![B_315, C_312, A_314, A_311, B_313]: (r2_hidden('#skF_2'(A_311, B_315, C_312), A_311) | ~r2_hidden('#skF_6'(A_314, B_313, k2_zfmisc_1(A_314, B_313), '#skF_4'(A_311, B_315, C_312)), B_315) | ~r2_hidden('#skF_5'(A_314, B_313, k2_zfmisc_1(A_314, B_313), '#skF_4'(A_311, B_315, C_312)), A_311) | k2_zfmisc_1(A_311, B_315)=C_312 | ~r2_hidden('#skF_4'(A_311, B_315, C_312), k2_zfmisc_1(A_314, B_313)))), inference(reflexivity, [status(thm), theory('equality')], [c_101])).
% 10.59/3.71  tff(c_3145, plain, (![A_363, B_364, C_365, A_366]: (r2_hidden('#skF_2'(A_363, B_364, C_365), A_363) | ~r2_hidden('#skF_5'(A_366, B_364, k2_zfmisc_1(A_366, B_364), '#skF_4'(A_363, B_364, C_365)), A_363) | k2_zfmisc_1(A_363, B_364)=C_365 | ~r2_hidden('#skF_4'(A_363, B_364, C_365), k2_zfmisc_1(A_366, B_364)))), inference(resolution, [status(thm)], [c_6, c_1772])).
% 10.59/3.71  tff(c_3246, plain, (![A_367, B_368, C_369]: (r2_hidden('#skF_2'(A_367, B_368, C_369), A_367) | k2_zfmisc_1(A_367, B_368)=C_369 | ~r2_hidden('#skF_4'(A_367, B_368, C_369), k2_zfmisc_1(A_367, B_368)))), inference(resolution, [status(thm)], [c_8, c_3145])).
% 10.59/3.71  tff(c_3687, plain, (![C_377]: (r2_hidden('#skF_2'('#skF_7', '#skF_8', C_377), '#skF_7') | k2_zfmisc_1('#skF_7', '#skF_8')=C_377 | ~r2_hidden('#skF_4'('#skF_7', '#skF_8', C_377), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_593, c_3246])).
% 10.59/3.71  tff(c_3725, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_7') | k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_24, c_3687])).
% 10.59/3.71  tff(c_3745, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_3725])).
% 10.59/3.71  tff(c_22, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_3'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_4'(A_1, B_2, C_3), C_3) | k2_zfmisc_1(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_92, plain, (![B_77, C_78, F_76, E_75, A_79]: (r2_hidden('#skF_3'(A_79, B_77, C_78), B_77) | k4_tarski(E_75, F_76)!='#skF_4'(A_79, B_77, C_78) | ~r2_hidden(F_76, B_77) | ~r2_hidden(E_75, A_79) | k2_zfmisc_1(A_79, B_77)=C_78)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_96, plain, (![B_77, C_78, B_2, A_1, D_28, A_79]: (r2_hidden('#skF_3'(A_79, B_77, C_78), B_77) | D_28!='#skF_4'(A_79, B_77, C_78) | ~r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_77) | ~r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_79) | k2_zfmisc_1(A_79, B_77)=C_78 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 10.59/3.71  tff(c_2289, plain, (![C_334, B_330, A_331, A_333, B_332]: (r2_hidden('#skF_3'(A_331, B_330, C_334), B_330) | ~r2_hidden('#skF_6'(A_333, B_332, k2_zfmisc_1(A_333, B_332), '#skF_4'(A_331, B_330, C_334)), B_330) | ~r2_hidden('#skF_5'(A_333, B_332, k2_zfmisc_1(A_333, B_332), '#skF_4'(A_331, B_330, C_334)), A_331) | k2_zfmisc_1(A_331, B_330)=C_334 | ~r2_hidden('#skF_4'(A_331, B_330, C_334), k2_zfmisc_1(A_333, B_332)))), inference(reflexivity, [status(thm), theory('equality')], [c_96])).
% 10.59/3.71  tff(c_3416, plain, (![A_370, B_371, C_372, A_373]: (r2_hidden('#skF_3'(A_370, B_371, C_372), B_371) | ~r2_hidden('#skF_5'(A_373, B_371, k2_zfmisc_1(A_373, B_371), '#skF_4'(A_370, B_371, C_372)), A_370) | k2_zfmisc_1(A_370, B_371)=C_372 | ~r2_hidden('#skF_4'(A_370, B_371, C_372), k2_zfmisc_1(A_373, B_371)))), inference(resolution, [status(thm)], [c_6, c_2289])).
% 10.59/3.71  tff(c_3517, plain, (![A_374, B_375, C_376]: (r2_hidden('#skF_3'(A_374, B_375, C_376), B_375) | k2_zfmisc_1(A_374, B_375)=C_376 | ~r2_hidden('#skF_4'(A_374, B_375, C_376), k2_zfmisc_1(A_374, B_375)))), inference(resolution, [status(thm)], [c_8, c_3416])).
% 10.59/3.71  tff(c_3747, plain, (![C_378]: (r2_hidden('#skF_3'('#skF_7', '#skF_8', C_378), '#skF_8') | k2_zfmisc_1('#skF_7', '#skF_8')=C_378 | ~r2_hidden('#skF_4'('#skF_7', '#skF_8', C_378), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_593, c_3517])).
% 10.59/3.71  tff(c_3781, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_8') | k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_22, c_3747])).
% 10.59/3.71  tff(c_3803, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_3781])).
% 10.59/3.71  tff(c_71, plain, (![A_72, B_73, C_74]: (k4_tarski('#skF_2'(A_72, B_73, C_74), '#skF_3'(A_72, B_73, C_74))='#skF_1'(A_72, B_73, C_74) | r2_hidden('#skF_4'(A_72, B_73, C_74), C_74) | k2_zfmisc_1(A_72, B_73)=C_74)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_32, plain, (![E_43, F_44]: (r2_hidden(k4_tarski(E_43, F_44), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(k4_tarski(E_43, F_44), k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.59/3.71  tff(c_37, plain, (![E_33, F_34]: (r2_hidden(k4_tarski(E_33, F_34), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(F_34, '#skF_8') | ~r2_hidden(E_33, '#skF_7'))), inference(resolution, [status(thm)], [c_2, c_32])).
% 10.59/3.71  tff(c_804, plain, (![A_191, B_192, C_193]: (r2_hidden('#skF_1'(A_191, B_192, C_193), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden('#skF_3'(A_191, B_192, C_193), '#skF_8') | ~r2_hidden('#skF_2'(A_191, B_192, C_193), '#skF_7') | r2_hidden('#skF_4'(A_191, B_192, C_193), C_193) | k2_zfmisc_1(A_191, B_192)=C_193)), inference(superposition, [status(thm), theory('equality')], [c_71, c_37])).
% 10.59/3.71  tff(c_18, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_4'(A_1, B_2, C_3), C_3) | k2_zfmisc_1(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_832, plain, (![A_191, B_192]: (~r2_hidden('#skF_3'(A_191, B_192, k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_8') | ~r2_hidden('#skF_2'(A_191, B_192, k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_7') | r2_hidden('#skF_4'(A_191, B_192, k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10')) | k2_zfmisc_1(A_191, B_192)=k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_804, c_18])).
% 10.59/3.71  tff(c_102, plain, (![B_87, F_86, E_85, A_89, C_88]: (k4_tarski('#skF_2'(A_89, B_87, C_88), '#skF_3'(A_89, B_87, C_88))='#skF_1'(A_89, B_87, C_88) | k4_tarski(E_85, F_86)!='#skF_4'(A_89, B_87, C_88) | ~r2_hidden(F_86, B_87) | ~r2_hidden(E_85, A_89) | k2_zfmisc_1(A_89, B_87)=C_88)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_106, plain, (![B_87, B_2, A_1, A_89, D_28, C_88]: (k4_tarski('#skF_2'(A_89, B_87, C_88), '#skF_3'(A_89, B_87, C_88))='#skF_1'(A_89, B_87, C_88) | D_28!='#skF_4'(A_89, B_87, C_88) | ~r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_87) | ~r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_89) | k2_zfmisc_1(A_89, B_87)=C_88 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_102])).
% 10.59/3.71  tff(c_3045, plain, (![C_357, A_358, B_356, B_359, A_360]: (k4_tarski('#skF_2'(A_358, B_356, C_357), '#skF_3'(A_358, B_356, C_357))='#skF_1'(A_358, B_356, C_357) | ~r2_hidden('#skF_6'(A_360, B_359, k2_zfmisc_1(A_360, B_359), '#skF_4'(A_358, B_356, C_357)), B_356) | ~r2_hidden('#skF_5'(A_360, B_359, k2_zfmisc_1(A_360, B_359), '#skF_4'(A_358, B_356, C_357)), A_358) | k2_zfmisc_1(A_358, B_356)=C_357 | ~r2_hidden('#skF_4'(A_358, B_356, C_357), k2_zfmisc_1(A_360, B_359)))), inference(reflexivity, [status(thm), theory('equality')], [c_106])).
% 10.59/3.71  tff(c_3809, plain, (![A_379, B_380, C_381, A_382]: (k4_tarski('#skF_2'(A_379, B_380, C_381), '#skF_3'(A_379, B_380, C_381))='#skF_1'(A_379, B_380, C_381) | ~r2_hidden('#skF_5'(A_382, B_380, k2_zfmisc_1(A_382, B_380), '#skF_4'(A_379, B_380, C_381)), A_379) | k2_zfmisc_1(A_379, B_380)=C_381 | ~r2_hidden('#skF_4'(A_379, B_380, C_381), k2_zfmisc_1(A_382, B_380)))), inference(resolution, [status(thm)], [c_6, c_3045])).
% 10.59/3.71  tff(c_3892, plain, (![A_383, B_384, C_385]: (k4_tarski('#skF_2'(A_383, B_384, C_385), '#skF_3'(A_383, B_384, C_385))='#skF_1'(A_383, B_384, C_385) | k2_zfmisc_1(A_383, B_384)=C_385 | ~r2_hidden('#skF_4'(A_383, B_384, C_385), k2_zfmisc_1(A_383, B_384)))), inference(resolution, [status(thm)], [c_8, c_3809])).
% 10.59/3.71  tff(c_4116, plain, (![C_386]: (k4_tarski('#skF_2'('#skF_7', '#skF_8', C_386), '#skF_3'('#skF_7', '#skF_8', C_386))='#skF_1'('#skF_7', '#skF_8', C_386) | k2_zfmisc_1('#skF_7', '#skF_8')=C_386 | ~r2_hidden('#skF_4'('#skF_7', '#skF_8', C_386), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_593, c_3892])).
% 10.59/3.71  tff(c_4128, plain, (k4_tarski('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')))='#skF_1'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden('#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_8') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_7') | k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_832, c_4116])).
% 10.59/3.71  tff(c_4153, plain, (k4_tarski('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')))='#skF_1'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3745, c_3803, c_4128])).
% 10.59/3.71  tff(c_4154, plain, (k4_tarski('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')))='#skF_1'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_26, c_4153])).
% 10.59/3.71  tff(c_4233, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden('#skF_3'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_8') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4154, c_37])).
% 10.59/3.71  tff(c_4247, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3745, c_3803, c_4233])).
% 10.59/3.71  tff(c_10, plain, (![E_26, F_27, B_2, C_3, A_1]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | k4_tarski(E_26, F_27)!='#skF_4'(A_1, B_2, C_3) | ~r2_hidden(F_27, B_2) | ~r2_hidden(E_26, A_1) | k2_zfmisc_1(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.59/3.71  tff(c_4252, plain, (![E_26, F_27]: (k4_tarski(E_26, F_27)!='#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(F_27, '#skF_8') | ~r2_hidden(E_26, '#skF_7') | k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_4247, c_10])).
% 10.59/3.71  tff(c_4279, plain, (![E_387, F_388]: (k4_tarski(E_387, F_388)!='#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(F_388, '#skF_8') | ~r2_hidden(E_387, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_26, c_4252])).
% 10.59/3.71  tff(c_5143, plain, (![D_416, A_417, B_418]: (D_416!='#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden('#skF_6'(A_417, B_418, k2_zfmisc_1(A_417, B_418), D_416), '#skF_8') | ~r2_hidden('#skF_5'(A_417, B_418, k2_zfmisc_1(A_417, B_418), D_416), '#skF_7') | ~r2_hidden(D_416, k2_zfmisc_1(A_417, B_418)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4279])).
% 10.59/3.71  tff(c_5150, plain, (![D_419, A_420]: (D_419!='#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden('#skF_5'(A_420, '#skF_8', k2_zfmisc_1(A_420, '#skF_8'), D_419), '#skF_7') | ~r2_hidden(D_419, k2_zfmisc_1(A_420, '#skF_8')))), inference(resolution, [status(thm)], [c_6, c_5143])).
% 10.59/3.71  tff(c_5157, plain, (![D_421]: (D_421!='#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(D_421, k2_zfmisc_1('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_8, c_5150])).
% 10.59/3.71  tff(c_5274, plain, (~r2_hidden('#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_593, c_5157])).
% 10.59/3.71  tff(c_4255, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10')) | k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_4247, c_18])).
% 10.59/3.71  tff(c_4261, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_26, c_4255])).
% 10.59/3.71  tff(c_5276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5274, c_4261])).
% 10.59/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/3.71  
% 10.59/3.71  Inference rules
% 10.59/3.71  ----------------------
% 10.59/3.71  #Ref     : 3
% 10.59/3.71  #Sup     : 1092
% 10.59/3.71  #Fact    : 0
% 10.59/3.71  #Define  : 0
% 10.59/3.71  #Split   : 5
% 10.59/3.71  #Chain   : 0
% 10.59/3.71  #Close   : 0
% 10.59/3.71  
% 10.59/3.71  Ordering : KBO
% 10.59/3.71  
% 10.59/3.71  Simplification rules
% 10.59/3.71  ----------------------
% 10.59/3.71  #Subsume      : 158
% 10.59/3.71  #Demod        : 38
% 10.72/3.71  #Tautology    : 104
% 10.72/3.71  #SimpNegUnit  : 46
% 10.72/3.71  #BackRed      : 1
% 10.72/3.71  
% 10.72/3.71  #Partial instantiations: 0
% 10.72/3.71  #Strategies tried      : 1
% 10.72/3.71  
% 10.72/3.71  Timing (in seconds)
% 10.72/3.71  ----------------------
% 10.72/3.71  Preprocessing        : 0.43
% 10.72/3.71  Parsing              : 0.20
% 10.72/3.71  CNF conversion       : 0.04
% 10.72/3.71  Main loop            : 2.27
% 10.72/3.71  Inferencing          : 0.92
% 10.72/3.71  Reduction            : 0.41
% 10.72/3.71  Demodulation         : 0.19
% 10.72/3.71  BG Simplification    : 0.10
% 10.72/3.71  Subsumption          : 0.68
% 10.72/3.71  Abstraction          : 0.13
% 10.72/3.71  MUC search           : 0.00
% 10.72/3.71  Cooper               : 0.00
% 10.72/3.72  Total                : 2.76
% 10.72/3.72  Index Insertion      : 0.00
% 10.72/3.72  Index Deletion       : 0.00
% 10.72/3.72  Index Matching       : 0.00
% 10.72/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
