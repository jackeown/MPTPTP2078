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
% DateTime   : Thu Dec  3 09:53:56 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 281 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 696 expanded)
%              Number of equality atoms :   20 ( 112 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_34,plain,
    ( r1_xboole_0('#skF_10','#skF_11')
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_184,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden('#skF_4'(A_91,B_92,C_93),B_92)
      | r2_hidden('#skF_5'(A_91,B_92,C_93),C_93)
      | k2_zfmisc_1(A_91,B_92) = C_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1499,plain,(
    ! [A_281,B_282,A_283,C_284] :
      ( ~ r1_xboole_0(A_281,B_282)
      | r2_hidden('#skF_5'(A_283,k3_xboole_0(A_281,B_282),C_284),C_284)
      | k2_zfmisc_1(A_283,k3_xboole_0(A_281,B_282)) = C_284 ) ),
    inference(resolution,[status(thm)],[c_184,c_4])).

tff(c_1664,plain,(
    ! [A_285,A_289,A_288,B_286,B_287] :
      ( ~ r1_xboole_0(A_289,B_287)
      | ~ r1_xboole_0(A_285,B_286)
      | k3_xboole_0(A_289,B_287) = k2_zfmisc_1(A_288,k3_xboole_0(A_285,B_286)) ) ),
    inference(resolution,[status(thm)],[c_1499,c_4])).

tff(c_1668,plain,(
    ! [A_290,B_291,A_292] :
      ( ~ r1_xboole_0(A_290,B_291)
      | k2_zfmisc_1(A_292,k3_xboole_0(A_290,B_291)) = k3_xboole_0('#skF_8','#skF_9') ) ),
    inference(resolution,[status(thm)],[c_35,c_1664])).

tff(c_12,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),A_6)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_64,B_65,D_66] :
      ( r2_hidden('#skF_6'(A_64,B_65,k2_zfmisc_1(A_64,B_65),D_66),A_64)
      | ~ r2_hidden(D_66,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_89,plain,(
    ! [A_67,B_68,D_69,B_70] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(D_69,k2_zfmisc_1(k3_xboole_0(A_67,B_68),B_70)) ) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_165,plain,(
    ! [B_87,A_88,B_89,B_86,D_90] :
      ( ~ r1_xboole_0(A_88,B_86)
      | ~ r2_hidden(D_90,k2_zfmisc_1(k2_zfmisc_1(k3_xboole_0(A_88,B_86),B_87),B_89)) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_181,plain,(
    ! [B_7,B_87,A_88,D_33,B_89,B_86] :
      ( ~ r1_xboole_0(A_88,B_86)
      | ~ r2_hidden(D_33,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k3_xboole_0(A_88,B_86),B_87),B_89),B_7)) ) ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_1813,plain,(
    ! [A_290,A_88,D_33,B_291,B_86] :
      ( ~ r1_xboole_0(A_88,B_86)
      | ~ r2_hidden(D_33,k3_xboole_0('#skF_8','#skF_9'))
      | ~ r1_xboole_0(A_290,B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1668,c_181])).

tff(c_1897,plain,(
    ! [A_290,B_291] : ~ r1_xboole_0(A_290,B_291) ),
    inference(splitLeft,[status(thm)],[c_1813])).

tff(c_1900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1897,c_35])).

tff(c_1901,plain,(
    ! [A_88,B_86,D_33] :
      ( ~ r1_xboole_0(A_88,B_86)
      | ~ r2_hidden(D_33,k3_xboole_0('#skF_8','#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_1813])).

tff(c_1902,plain,(
    ! [D_33] : ~ r2_hidden(D_33,k3_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1901])).

tff(c_342,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_3'(A_112,B_113,C_114),A_112)
      | r2_hidden('#skF_5'(A_112,B_113,C_114),C_114)
      | k2_zfmisc_1(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2972,plain,(
    ! [A_342,B_343,A_344,B_345] :
      ( ~ r1_xboole_0(A_342,B_343)
      | r2_hidden('#skF_3'(A_344,B_345,k3_xboole_0(A_342,B_343)),A_344)
      | k3_xboole_0(A_342,B_343) = k2_zfmisc_1(A_344,B_345) ) ),
    inference(resolution,[status(thm)],[c_342,c_4])).

tff(c_3172,plain,(
    ! [A_346,B_347,B_348] :
      ( ~ r1_xboole_0(A_346,B_347)
      | k3_xboole_0(A_346,B_347) = k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_9'),B_348) ) ),
    inference(resolution,[status(thm)],[c_2972,c_1902])).

tff(c_3175,plain,(
    ! [B_348] : k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_9'),B_348) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_35,c_3172])).

tff(c_43,plain,(
    ! [A_53,C_54,B_55,D_56] : k3_xboole_0(k2_zfmisc_1(A_53,C_54),k2_zfmisc_1(B_55,D_56)) = k2_zfmisc_1(k3_xboole_0(A_53,B_55),k3_xboole_0(C_54,D_56)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3989,plain,(
    ! [A_357,C_358,B_359,D_360] :
      ( r2_hidden('#skF_1'(k2_zfmisc_1(A_357,C_358),k2_zfmisc_1(B_359,D_360)),k2_zfmisc_1(k3_xboole_0(A_357,B_359),k3_xboole_0(C_358,D_360)))
      | r1_xboole_0(k2_zfmisc_1(A_357,C_358),k2_zfmisc_1(B_359,D_360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_2])).

tff(c_4018,plain,(
    ! [C_358,D_360] :
      ( r2_hidden('#skF_1'(k2_zfmisc_1('#skF_8',C_358),k2_zfmisc_1('#skF_9',D_360)),k3_xboole_0('#skF_8','#skF_9'))
      | r1_xboole_0(k2_zfmisc_1('#skF_8',C_358),k2_zfmisc_1('#skF_9',D_360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3175,c_3989])).

tff(c_4051,plain,(
    ! [C_358,D_360] : r1_xboole_0(k2_zfmisc_1('#skF_8',C_358),k2_zfmisc_1('#skF_9',D_360)) ),
    inference(negUnitSimplification,[status(thm)],[c_1902,c_4018])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_8','#skF_10'),k2_zfmisc_1('#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4051,c_32])).

tff(c_4059,plain,(
    ! [A_88,B_86] : ~ r1_xboole_0(A_88,B_86) ),
    inference(splitRight,[status(thm)],[c_1901])).

tff(c_4062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4059,c_35])).

tff(c_4063,plain,(
    r1_xboole_0('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4592,plain,(
    ! [A_462,B_463,C_464] :
      ( r2_hidden('#skF_4'(A_462,B_463,C_464),B_463)
      | r2_hidden('#skF_5'(A_462,B_463,C_464),C_464)
      | k2_zfmisc_1(A_462,B_463) = C_464 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5529,plain,(
    ! [A_603,B_604,A_605,B_606] :
      ( ~ r1_xboole_0(A_603,B_604)
      | r2_hidden('#skF_4'(A_605,B_606,k3_xboole_0(A_603,B_604)),B_606)
      | k3_xboole_0(A_603,B_604) = k2_zfmisc_1(A_605,B_606) ) ),
    inference(resolution,[status(thm)],[c_4592,c_4])).

tff(c_5694,plain,(
    ! [A_611,A_610,B_609,B_607,A_608] :
      ( ~ r1_xboole_0(A_610,B_609)
      | ~ r1_xboole_0(A_608,B_607)
      | k3_xboole_0(A_608,B_607) = k2_zfmisc_1(A_611,k3_xboole_0(A_610,B_609)) ) ),
    inference(resolution,[status(thm)],[c_5529,c_4])).

tff(c_5698,plain,(
    ! [A_612,B_613,A_614] :
      ( ~ r1_xboole_0(A_612,B_613)
      | k2_zfmisc_1(A_614,k3_xboole_0(A_612,B_613)) = k3_xboole_0('#skF_10','#skF_11') ) ),
    inference(resolution,[status(thm)],[c_4063,c_5694])).

tff(c_10,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_7'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),B_7)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4078,plain,(
    ! [A_373,B_374,D_375] :
      ( r2_hidden('#skF_6'(A_373,B_374,k2_zfmisc_1(A_373,B_374),D_375),A_373)
      | ~ r2_hidden(D_375,k2_zfmisc_1(A_373,B_374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4100,plain,(
    ! [A_380,B_381,D_382,B_383] :
      ( ~ r1_xboole_0(A_380,B_381)
      | ~ r2_hidden(D_382,k2_zfmisc_1(k3_xboole_0(A_380,B_381),B_383)) ) ),
    inference(resolution,[status(thm)],[c_4078,c_4])).

tff(c_4175,plain,(
    ! [B_398,D_402,A_401,B_400,A_399] :
      ( ~ r1_xboole_0(A_399,B_398)
      | ~ r2_hidden(D_402,k2_zfmisc_1(A_401,k2_zfmisc_1(k3_xboole_0(A_399,B_398),B_400))) ) ),
    inference(resolution,[status(thm)],[c_10,c_4100])).

tff(c_4191,plain,(
    ! [B_7,B_398,D_33,A_401,B_400,A_399] :
      ( ~ r1_xboole_0(A_399,B_398)
      | ~ r2_hidden(D_33,k2_zfmisc_1(k2_zfmisc_1(A_401,k2_zfmisc_1(k3_xboole_0(A_399,B_398),B_400)),B_7)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4175])).

tff(c_5837,plain,(
    ! [B_613,B_398,D_33,A_399,A_612] :
      ( ~ r1_xboole_0(A_399,B_398)
      | ~ r2_hidden(D_33,k3_xboole_0('#skF_10','#skF_11'))
      | ~ r1_xboole_0(A_612,B_613) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5698,c_4191])).

tff(c_5927,plain,(
    ! [A_612,B_613] : ~ r1_xboole_0(A_612,B_613) ),
    inference(splitLeft,[status(thm)],[c_5837])).

tff(c_5930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5927,c_4063])).

tff(c_5931,plain,(
    ! [A_399,B_398,D_33] :
      ( ~ r1_xboole_0(A_399,B_398)
      | ~ r2_hidden(D_33,k3_xboole_0('#skF_10','#skF_11')) ) ),
    inference(splitRight,[status(thm)],[c_5837])).

tff(c_5932,plain,(
    ! [D_33] : ~ r2_hidden(D_33,k3_xboole_0('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_5931])).

tff(c_4742,plain,(
    ! [A_1,B_2,A_462,B_463] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r2_hidden('#skF_4'(A_462,B_463,k3_xboole_0(A_1,B_2)),B_463)
      | k3_xboole_0(A_1,B_2) = k2_zfmisc_1(A_462,B_463) ) ),
    inference(resolution,[status(thm)],[c_4592,c_4])).

tff(c_5933,plain,(
    ! [D_615] : ~ r2_hidden(D_615,k3_xboole_0('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_5931])).

tff(c_6694,plain,(
    ! [A_645,B_646,A_647] :
      ( ~ r1_xboole_0(A_645,B_646)
      | k3_xboole_0(A_645,B_646) = k2_zfmisc_1(A_647,k3_xboole_0('#skF_10','#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_4742,c_5933])).

tff(c_6697,plain,(
    ! [A_647] : k2_zfmisc_1(A_647,k3_xboole_0('#skF_10','#skF_11')) = k3_xboole_0('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_4063,c_6694])).

tff(c_4132,plain,(
    ! [A_389,C_390,B_391,D_392] : k3_xboole_0(k2_zfmisc_1(A_389,C_390),k2_zfmisc_1(B_391,D_392)) = k2_zfmisc_1(k3_xboole_0(A_389,B_391),k3_xboole_0(C_390,D_392)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7999,plain,(
    ! [A_670,C_671,B_672,D_673] :
      ( r2_hidden('#skF_1'(k2_zfmisc_1(A_670,C_671),k2_zfmisc_1(B_672,D_673)),k2_zfmisc_1(k3_xboole_0(A_670,B_672),k3_xboole_0(C_671,D_673)))
      | r1_xboole_0(k2_zfmisc_1(A_670,C_671),k2_zfmisc_1(B_672,D_673)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4132,c_2])).

tff(c_8038,plain,(
    ! [A_670,B_672] :
      ( r2_hidden('#skF_1'(k2_zfmisc_1(A_670,'#skF_10'),k2_zfmisc_1(B_672,'#skF_11')),k3_xboole_0('#skF_10','#skF_11'))
      | r1_xboole_0(k2_zfmisc_1(A_670,'#skF_10'),k2_zfmisc_1(B_672,'#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6697,c_7999])).

tff(c_8064,plain,(
    ! [A_670,B_672] : r1_xboole_0(k2_zfmisc_1(A_670,'#skF_10'),k2_zfmisc_1(B_672,'#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_5932,c_8038])).

tff(c_8089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8064,c_32])).

tff(c_8090,plain,(
    ! [A_399,B_398] : ~ r1_xboole_0(A_399,B_398) ),
    inference(splitRight,[status(thm)],[c_5931])).

tff(c_8093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8090,c_4063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n007.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 09:43:36 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.20  
% 6.38/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.21  %$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 6.38/2.21  
% 6.38/2.21  %Foreground sorts:
% 6.38/2.21  
% 6.38/2.21  
% 6.38/2.21  %Background operators:
% 6.38/2.21  
% 6.38/2.21  
% 6.38/2.21  %Foreground operators:
% 6.38/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.38/2.21  tff('#skF_11', type, '#skF_11': $i).
% 6.38/2.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.38/2.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.38/2.21  tff('#skF_10', type, '#skF_10': $i).
% 6.38/2.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.38/2.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.38/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.38/2.21  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.38/2.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.38/2.21  tff('#skF_9', type, '#skF_9': $i).
% 6.38/2.21  tff('#skF_8', type, '#skF_8': $i).
% 6.38/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.38/2.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.38/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.38/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.38/2.21  
% 6.74/2.22  tff(f_60, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 6.74/2.22  tff(f_51, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.74/2.22  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.74/2.22  tff(f_53, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 6.74/2.22  tff(c_34, plain, (r1_xboole_0('#skF_10', '#skF_11') | r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.74/2.22  tff(c_35, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_34])).
% 6.74/2.22  tff(c_184, plain, (![A_91, B_92, C_93]: (r2_hidden('#skF_4'(A_91, B_92, C_93), B_92) | r2_hidden('#skF_5'(A_91, B_92, C_93), C_93) | k2_zfmisc_1(A_91, B_92)=C_93)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.74/2.22  tff(c_1499, plain, (![A_281, B_282, A_283, C_284]: (~r1_xboole_0(A_281, B_282) | r2_hidden('#skF_5'(A_283, k3_xboole_0(A_281, B_282), C_284), C_284) | k2_zfmisc_1(A_283, k3_xboole_0(A_281, B_282))=C_284)), inference(resolution, [status(thm)], [c_184, c_4])).
% 6.74/2.22  tff(c_1664, plain, (![A_285, A_289, A_288, B_286, B_287]: (~r1_xboole_0(A_289, B_287) | ~r1_xboole_0(A_285, B_286) | k3_xboole_0(A_289, B_287)=k2_zfmisc_1(A_288, k3_xboole_0(A_285, B_286)))), inference(resolution, [status(thm)], [c_1499, c_4])).
% 6.74/2.22  tff(c_1668, plain, (![A_290, B_291, A_292]: (~r1_xboole_0(A_290, B_291) | k2_zfmisc_1(A_292, k3_xboole_0(A_290, B_291))=k3_xboole_0('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_35, c_1664])).
% 6.74/2.22  tff(c_12, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), A_6) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_78, plain, (![A_64, B_65, D_66]: (r2_hidden('#skF_6'(A_64, B_65, k2_zfmisc_1(A_64, B_65), D_66), A_64) | ~r2_hidden(D_66, k2_zfmisc_1(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_89, plain, (![A_67, B_68, D_69, B_70]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(D_69, k2_zfmisc_1(k3_xboole_0(A_67, B_68), B_70)))), inference(resolution, [status(thm)], [c_78, c_4])).
% 6.74/2.22  tff(c_165, plain, (![B_87, A_88, B_89, B_86, D_90]: (~r1_xboole_0(A_88, B_86) | ~r2_hidden(D_90, k2_zfmisc_1(k2_zfmisc_1(k3_xboole_0(A_88, B_86), B_87), B_89)))), inference(resolution, [status(thm)], [c_12, c_89])).
% 6.74/2.22  tff(c_181, plain, (![B_7, B_87, A_88, D_33, B_89, B_86]: (~r1_xboole_0(A_88, B_86) | ~r2_hidden(D_33, k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k3_xboole_0(A_88, B_86), B_87), B_89), B_7)))), inference(resolution, [status(thm)], [c_12, c_165])).
% 6.74/2.22  tff(c_1813, plain, (![A_290, A_88, D_33, B_291, B_86]: (~r1_xboole_0(A_88, B_86) | ~r2_hidden(D_33, k3_xboole_0('#skF_8', '#skF_9')) | ~r1_xboole_0(A_290, B_291))), inference(superposition, [status(thm), theory('equality')], [c_1668, c_181])).
% 6.74/2.22  tff(c_1897, plain, (![A_290, B_291]: (~r1_xboole_0(A_290, B_291))), inference(splitLeft, [status(thm)], [c_1813])).
% 6.74/2.22  tff(c_1900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1897, c_35])).
% 6.74/2.22  tff(c_1901, plain, (![A_88, B_86, D_33]: (~r1_xboole_0(A_88, B_86) | ~r2_hidden(D_33, k3_xboole_0('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_1813])).
% 6.74/2.22  tff(c_1902, plain, (![D_33]: (~r2_hidden(D_33, k3_xboole_0('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_1901])).
% 6.74/2.22  tff(c_342, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_3'(A_112, B_113, C_114), A_112) | r2_hidden('#skF_5'(A_112, B_113, C_114), C_114) | k2_zfmisc_1(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_2972, plain, (![A_342, B_343, A_344, B_345]: (~r1_xboole_0(A_342, B_343) | r2_hidden('#skF_3'(A_344, B_345, k3_xboole_0(A_342, B_343)), A_344) | k3_xboole_0(A_342, B_343)=k2_zfmisc_1(A_344, B_345))), inference(resolution, [status(thm)], [c_342, c_4])).
% 6.74/2.22  tff(c_3172, plain, (![A_346, B_347, B_348]: (~r1_xboole_0(A_346, B_347) | k3_xboole_0(A_346, B_347)=k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_9'), B_348))), inference(resolution, [status(thm)], [c_2972, c_1902])).
% 6.74/2.22  tff(c_3175, plain, (![B_348]: (k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_9'), B_348)=k3_xboole_0('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_35, c_3172])).
% 6.74/2.22  tff(c_43, plain, (![A_53, C_54, B_55, D_56]: (k3_xboole_0(k2_zfmisc_1(A_53, C_54), k2_zfmisc_1(B_55, D_56))=k2_zfmisc_1(k3_xboole_0(A_53, B_55), k3_xboole_0(C_54, D_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.74/2.22  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.74/2.22  tff(c_3989, plain, (![A_357, C_358, B_359, D_360]: (r2_hidden('#skF_1'(k2_zfmisc_1(A_357, C_358), k2_zfmisc_1(B_359, D_360)), k2_zfmisc_1(k3_xboole_0(A_357, B_359), k3_xboole_0(C_358, D_360))) | r1_xboole_0(k2_zfmisc_1(A_357, C_358), k2_zfmisc_1(B_359, D_360)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_2])).
% 6.74/2.22  tff(c_4018, plain, (![C_358, D_360]: (r2_hidden('#skF_1'(k2_zfmisc_1('#skF_8', C_358), k2_zfmisc_1('#skF_9', D_360)), k3_xboole_0('#skF_8', '#skF_9')) | r1_xboole_0(k2_zfmisc_1('#skF_8', C_358), k2_zfmisc_1('#skF_9', D_360)))), inference(superposition, [status(thm), theory('equality')], [c_3175, c_3989])).
% 6.74/2.22  tff(c_4051, plain, (![C_358, D_360]: (r1_xboole_0(k2_zfmisc_1('#skF_8', C_358), k2_zfmisc_1('#skF_9', D_360)))), inference(negUnitSimplification, [status(thm)], [c_1902, c_4018])).
% 6.74/2.22  tff(c_32, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_10'), k2_zfmisc_1('#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.74/2.22  tff(c_4058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4051, c_32])).
% 6.74/2.22  tff(c_4059, plain, (![A_88, B_86]: (~r1_xboole_0(A_88, B_86))), inference(splitRight, [status(thm)], [c_1901])).
% 6.74/2.22  tff(c_4062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4059, c_35])).
% 6.74/2.22  tff(c_4063, plain, (r1_xboole_0('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_34])).
% 6.74/2.22  tff(c_4592, plain, (![A_462, B_463, C_464]: (r2_hidden('#skF_4'(A_462, B_463, C_464), B_463) | r2_hidden('#skF_5'(A_462, B_463, C_464), C_464) | k2_zfmisc_1(A_462, B_463)=C_464)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_5529, plain, (![A_603, B_604, A_605, B_606]: (~r1_xboole_0(A_603, B_604) | r2_hidden('#skF_4'(A_605, B_606, k3_xboole_0(A_603, B_604)), B_606) | k3_xboole_0(A_603, B_604)=k2_zfmisc_1(A_605, B_606))), inference(resolution, [status(thm)], [c_4592, c_4])).
% 6.74/2.22  tff(c_5694, plain, (![A_611, A_610, B_609, B_607, A_608]: (~r1_xboole_0(A_610, B_609) | ~r1_xboole_0(A_608, B_607) | k3_xboole_0(A_608, B_607)=k2_zfmisc_1(A_611, k3_xboole_0(A_610, B_609)))), inference(resolution, [status(thm)], [c_5529, c_4])).
% 6.74/2.22  tff(c_5698, plain, (![A_612, B_613, A_614]: (~r1_xboole_0(A_612, B_613) | k2_zfmisc_1(A_614, k3_xboole_0(A_612, B_613))=k3_xboole_0('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_4063, c_5694])).
% 6.74/2.22  tff(c_10, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_7'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), B_7) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_4078, plain, (![A_373, B_374, D_375]: (r2_hidden('#skF_6'(A_373, B_374, k2_zfmisc_1(A_373, B_374), D_375), A_373) | ~r2_hidden(D_375, k2_zfmisc_1(A_373, B_374)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.74/2.22  tff(c_4100, plain, (![A_380, B_381, D_382, B_383]: (~r1_xboole_0(A_380, B_381) | ~r2_hidden(D_382, k2_zfmisc_1(k3_xboole_0(A_380, B_381), B_383)))), inference(resolution, [status(thm)], [c_4078, c_4])).
% 6.74/2.22  tff(c_4175, plain, (![B_398, D_402, A_401, B_400, A_399]: (~r1_xboole_0(A_399, B_398) | ~r2_hidden(D_402, k2_zfmisc_1(A_401, k2_zfmisc_1(k3_xboole_0(A_399, B_398), B_400))))), inference(resolution, [status(thm)], [c_10, c_4100])).
% 6.74/2.22  tff(c_4191, plain, (![B_7, B_398, D_33, A_401, B_400, A_399]: (~r1_xboole_0(A_399, B_398) | ~r2_hidden(D_33, k2_zfmisc_1(k2_zfmisc_1(A_401, k2_zfmisc_1(k3_xboole_0(A_399, B_398), B_400)), B_7)))), inference(resolution, [status(thm)], [c_12, c_4175])).
% 6.74/2.22  tff(c_5837, plain, (![B_613, B_398, D_33, A_399, A_612]: (~r1_xboole_0(A_399, B_398) | ~r2_hidden(D_33, k3_xboole_0('#skF_10', '#skF_11')) | ~r1_xboole_0(A_612, B_613))), inference(superposition, [status(thm), theory('equality')], [c_5698, c_4191])).
% 6.74/2.22  tff(c_5927, plain, (![A_612, B_613]: (~r1_xboole_0(A_612, B_613))), inference(splitLeft, [status(thm)], [c_5837])).
% 6.74/2.22  tff(c_5930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5927, c_4063])).
% 6.74/2.22  tff(c_5931, plain, (![A_399, B_398, D_33]: (~r1_xboole_0(A_399, B_398) | ~r2_hidden(D_33, k3_xboole_0('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_5837])).
% 6.74/2.22  tff(c_5932, plain, (![D_33]: (~r2_hidden(D_33, k3_xboole_0('#skF_10', '#skF_11')))), inference(splitLeft, [status(thm)], [c_5931])).
% 6.74/2.22  tff(c_4742, plain, (![A_1, B_2, A_462, B_463]: (~r1_xboole_0(A_1, B_2) | r2_hidden('#skF_4'(A_462, B_463, k3_xboole_0(A_1, B_2)), B_463) | k3_xboole_0(A_1, B_2)=k2_zfmisc_1(A_462, B_463))), inference(resolution, [status(thm)], [c_4592, c_4])).
% 6.74/2.22  tff(c_5933, plain, (![D_615]: (~r2_hidden(D_615, k3_xboole_0('#skF_10', '#skF_11')))), inference(splitLeft, [status(thm)], [c_5931])).
% 6.74/2.22  tff(c_6694, plain, (![A_645, B_646, A_647]: (~r1_xboole_0(A_645, B_646) | k3_xboole_0(A_645, B_646)=k2_zfmisc_1(A_647, k3_xboole_0('#skF_10', '#skF_11')))), inference(resolution, [status(thm)], [c_4742, c_5933])).
% 6.74/2.22  tff(c_6697, plain, (![A_647]: (k2_zfmisc_1(A_647, k3_xboole_0('#skF_10', '#skF_11'))=k3_xboole_0('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_4063, c_6694])).
% 6.74/2.22  tff(c_4132, plain, (![A_389, C_390, B_391, D_392]: (k3_xboole_0(k2_zfmisc_1(A_389, C_390), k2_zfmisc_1(B_391, D_392))=k2_zfmisc_1(k3_xboole_0(A_389, B_391), k3_xboole_0(C_390, D_392)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.74/2.22  tff(c_7999, plain, (![A_670, C_671, B_672, D_673]: (r2_hidden('#skF_1'(k2_zfmisc_1(A_670, C_671), k2_zfmisc_1(B_672, D_673)), k2_zfmisc_1(k3_xboole_0(A_670, B_672), k3_xboole_0(C_671, D_673))) | r1_xboole_0(k2_zfmisc_1(A_670, C_671), k2_zfmisc_1(B_672, D_673)))), inference(superposition, [status(thm), theory('equality')], [c_4132, c_2])).
% 6.74/2.22  tff(c_8038, plain, (![A_670, B_672]: (r2_hidden('#skF_1'(k2_zfmisc_1(A_670, '#skF_10'), k2_zfmisc_1(B_672, '#skF_11')), k3_xboole_0('#skF_10', '#skF_11')) | r1_xboole_0(k2_zfmisc_1(A_670, '#skF_10'), k2_zfmisc_1(B_672, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_6697, c_7999])).
% 6.74/2.22  tff(c_8064, plain, (![A_670, B_672]: (r1_xboole_0(k2_zfmisc_1(A_670, '#skF_10'), k2_zfmisc_1(B_672, '#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_5932, c_8038])).
% 6.74/2.22  tff(c_8089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8064, c_32])).
% 6.74/2.22  tff(c_8090, plain, (![A_399, B_398]: (~r1_xboole_0(A_399, B_398))), inference(splitRight, [status(thm)], [c_5931])).
% 6.74/2.22  tff(c_8093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8090, c_4063])).
% 6.74/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/2.22  
% 6.74/2.22  Inference rules
% 6.74/2.22  ----------------------
% 6.74/2.22  #Ref     : 0
% 6.74/2.22  #Sup     : 1804
% 6.74/2.22  #Fact    : 0
% 6.74/2.22  #Define  : 0
% 6.74/2.22  #Split   : 5
% 6.74/2.22  #Chain   : 0
% 6.74/2.22  #Close   : 0
% 6.74/2.22  
% 6.74/2.22  Ordering : KBO
% 6.74/2.22  
% 6.74/2.22  Simplification rules
% 6.74/2.22  ----------------------
% 6.74/2.22  #Subsume      : 840
% 6.74/2.22  #Demod        : 618
% 6.74/2.22  #Tautology    : 60
% 6.74/2.22  #SimpNegUnit  : 26
% 6.74/2.22  #BackRed      : 31
% 6.74/2.22  
% 6.74/2.22  #Partial instantiations: 0
% 6.74/2.22  #Strategies tried      : 1
% 6.74/2.22  
% 6.74/2.22  Timing (in seconds)
% 6.74/2.22  ----------------------
% 6.74/2.23  Preprocessing        : 0.30
% 6.74/2.23  Parsing              : 0.16
% 6.74/2.23  CNF conversion       : 0.02
% 6.74/2.23  Main loop            : 1.27
% 6.74/2.23  Inferencing          : 0.48
% 6.74/2.23  Reduction            : 0.27
% 6.74/2.23  Demodulation         : 0.20
% 6.74/2.23  BG Simplification    : 0.05
% 6.74/2.23  Subsumption          : 0.35
% 6.74/2.23  Abstraction          : 0.10
% 6.74/2.23  MUC search           : 0.00
% 6.74/2.23  Cooper               : 0.00
% 6.74/2.23  Total                : 1.60
% 6.74/2.23  Index Insertion      : 0.00
% 6.74/2.23  Index Deletion       : 0.00
% 6.74/2.23  Index Matching       : 0.00
% 6.74/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
