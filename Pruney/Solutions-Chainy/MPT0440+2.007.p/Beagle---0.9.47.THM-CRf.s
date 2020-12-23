%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:18 EST 2020

% Result     : Theorem 8.76s
% Output     : CNFRefutation 8.76s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 133 expanded)
%              Number of leaves         :   41 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 194 expanded)
%              Number of equality atoms :   25 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( C = k1_tarski(k4_tarski(A,B))
         => ( k1_relat_1(C) = k1_tarski(A)
            & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_74,plain,(
    k1_tarski(k4_tarski('#skF_10','#skF_11')) = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4204,plain,(
    ! [A_429,C_430,B_431] :
      ( r2_hidden(A_429,C_430)
      | ~ r1_tarski(k2_tarski(A_429,B_431),C_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4226,plain,(
    ! [A_434,B_435] : r2_hidden(A_434,k2_tarski(A_434,B_435)) ),
    inference(resolution,[status(thm)],[c_16,c_4204])).

tff(c_4230,plain,(
    ! [A_436] : r2_hidden(A_436,k1_tarski(A_436)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4226])).

tff(c_4236,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4230])).

tff(c_4288,plain,(
    ! [C_451,A_452,D_453] :
      ( r2_hidden(C_451,k2_relat_1(A_452))
      | ~ r2_hidden(k4_tarski(D_453,C_451),A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4309,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_4236,c_4288])).

tff(c_4500,plain,(
    ! [A_503,B_504,C_505] :
      ( r1_tarski(k2_tarski(A_503,B_504),C_505)
      | ~ r2_hidden(B_504,C_505)
      | ~ r2_hidden(A_503,C_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4511,plain,(
    ! [A_8,C_505] :
      ( r1_tarski(k1_tarski(A_8),C_505)
      | ~ r2_hidden(A_8,C_505)
      | ~ r2_hidden(A_8,C_505) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4500])).

tff(c_105,plain,(
    ! [A_93,C_94,B_95] :
      ( r2_hidden(A_93,C_94)
      | ~ r1_tarski(k2_tarski(A_93,B_95),C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_114,plain,(
    ! [A_96,B_97] : r2_hidden(A_96,k2_tarski(A_96,B_97)) ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_118,plain,(
    ! [A_98] : r2_hidden(A_98,k1_tarski(A_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_114])).

tff(c_121,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_118])).

tff(c_173,plain,(
    ! [C_113,A_114,D_115] :
      ( r2_hidden(C_113,k1_relat_1(A_114))
      | ~ r2_hidden(k4_tarski(C_113,D_115),A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_194,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_121,c_173])).

tff(c_393,plain,(
    ! [A_168,B_169,C_170] :
      ( r1_tarski(k2_tarski(A_168,B_169),C_170)
      | ~ r2_hidden(B_169,C_170)
      | ~ r2_hidden(A_168,C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_404,plain,(
    ! [A_8,C_170] :
      ( r1_tarski(k1_tarski(A_8),C_170)
      | ~ r2_hidden(A_8,C_170)
      | ~ r2_hidden(A_8,C_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_393])).

tff(c_72,plain,
    ( k2_relat_1('#skF_12') != k1_tarski('#skF_11')
    | k1_tarski('#skF_10') != k1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_104,plain,(
    k1_tarski('#skF_10') != k1_relat_1('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1139,plain,(
    ! [A_249,B_250,C_251] : k2_zfmisc_1(k1_tarski(A_249),k2_tarski(B_250,C_251)) = k2_tarski(k4_tarski(A_249,B_250),k4_tarski(A_249,C_251)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1267,plain,(
    ! [A_249,B_250] : k2_zfmisc_1(k1_tarski(A_249),k2_tarski(B_250,B_250)) = k1_tarski(k4_tarski(A_249,B_250)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1139])).

tff(c_1276,plain,(
    ! [A_249,B_250] : k2_zfmisc_1(k1_tarski(A_249),k1_tarski(B_250)) = k1_tarski(k4_tarski(A_249,B_250)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1267])).

tff(c_1748,plain,(
    ! [C_281,A_282] :
      ( r2_hidden(k4_tarski(C_281,'#skF_5'(A_282,k1_relat_1(A_282),C_281)),A_282)
      | ~ r2_hidden(C_281,k1_relat_1(A_282)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [A_36,C_38,B_37,D_39] :
      ( r2_hidden(A_36,C_38)
      | ~ r2_hidden(k4_tarski(A_36,B_37),k2_zfmisc_1(C_38,D_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1812,plain,(
    ! [C_285,C_286,D_287] :
      ( r2_hidden(C_285,C_286)
      | ~ r2_hidden(C_285,k1_relat_1(k2_zfmisc_1(C_286,D_287))) ) ),
    inference(resolution,[status(thm)],[c_1748,c_36])).

tff(c_3937,plain,(
    ! [C_415,A_416,B_417] :
      ( r2_hidden(C_415,k1_tarski(A_416))
      | ~ r2_hidden(C_415,k1_relat_1(k1_tarski(k4_tarski(A_416,B_417)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_1812])).

tff(c_3993,plain,(
    ! [C_418] :
      ( r2_hidden(C_418,k1_tarski('#skF_10'))
      | ~ r2_hidden(C_418,k1_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_3937])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4153,plain,(
    ! [B_426] :
      ( ~ r2_xboole_0(k1_tarski('#skF_10'),B_426)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_10'),B_426),k1_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_3993,c_8])).

tff(c_4158,plain,(
    ~ r2_xboole_0(k1_tarski('#skF_10'),k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_10,c_4153])).

tff(c_4161,plain,
    ( k1_tarski('#skF_10') = k1_relat_1('#skF_12')
    | ~ r1_tarski(k1_tarski('#skF_10'),k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_2,c_4158])).

tff(c_4164,plain,(
    ~ r1_tarski(k1_tarski('#skF_10'),k1_relat_1('#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4161])).

tff(c_4187,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_404,c_4164])).

tff(c_4191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_4187])).

tff(c_4192,plain,(
    k2_relat_1('#skF_12') != k1_tarski('#skF_11') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4669,plain,(
    ! [A_515,B_516,C_517] : k2_zfmisc_1(k2_tarski(A_515,B_516),k1_tarski(C_517)) = k2_tarski(k4_tarski(A_515,C_517),k4_tarski(B_516,C_517)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4721,plain,(
    ! [B_516,C_517] : k2_zfmisc_1(k2_tarski(B_516,B_516),k1_tarski(C_517)) = k1_tarski(k4_tarski(B_516,C_517)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4669,c_18])).

tff(c_4743,plain,(
    ! [B_516,C_517] : k2_zfmisc_1(k1_tarski(B_516),k1_tarski(C_517)) = k1_tarski(k4_tarski(B_516,C_517)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4721])).

tff(c_4881,plain,(
    ! [A_523,C_524] :
      ( r2_hidden(k4_tarski('#skF_9'(A_523,k2_relat_1(A_523),C_524),C_524),A_523)
      | ~ r2_hidden(C_524,k2_relat_1(A_523)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [B_37,D_39,A_36,C_38] :
      ( r2_hidden(B_37,D_39)
      | ~ r2_hidden(k4_tarski(A_36,B_37),k2_zfmisc_1(C_38,D_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5102,plain,(
    ! [C_539,D_540,C_541] :
      ( r2_hidden(C_539,D_540)
      | ~ r2_hidden(C_539,k2_relat_1(k2_zfmisc_1(C_541,D_540))) ) ),
    inference(resolution,[status(thm)],[c_4881,c_34])).

tff(c_9650,plain,(
    ! [C_757,C_758,B_759] :
      ( r2_hidden(C_757,k1_tarski(C_758))
      | ~ r2_hidden(C_757,k2_relat_1(k1_tarski(k4_tarski(B_759,C_758)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4743,c_5102])).

tff(c_9714,plain,(
    ! [C_760] :
      ( r2_hidden(C_760,k1_tarski('#skF_11'))
      | ~ r2_hidden(C_760,k2_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_9650])).

tff(c_11518,plain,(
    ! [A_859] :
      ( r2_hidden('#skF_1'(A_859,k2_relat_1('#skF_12')),k1_tarski('#skF_11'))
      | ~ r2_xboole_0(A_859,k2_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_10,c_9714])).

tff(c_11529,plain,(
    ~ r2_xboole_0(k1_tarski('#skF_11'),k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_11518,c_8])).

tff(c_11607,plain,
    ( k2_relat_1('#skF_12') = k1_tarski('#skF_11')
    | ~ r1_tarski(k1_tarski('#skF_11'),k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_2,c_11529])).

tff(c_11610,plain,(
    ~ r1_tarski(k1_tarski('#skF_11'),k2_relat_1('#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_4192,c_11607])).

tff(c_11613,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_4511,c_11610])).

tff(c_11617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4309,c_11613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.76/3.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.76/3.41  
% 8.76/3.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.76/3.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 8.76/3.41  
% 8.76/3.41  %Foreground sorts:
% 8.76/3.41  
% 8.76/3.41  
% 8.76/3.41  %Background operators:
% 8.76/3.41  
% 8.76/3.41  
% 8.76/3.41  %Foreground operators:
% 8.76/3.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.76/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.76/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.76/3.41  tff('#skF_11', type, '#skF_11': $i).
% 8.76/3.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.76/3.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.76/3.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.76/3.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.76/3.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.76/3.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.76/3.41  tff('#skF_10', type, '#skF_10': $i).
% 8.76/3.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.76/3.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.76/3.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.76/3.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.76/3.41  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.76/3.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.76/3.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.76/3.41  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 8.76/3.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.76/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.76/3.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.76/3.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.76/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.76/3.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.76/3.41  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.76/3.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.76/3.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.76/3.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.76/3.41  tff('#skF_12', type, '#skF_12': $i).
% 8.76/3.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.76/3.41  
% 8.76/3.42  tff(f_103, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 8.76/3.42  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.76/3.42  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.76/3.42  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.76/3.42  tff(f_94, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.76/3.42  tff(f_86, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 8.76/3.42  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.76/3.42  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 8.76/3.42  tff(f_72, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 8.76/3.42  tff(f_68, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.76/3.42  tff(c_74, plain, (k1_tarski(k4_tarski('#skF_10', '#skF_11'))='#skF_12'), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.76/3.42  tff(c_18, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.76/3.42  tff(c_16, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.76/3.42  tff(c_4204, plain, (![A_429, C_430, B_431]: (r2_hidden(A_429, C_430) | ~r1_tarski(k2_tarski(A_429, B_431), C_430))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.76/3.42  tff(c_4226, plain, (![A_434, B_435]: (r2_hidden(A_434, k2_tarski(A_434, B_435)))), inference(resolution, [status(thm)], [c_16, c_4204])).
% 8.76/3.42  tff(c_4230, plain, (![A_436]: (r2_hidden(A_436, k1_tarski(A_436)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4226])).
% 8.76/3.42  tff(c_4236, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_74, c_4230])).
% 8.76/3.42  tff(c_4288, plain, (![C_451, A_452, D_453]: (r2_hidden(C_451, k2_relat_1(A_452)) | ~r2_hidden(k4_tarski(D_453, C_451), A_452))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.76/3.42  tff(c_4309, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_4236, c_4288])).
% 8.76/3.42  tff(c_4500, plain, (![A_503, B_504, C_505]: (r1_tarski(k2_tarski(A_503, B_504), C_505) | ~r2_hidden(B_504, C_505) | ~r2_hidden(A_503, C_505))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.76/3.42  tff(c_4511, plain, (![A_8, C_505]: (r1_tarski(k1_tarski(A_8), C_505) | ~r2_hidden(A_8, C_505) | ~r2_hidden(A_8, C_505))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4500])).
% 8.76/3.42  tff(c_105, plain, (![A_93, C_94, B_95]: (r2_hidden(A_93, C_94) | ~r1_tarski(k2_tarski(A_93, B_95), C_94))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.76/3.42  tff(c_114, plain, (![A_96, B_97]: (r2_hidden(A_96, k2_tarski(A_96, B_97)))), inference(resolution, [status(thm)], [c_16, c_105])).
% 8.76/3.42  tff(c_118, plain, (![A_98]: (r2_hidden(A_98, k1_tarski(A_98)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_114])).
% 8.76/3.42  tff(c_121, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_74, c_118])).
% 8.76/3.42  tff(c_173, plain, (![C_113, A_114, D_115]: (r2_hidden(C_113, k1_relat_1(A_114)) | ~r2_hidden(k4_tarski(C_113, D_115), A_114))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.76/3.42  tff(c_194, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_121, c_173])).
% 8.76/3.42  tff(c_393, plain, (![A_168, B_169, C_170]: (r1_tarski(k2_tarski(A_168, B_169), C_170) | ~r2_hidden(B_169, C_170) | ~r2_hidden(A_168, C_170))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.76/3.42  tff(c_404, plain, (![A_8, C_170]: (r1_tarski(k1_tarski(A_8), C_170) | ~r2_hidden(A_8, C_170) | ~r2_hidden(A_8, C_170))), inference(superposition, [status(thm), theory('equality')], [c_18, c_393])).
% 8.76/3.42  tff(c_72, plain, (k2_relat_1('#skF_12')!=k1_tarski('#skF_11') | k1_tarski('#skF_10')!=k1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.76/3.42  tff(c_104, plain, (k1_tarski('#skF_10')!=k1_relat_1('#skF_12')), inference(splitLeft, [status(thm)], [c_72])).
% 8.76/3.42  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.76/3.42  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.76/3.42  tff(c_1139, plain, (![A_249, B_250, C_251]: (k2_zfmisc_1(k1_tarski(A_249), k2_tarski(B_250, C_251))=k2_tarski(k4_tarski(A_249, B_250), k4_tarski(A_249, C_251)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.76/3.42  tff(c_1267, plain, (![A_249, B_250]: (k2_zfmisc_1(k1_tarski(A_249), k2_tarski(B_250, B_250))=k1_tarski(k4_tarski(A_249, B_250)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1139])).
% 8.76/3.42  tff(c_1276, plain, (![A_249, B_250]: (k2_zfmisc_1(k1_tarski(A_249), k1_tarski(B_250))=k1_tarski(k4_tarski(A_249, B_250)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1267])).
% 8.76/3.42  tff(c_1748, plain, (![C_281, A_282]: (r2_hidden(k4_tarski(C_281, '#skF_5'(A_282, k1_relat_1(A_282), C_281)), A_282) | ~r2_hidden(C_281, k1_relat_1(A_282)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.76/3.42  tff(c_36, plain, (![A_36, C_38, B_37, D_39]: (r2_hidden(A_36, C_38) | ~r2_hidden(k4_tarski(A_36, B_37), k2_zfmisc_1(C_38, D_39)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.76/3.42  tff(c_1812, plain, (![C_285, C_286, D_287]: (r2_hidden(C_285, C_286) | ~r2_hidden(C_285, k1_relat_1(k2_zfmisc_1(C_286, D_287))))), inference(resolution, [status(thm)], [c_1748, c_36])).
% 8.76/3.42  tff(c_3937, plain, (![C_415, A_416, B_417]: (r2_hidden(C_415, k1_tarski(A_416)) | ~r2_hidden(C_415, k1_relat_1(k1_tarski(k4_tarski(A_416, B_417)))))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_1812])).
% 8.76/3.42  tff(c_3993, plain, (![C_418]: (r2_hidden(C_418, k1_tarski('#skF_10')) | ~r2_hidden(C_418, k1_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_3937])).
% 8.76/3.42  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.76/3.42  tff(c_4153, plain, (![B_426]: (~r2_xboole_0(k1_tarski('#skF_10'), B_426) | ~r2_hidden('#skF_1'(k1_tarski('#skF_10'), B_426), k1_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_3993, c_8])).
% 8.76/3.42  tff(c_4158, plain, (~r2_xboole_0(k1_tarski('#skF_10'), k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_10, c_4153])).
% 8.76/3.42  tff(c_4161, plain, (k1_tarski('#skF_10')=k1_relat_1('#skF_12') | ~r1_tarski(k1_tarski('#skF_10'), k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_2, c_4158])).
% 8.76/3.42  tff(c_4164, plain, (~r1_tarski(k1_tarski('#skF_10'), k1_relat_1('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_104, c_4161])).
% 8.76/3.42  tff(c_4187, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_404, c_4164])).
% 8.76/3.42  tff(c_4191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_4187])).
% 8.76/3.42  tff(c_4192, plain, (k2_relat_1('#skF_12')!=k1_tarski('#skF_11')), inference(splitRight, [status(thm)], [c_72])).
% 8.76/3.42  tff(c_4669, plain, (![A_515, B_516, C_517]: (k2_zfmisc_1(k2_tarski(A_515, B_516), k1_tarski(C_517))=k2_tarski(k4_tarski(A_515, C_517), k4_tarski(B_516, C_517)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.76/3.42  tff(c_4721, plain, (![B_516, C_517]: (k2_zfmisc_1(k2_tarski(B_516, B_516), k1_tarski(C_517))=k1_tarski(k4_tarski(B_516, C_517)))), inference(superposition, [status(thm), theory('equality')], [c_4669, c_18])).
% 8.76/3.42  tff(c_4743, plain, (![B_516, C_517]: (k2_zfmisc_1(k1_tarski(B_516), k1_tarski(C_517))=k1_tarski(k4_tarski(B_516, C_517)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4721])).
% 8.76/3.42  tff(c_4881, plain, (![A_523, C_524]: (r2_hidden(k4_tarski('#skF_9'(A_523, k2_relat_1(A_523), C_524), C_524), A_523) | ~r2_hidden(C_524, k2_relat_1(A_523)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.76/3.42  tff(c_34, plain, (![B_37, D_39, A_36, C_38]: (r2_hidden(B_37, D_39) | ~r2_hidden(k4_tarski(A_36, B_37), k2_zfmisc_1(C_38, D_39)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.76/3.42  tff(c_5102, plain, (![C_539, D_540, C_541]: (r2_hidden(C_539, D_540) | ~r2_hidden(C_539, k2_relat_1(k2_zfmisc_1(C_541, D_540))))), inference(resolution, [status(thm)], [c_4881, c_34])).
% 8.76/3.42  tff(c_9650, plain, (![C_757, C_758, B_759]: (r2_hidden(C_757, k1_tarski(C_758)) | ~r2_hidden(C_757, k2_relat_1(k1_tarski(k4_tarski(B_759, C_758)))))), inference(superposition, [status(thm), theory('equality')], [c_4743, c_5102])).
% 8.76/3.42  tff(c_9714, plain, (![C_760]: (r2_hidden(C_760, k1_tarski('#skF_11')) | ~r2_hidden(C_760, k2_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_9650])).
% 8.76/3.42  tff(c_11518, plain, (![A_859]: (r2_hidden('#skF_1'(A_859, k2_relat_1('#skF_12')), k1_tarski('#skF_11')) | ~r2_xboole_0(A_859, k2_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_10, c_9714])).
% 8.76/3.42  tff(c_11529, plain, (~r2_xboole_0(k1_tarski('#skF_11'), k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_11518, c_8])).
% 8.76/3.42  tff(c_11607, plain, (k2_relat_1('#skF_12')=k1_tarski('#skF_11') | ~r1_tarski(k1_tarski('#skF_11'), k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_2, c_11529])).
% 8.76/3.42  tff(c_11610, plain, (~r1_tarski(k1_tarski('#skF_11'), k2_relat_1('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_4192, c_11607])).
% 8.76/3.42  tff(c_11613, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_4511, c_11610])).
% 8.76/3.42  tff(c_11617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4309, c_11613])).
% 8.76/3.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.76/3.42  
% 8.76/3.42  Inference rules
% 8.76/3.42  ----------------------
% 8.76/3.42  #Ref     : 0
% 8.76/3.42  #Sup     : 2919
% 8.76/3.42  #Fact    : 0
% 8.76/3.42  #Define  : 0
% 8.76/3.42  #Split   : 5
% 8.76/3.42  #Chain   : 0
% 8.76/3.42  #Close   : 0
% 8.76/3.42  
% 8.76/3.42  Ordering : KBO
% 8.76/3.42  
% 8.76/3.42  Simplification rules
% 8.76/3.42  ----------------------
% 8.76/3.42  #Subsume      : 81
% 8.76/3.42  #Demod        : 999
% 8.76/3.42  #Tautology    : 694
% 8.76/3.42  #SimpNegUnit  : 2
% 8.76/3.42  #BackRed      : 16
% 8.76/3.42  
% 8.76/3.42  #Partial instantiations: 0
% 8.76/3.42  #Strategies tried      : 1
% 8.76/3.42  
% 8.76/3.42  Timing (in seconds)
% 8.76/3.42  ----------------------
% 8.76/3.43  Preprocessing        : 0.34
% 8.76/3.43  Parsing              : 0.18
% 8.76/3.43  CNF conversion       : 0.03
% 8.76/3.43  Main loop            : 2.31
% 8.76/3.43  Inferencing          : 0.57
% 8.76/3.43  Reduction            : 1.09
% 8.76/3.43  Demodulation         : 0.91
% 8.76/3.43  BG Simplification    : 0.07
% 8.76/3.43  Subsumption          : 0.42
% 8.76/3.43  Abstraction          : 0.07
% 8.76/3.43  MUC search           : 0.00
% 8.76/3.43  Cooper               : 0.00
% 8.76/3.43  Total                : 2.69
% 8.76/3.43  Index Insertion      : 0.00
% 8.76/3.43  Index Deletion       : 0.00
% 8.76/3.43  Index Matching       : 0.00
% 8.76/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
