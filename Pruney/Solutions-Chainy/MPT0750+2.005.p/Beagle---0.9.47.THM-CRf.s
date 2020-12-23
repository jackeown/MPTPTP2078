%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:24 EST 2020

% Result     : Theorem 12.87s
% Output     : CNFRefutation 12.87s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 391 expanded)
%              Number of leaves         :   40 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 ( 829 expanded)
%              Number of equality atoms :   33 (  86 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_6 > #skF_8 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,axiom,(
    ! [A] :
      ( v4_ordinal1(A)
    <=> A = k3_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( v4_ordinal1(A)
        <=> ! [B] :
              ( v3_ordinal1(B)
             => ( r2_hidden(B,A)
               => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_109,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_114,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_73,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_56,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_116,plain,(
    ! [A_59] :
      ( v4_ordinal1(A_59)
      | k3_tarski(A_59) != A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_84,plain,
    ( v3_ordinal1('#skF_10')
    | ~ v4_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_95,plain,(
    ~ v4_ordinal1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_120,plain,(
    k3_tarski('#skF_9') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_116,c_95])).

tff(c_78,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ! [A_49] :
      ( v3_ordinal1(k3_tarski(A_49))
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_94,plain,(
    ! [B_54] :
      ( v4_ordinal1('#skF_9')
      | r2_hidden(k1_ordinal1(B_54),'#skF_9')
      | ~ r2_hidden(B_54,'#skF_9')
      | ~ v3_ordinal1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_231,plain,(
    ! [B_86] :
      ( r2_hidden(k1_ordinal1(B_86),'#skF_9')
      | ~ r2_hidden(B_86,'#skF_9')
      | ~ v3_ordinal1(B_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_94])).

tff(c_200,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,k3_tarski(B_79))
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ! [A_44] : r2_hidden(A_44,k1_ordinal1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_170,plain,(
    ! [B_72,A_73] :
      ( ~ r1_tarski(B_72,A_73)
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_174,plain,(
    ! [A_44] : ~ r1_tarski(k1_ordinal1(A_44),A_44) ),
    inference(resolution,[status(thm)],[c_68,c_170])).

tff(c_212,plain,(
    ! [B_79] : ~ r2_hidden(k1_ordinal1(k3_tarski(B_79)),B_79) ),
    inference(resolution,[status(thm)],[c_200,c_174])).

tff(c_239,plain,
    ( ~ r2_hidden(k3_tarski('#skF_9'),'#skF_9')
    | ~ v3_ordinal1(k3_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_231,c_212])).

tff(c_241,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_244,plain,(
    ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_244])).

tff(c_250,plain,(
    v3_ordinal1(k3_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_1484,plain,(
    ! [B_187,A_188] :
      ( r2_hidden(B_187,A_188)
      | B_187 = A_188
      | r2_hidden(A_188,B_187)
      | ~ v3_ordinal1(B_187)
      | ~ v3_ordinal1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_249,plain,(
    ~ r2_hidden(k3_tarski('#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_1627,plain,
    ( k3_tarski('#skF_9') = '#skF_9'
    | r2_hidden('#skF_9',k3_tarski('#skF_9'))
    | ~ v3_ordinal1(k3_tarski('#skF_9'))
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1484,c_249])).

tff(c_1845,plain,
    ( k3_tarski('#skF_9') = '#skF_9'
    | r2_hidden('#skF_9',k3_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_250,c_1627])).

tff(c_1846,plain,(
    r2_hidden('#skF_9',k3_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1845])).

tff(c_76,plain,(
    ! [B_51,A_50] :
      ( ~ r1_tarski(B_51,A_50)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1917,plain,(
    ~ r1_tarski(k3_tarski('#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1846,c_76])).

tff(c_96,plain,(
    ! [A_55] :
      ( v1_ordinal1(A_55)
      | ~ v3_ordinal1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_100,plain,(
    v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_96])).

tff(c_590,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_7'(A_127,B_128),A_127)
      | r1_tarski(k3_tarski(A_127),B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    ! [B_42,A_39] :
      ( r1_tarski(B_42,A_39)
      | ~ r2_hidden(B_42,A_39)
      | ~ v1_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10029,plain,(
    ! [A_408,B_409] :
      ( r1_tarski('#skF_7'(A_408,B_409),A_408)
      | ~ v1_ordinal1(A_408)
      | r1_tarski(k3_tarski(A_408),B_409) ) ),
    inference(resolution,[status(thm)],[c_590,c_58])).

tff(c_10047,plain,
    ( r1_tarski('#skF_7'('#skF_9','#skF_9'),'#skF_9')
    | ~ v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_10029,c_1917])).

tff(c_10067,plain,(
    r1_tarski('#skF_7'('#skF_9','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10047])).

tff(c_46,plain,(
    ! [A_32,B_33] :
      ( ~ r1_tarski('#skF_7'(A_32,B_33),B_33)
      | r1_tarski(k3_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10070,plain,(
    r1_tarski(k3_tarski('#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_10067,c_46])).

tff(c_10077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1917,c_10070])).

tff(c_10078,plain,(
    v3_ordinal1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_10082,plain,(
    ! [A_410] :
      ( v1_ordinal1(A_410)
      | ~ v3_ordinal1(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10089,plain,(
    v1_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_10078,c_10082])).

tff(c_10079,plain,(
    v4_ordinal1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( r2_hidden('#skF_10','#skF_9')
    | ~ v4_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10081,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10079,c_82])).

tff(c_56,plain,(
    ! [A_38] : k2_xboole_0(A_38,k1_tarski(A_38)) = k1_ordinal1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10586,plain,(
    ! [A_481,B_482] : k2_xboole_0(k3_tarski(A_481),k3_tarski(B_482)) = k3_tarski(k2_xboole_0(A_481,B_482)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24428,plain,(
    ! [A_797,A_798] : k3_tarski(k2_xboole_0(A_797,k1_tarski(A_798))) = k2_xboole_0(k3_tarski(A_797),A_798) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10586])).

tff(c_24552,plain,(
    ! [A_38] : k2_xboole_0(k3_tarski(A_38),A_38) = k3_tarski(k1_ordinal1(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_24428])).

tff(c_10439,plain,(
    ! [A_463,B_464] :
      ( r2_hidden('#skF_7'(A_463,B_464),A_463)
      | r1_tarski(k3_tarski(A_463),B_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28974,plain,(
    ! [A_864,B_865] :
      ( r1_tarski('#skF_7'(A_864,B_865),A_864)
      | ~ v1_ordinal1(A_864)
      | r1_tarski(k3_tarski(A_864),B_865) ) ),
    inference(resolution,[status(thm)],[c_10439,c_58])).

tff(c_29394,plain,(
    ! [A_874] :
      ( ~ v1_ordinal1(A_874)
      | r1_tarski(k3_tarski(A_874),A_874) ) ),
    inference(resolution,[status(thm)],[c_28974,c_46])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29413,plain,(
    ! [A_874] :
      ( k2_xboole_0(k3_tarski(A_874),A_874) = A_874
      | ~ v1_ordinal1(A_874) ) ),
    inference(resolution,[status(thm)],[c_29394,c_20])).

tff(c_29561,plain,(
    ! [A_876] :
      ( k3_tarski(k1_ordinal1(A_876)) = A_876
      | ~ v1_ordinal1(A_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24552,c_29413])).

tff(c_48,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_7'(A_32,B_33),A_32)
      | r1_tarski(k3_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k3_tarski(B_30))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10741,plain,(
    ! [A_488,B_489] :
      ( ~ r1_tarski('#skF_7'(A_488,B_489),B_489)
      | r1_tarski(k3_tarski(A_488),B_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28167,plain,(
    ! [A_856,B_857] :
      ( r1_tarski(k3_tarski(A_856),k3_tarski(B_857))
      | ~ r2_hidden('#skF_7'(A_856,k3_tarski(B_857)),B_857) ) ),
    inference(resolution,[status(thm)],[c_42,c_10741])).

tff(c_28313,plain,(
    ! [A_858] : r1_tarski(k3_tarski(A_858),k3_tarski(A_858)) ),
    inference(resolution,[status(thm)],[c_48,c_28167])).

tff(c_10122,plain,(
    ! [A_416] :
      ( k3_tarski(A_416) = A_416
      | ~ v4_ordinal1(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10130,plain,(
    k3_tarski('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_10079,c_10122])).

tff(c_10212,plain,(
    ! [A_433,B_434] :
      ( r1_tarski(A_433,k3_tarski(B_434))
      | ~ r2_hidden(A_433,B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10223,plain,(
    ! [A_433] :
      ( r1_tarski(A_433,'#skF_9')
      | ~ r2_hidden(A_433,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10130,c_10212])).

tff(c_10454,plain,(
    ! [B_464] :
      ( r1_tarski('#skF_7'('#skF_9',B_464),'#skF_9')
      | r1_tarski(k3_tarski('#skF_9'),B_464) ) ),
    inference(resolution,[status(thm)],[c_10439,c_10223])).

tff(c_10783,plain,(
    ! [B_491] :
      ( r1_tarski('#skF_7'('#skF_9',B_491),'#skF_9')
      | r1_tarski('#skF_9',B_491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10130,c_10454])).

tff(c_10786,plain,
    ( r1_tarski(k3_tarski('#skF_9'),'#skF_9')
    | r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_10783,c_46])).

tff(c_10791,plain,
    ( r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10130,c_10786])).

tff(c_10793,plain,(
    r1_tarski('#skF_9','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_10791])).

tff(c_72,plain,(
    ! [A_48] :
      ( v3_ordinal1(k1_ordinal1(A_48))
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11891,plain,(
    ! [B_539,A_540] :
      ( r2_hidden(B_539,A_540)
      | B_539 = A_540
      | r2_hidden(A_540,B_539)
      | ~ v3_ordinal1(B_539)
      | ~ v3_ordinal1(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_80,plain,
    ( ~ r2_hidden(k1_ordinal1('#skF_10'),'#skF_9')
    | ~ v4_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10112,plain,(
    ~ r2_hidden(k1_ordinal1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10079,c_80])).

tff(c_12080,plain,
    ( k1_ordinal1('#skF_10') = '#skF_9'
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_10'))
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11891,c_10112])).

tff(c_12354,plain,
    ( k1_ordinal1('#skF_10') = '#skF_9'
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12080])).

tff(c_12491,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_12354])).

tff(c_12494,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_12491])).

tff(c_12498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10078,c_12494])).

tff(c_12499,plain,
    ( r2_hidden('#skF_9',k1_ordinal1('#skF_10'))
    | k1_ordinal1('#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_12354])).

tff(c_12509,plain,(
    k1_ordinal1('#skF_10') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_12499])).

tff(c_13346,plain,(
    ! [A_564,A_565] : k3_tarski(k2_xboole_0(A_564,k1_tarski(A_565))) = k2_xboole_0(k3_tarski(A_564),A_565) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10586])).

tff(c_13431,plain,(
    ! [A_38] : k2_xboole_0(k3_tarski(A_38),A_38) = k3_tarski(k1_ordinal1(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_13346])).

tff(c_20341,plain,(
    ! [A_694,B_695] :
      ( r1_tarski('#skF_7'(A_694,B_695),A_694)
      | ~ v1_ordinal1(A_694)
      | r1_tarski(k3_tarski(A_694),B_695) ) ),
    inference(resolution,[status(thm)],[c_10439,c_58])).

tff(c_20392,plain,(
    ! [A_696] :
      ( ~ v1_ordinal1(A_696)
      | r1_tarski(k3_tarski(A_696),A_696) ) ),
    inference(resolution,[status(thm)],[c_20341,c_46])).

tff(c_20407,plain,(
    ! [A_696] :
      ( k2_xboole_0(k3_tarski(A_696),A_696) = A_696
      | ~ v1_ordinal1(A_696) ) ),
    inference(resolution,[status(thm)],[c_20392,c_20])).

tff(c_20496,plain,(
    ! [A_697] :
      ( k3_tarski(k1_ordinal1(A_697)) = A_697
      | ~ v1_ordinal1(A_697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13431,c_20407])).

tff(c_20691,plain,
    ( k3_tarski('#skF_9') = '#skF_10'
    | ~ v1_ordinal1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_12509,c_20496])).

tff(c_20709,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10089,c_10130,c_20691])).

tff(c_10196,plain,(
    ! [B_429,A_430] :
      ( ~ r1_tarski(B_429,A_430)
      | ~ r2_hidden(A_430,B_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10208,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_10081,c_10196])).

tff(c_20789,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20709,c_10208])).

tff(c_20844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10793,c_20789])).

tff(c_20845,plain,(
    r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_12499])).

tff(c_24,plain,(
    ! [C_25,A_10,D_28] :
      ( r2_hidden(C_25,k3_tarski(A_10))
      | ~ r2_hidden(D_28,A_10)
      | ~ r2_hidden(C_25,D_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21312,plain,(
    ! [C_706] :
      ( r2_hidden(C_706,k3_tarski(k1_ordinal1('#skF_10')))
      | ~ r2_hidden(C_706,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20845,c_24])).

tff(c_21432,plain,(
    ! [C_706] :
      ( ~ r1_tarski(k3_tarski(k1_ordinal1('#skF_10')),C_706)
      | ~ r2_hidden(C_706,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_21312,c_76])).

tff(c_28437,plain,(
    ~ r2_hidden(k3_tarski(k1_ordinal1('#skF_10')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_28313,c_21432])).

tff(c_29570,plain,
    ( ~ r2_hidden('#skF_10','#skF_9')
    | ~ v1_ordinal1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_29561,c_28437])).

tff(c_29816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10089,c_10081,c_29570])).

tff(c_29817,plain,(
    r1_tarski('#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_10791])).

tff(c_29818,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_10791])).

tff(c_29824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29817,c_29818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:42:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.87/5.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.87/5.48  
% 12.87/5.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.87/5.48  %$ r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_6 > #skF_8 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_5 > #skF_4
% 12.87/5.48  
% 12.87/5.48  %Foreground sorts:
% 12.87/5.48  
% 12.87/5.48  
% 12.87/5.48  %Background operators:
% 12.87/5.48  
% 12.87/5.48  
% 12.87/5.48  %Foreground operators:
% 12.87/5.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.87/5.48  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 12.87/5.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.87/5.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.87/5.48  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 12.87/5.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.87/5.48  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 12.87/5.48  tff('#skF_8', type, '#skF_8': $i > $i).
% 12.87/5.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.87/5.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.87/5.48  tff('#skF_10', type, '#skF_10': $i).
% 12.87/5.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.87/5.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.87/5.48  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 12.87/5.48  tff('#skF_9', type, '#skF_9': $i).
% 12.87/5.48  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 12.87/5.49  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 12.87/5.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.87/5.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.87/5.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.87/5.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.87/5.49  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 12.87/5.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.87/5.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.87/5.49  
% 12.87/5.51  tff(f_84, axiom, (![A]: (v4_ordinal1(A) <=> (A = k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_ordinal1)).
% 12.87/5.51  tff(f_126, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 12.87/5.51  tff(f_109, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 12.87/5.51  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 12.87/5.51  tff(f_86, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 12.87/5.51  tff(f_114, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 12.87/5.51  tff(f_101, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 12.87/5.51  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 12.87/5.51  tff(f_63, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 12.87/5.51  tff(f_80, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 12.87/5.51  tff(f_73, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 12.87/5.51  tff(f_56, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 12.87/5.51  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 12.87/5.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.87/5.51  tff(f_105, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 12.87/5.51  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 12.87/5.51  tff(c_116, plain, (![A_59]: (v4_ordinal1(A_59) | k3_tarski(A_59)!=A_59)), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.87/5.51  tff(c_84, plain, (v3_ordinal1('#skF_10') | ~v4_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.87/5.51  tff(c_95, plain, (~v4_ordinal1('#skF_9')), inference(splitLeft, [status(thm)], [c_84])).
% 12.87/5.51  tff(c_120, plain, (k3_tarski('#skF_9')!='#skF_9'), inference(resolution, [status(thm)], [c_116, c_95])).
% 12.87/5.51  tff(c_78, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.87/5.51  tff(c_74, plain, (![A_49]: (v3_ordinal1(k3_tarski(A_49)) | ~v3_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.87/5.51  tff(c_94, plain, (![B_54]: (v4_ordinal1('#skF_9') | r2_hidden(k1_ordinal1(B_54), '#skF_9') | ~r2_hidden(B_54, '#skF_9') | ~v3_ordinal1(B_54))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.87/5.51  tff(c_231, plain, (![B_86]: (r2_hidden(k1_ordinal1(B_86), '#skF_9') | ~r2_hidden(B_86, '#skF_9') | ~v3_ordinal1(B_86))), inference(negUnitSimplification, [status(thm)], [c_95, c_94])).
% 12.87/5.51  tff(c_200, plain, (![A_78, B_79]: (r1_tarski(A_78, k3_tarski(B_79)) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.87/5.51  tff(c_68, plain, (![A_44]: (r2_hidden(A_44, k1_ordinal1(A_44)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.87/5.51  tff(c_170, plain, (![B_72, A_73]: (~r1_tarski(B_72, A_73) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.87/5.51  tff(c_174, plain, (![A_44]: (~r1_tarski(k1_ordinal1(A_44), A_44))), inference(resolution, [status(thm)], [c_68, c_170])).
% 12.87/5.51  tff(c_212, plain, (![B_79]: (~r2_hidden(k1_ordinal1(k3_tarski(B_79)), B_79))), inference(resolution, [status(thm)], [c_200, c_174])).
% 12.87/5.51  tff(c_239, plain, (~r2_hidden(k3_tarski('#skF_9'), '#skF_9') | ~v3_ordinal1(k3_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_231, c_212])).
% 12.87/5.51  tff(c_241, plain, (~v3_ordinal1(k3_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_239])).
% 12.87/5.51  tff(c_244, plain, (~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_241])).
% 12.87/5.51  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_244])).
% 12.87/5.51  tff(c_250, plain, (v3_ordinal1(k3_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_239])).
% 12.87/5.51  tff(c_1484, plain, (![B_187, A_188]: (r2_hidden(B_187, A_188) | B_187=A_188 | r2_hidden(A_188, B_187) | ~v3_ordinal1(B_187) | ~v3_ordinal1(A_188))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.87/5.51  tff(c_249, plain, (~r2_hidden(k3_tarski('#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_239])).
% 12.87/5.51  tff(c_1627, plain, (k3_tarski('#skF_9')='#skF_9' | r2_hidden('#skF_9', k3_tarski('#skF_9')) | ~v3_ordinal1(k3_tarski('#skF_9')) | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_1484, c_249])).
% 12.87/5.51  tff(c_1845, plain, (k3_tarski('#skF_9')='#skF_9' | r2_hidden('#skF_9', k3_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_250, c_1627])).
% 12.87/5.51  tff(c_1846, plain, (r2_hidden('#skF_9', k3_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_120, c_1845])).
% 12.87/5.51  tff(c_76, plain, (![B_51, A_50]: (~r1_tarski(B_51, A_50) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.87/5.51  tff(c_1917, plain, (~r1_tarski(k3_tarski('#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_1846, c_76])).
% 12.87/5.51  tff(c_96, plain, (![A_55]: (v1_ordinal1(A_55) | ~v3_ordinal1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.87/5.51  tff(c_100, plain, (v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_96])).
% 12.87/5.51  tff(c_590, plain, (![A_127, B_128]: (r2_hidden('#skF_7'(A_127, B_128), A_127) | r1_tarski(k3_tarski(A_127), B_128))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.87/5.51  tff(c_58, plain, (![B_42, A_39]: (r1_tarski(B_42, A_39) | ~r2_hidden(B_42, A_39) | ~v1_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.87/5.51  tff(c_10029, plain, (![A_408, B_409]: (r1_tarski('#skF_7'(A_408, B_409), A_408) | ~v1_ordinal1(A_408) | r1_tarski(k3_tarski(A_408), B_409))), inference(resolution, [status(thm)], [c_590, c_58])).
% 12.87/5.51  tff(c_10047, plain, (r1_tarski('#skF_7'('#skF_9', '#skF_9'), '#skF_9') | ~v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_10029, c_1917])).
% 12.87/5.51  tff(c_10067, plain, (r1_tarski('#skF_7'('#skF_9', '#skF_9'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10047])).
% 12.87/5.51  tff(c_46, plain, (![A_32, B_33]: (~r1_tarski('#skF_7'(A_32, B_33), B_33) | r1_tarski(k3_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.87/5.51  tff(c_10070, plain, (r1_tarski(k3_tarski('#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_10067, c_46])).
% 12.87/5.51  tff(c_10077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1917, c_10070])).
% 12.87/5.51  tff(c_10078, plain, (v3_ordinal1('#skF_10')), inference(splitRight, [status(thm)], [c_84])).
% 12.87/5.51  tff(c_10082, plain, (![A_410]: (v1_ordinal1(A_410) | ~v3_ordinal1(A_410))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.87/5.51  tff(c_10089, plain, (v1_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_10078, c_10082])).
% 12.87/5.51  tff(c_10079, plain, (v4_ordinal1('#skF_9')), inference(splitRight, [status(thm)], [c_84])).
% 12.87/5.51  tff(c_82, plain, (r2_hidden('#skF_10', '#skF_9') | ~v4_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.87/5.51  tff(c_10081, plain, (r2_hidden('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10079, c_82])).
% 12.87/5.51  tff(c_56, plain, (![A_38]: (k2_xboole_0(A_38, k1_tarski(A_38))=k1_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.87/5.51  tff(c_44, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.87/5.51  tff(c_10586, plain, (![A_481, B_482]: (k2_xboole_0(k3_tarski(A_481), k3_tarski(B_482))=k3_tarski(k2_xboole_0(A_481, B_482)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.87/5.51  tff(c_24428, plain, (![A_797, A_798]: (k3_tarski(k2_xboole_0(A_797, k1_tarski(A_798)))=k2_xboole_0(k3_tarski(A_797), A_798))), inference(superposition, [status(thm), theory('equality')], [c_44, c_10586])).
% 12.87/5.51  tff(c_24552, plain, (![A_38]: (k2_xboole_0(k3_tarski(A_38), A_38)=k3_tarski(k1_ordinal1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_24428])).
% 12.87/5.51  tff(c_10439, plain, (![A_463, B_464]: (r2_hidden('#skF_7'(A_463, B_464), A_463) | r1_tarski(k3_tarski(A_463), B_464))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.87/5.51  tff(c_28974, plain, (![A_864, B_865]: (r1_tarski('#skF_7'(A_864, B_865), A_864) | ~v1_ordinal1(A_864) | r1_tarski(k3_tarski(A_864), B_865))), inference(resolution, [status(thm)], [c_10439, c_58])).
% 12.87/5.51  tff(c_29394, plain, (![A_874]: (~v1_ordinal1(A_874) | r1_tarski(k3_tarski(A_874), A_874))), inference(resolution, [status(thm)], [c_28974, c_46])).
% 12.87/5.51  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.87/5.51  tff(c_29413, plain, (![A_874]: (k2_xboole_0(k3_tarski(A_874), A_874)=A_874 | ~v1_ordinal1(A_874))), inference(resolution, [status(thm)], [c_29394, c_20])).
% 12.87/5.51  tff(c_29561, plain, (![A_876]: (k3_tarski(k1_ordinal1(A_876))=A_876 | ~v1_ordinal1(A_876))), inference(demodulation, [status(thm), theory('equality')], [c_24552, c_29413])).
% 12.87/5.51  tff(c_48, plain, (![A_32, B_33]: (r2_hidden('#skF_7'(A_32, B_33), A_32) | r1_tarski(k3_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.87/5.51  tff(c_42, plain, (![A_29, B_30]: (r1_tarski(A_29, k3_tarski(B_30)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.87/5.51  tff(c_10741, plain, (![A_488, B_489]: (~r1_tarski('#skF_7'(A_488, B_489), B_489) | r1_tarski(k3_tarski(A_488), B_489))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.87/5.51  tff(c_28167, plain, (![A_856, B_857]: (r1_tarski(k3_tarski(A_856), k3_tarski(B_857)) | ~r2_hidden('#skF_7'(A_856, k3_tarski(B_857)), B_857))), inference(resolution, [status(thm)], [c_42, c_10741])).
% 12.87/5.51  tff(c_28313, plain, (![A_858]: (r1_tarski(k3_tarski(A_858), k3_tarski(A_858)))), inference(resolution, [status(thm)], [c_48, c_28167])).
% 12.87/5.51  tff(c_10122, plain, (![A_416]: (k3_tarski(A_416)=A_416 | ~v4_ordinal1(A_416))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.87/5.51  tff(c_10130, plain, (k3_tarski('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_10079, c_10122])).
% 12.87/5.51  tff(c_10212, plain, (![A_433, B_434]: (r1_tarski(A_433, k3_tarski(B_434)) | ~r2_hidden(A_433, B_434))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.87/5.51  tff(c_10223, plain, (![A_433]: (r1_tarski(A_433, '#skF_9') | ~r2_hidden(A_433, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10130, c_10212])).
% 12.87/5.51  tff(c_10454, plain, (![B_464]: (r1_tarski('#skF_7'('#skF_9', B_464), '#skF_9') | r1_tarski(k3_tarski('#skF_9'), B_464))), inference(resolution, [status(thm)], [c_10439, c_10223])).
% 12.87/5.51  tff(c_10783, plain, (![B_491]: (r1_tarski('#skF_7'('#skF_9', B_491), '#skF_9') | r1_tarski('#skF_9', B_491))), inference(demodulation, [status(thm), theory('equality')], [c_10130, c_10454])).
% 12.87/5.51  tff(c_10786, plain, (r1_tarski(k3_tarski('#skF_9'), '#skF_9') | r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_10783, c_46])).
% 12.87/5.51  tff(c_10791, plain, (r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10130, c_10786])).
% 12.87/5.51  tff(c_10793, plain, (r1_tarski('#skF_9', '#skF_9')), inference(splitLeft, [status(thm)], [c_10791])).
% 12.87/5.51  tff(c_72, plain, (![A_48]: (v3_ordinal1(k1_ordinal1(A_48)) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.87/5.51  tff(c_11891, plain, (![B_539, A_540]: (r2_hidden(B_539, A_540) | B_539=A_540 | r2_hidden(A_540, B_539) | ~v3_ordinal1(B_539) | ~v3_ordinal1(A_540))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.87/5.51  tff(c_80, plain, (~r2_hidden(k1_ordinal1('#skF_10'), '#skF_9') | ~v4_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.87/5.51  tff(c_10112, plain, (~r2_hidden(k1_ordinal1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_10079, c_80])).
% 12.87/5.51  tff(c_12080, plain, (k1_ordinal1('#skF_10')='#skF_9' | r2_hidden('#skF_9', k1_ordinal1('#skF_10')) | ~v3_ordinal1(k1_ordinal1('#skF_10')) | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_11891, c_10112])).
% 12.87/5.51  tff(c_12354, plain, (k1_ordinal1('#skF_10')='#skF_9' | r2_hidden('#skF_9', k1_ordinal1('#skF_10')) | ~v3_ordinal1(k1_ordinal1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_12080])).
% 12.87/5.51  tff(c_12491, plain, (~v3_ordinal1(k1_ordinal1('#skF_10'))), inference(splitLeft, [status(thm)], [c_12354])).
% 12.87/5.51  tff(c_12494, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_12491])).
% 12.87/5.51  tff(c_12498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10078, c_12494])).
% 12.87/5.51  tff(c_12499, plain, (r2_hidden('#skF_9', k1_ordinal1('#skF_10')) | k1_ordinal1('#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_12354])).
% 12.87/5.51  tff(c_12509, plain, (k1_ordinal1('#skF_10')='#skF_9'), inference(splitLeft, [status(thm)], [c_12499])).
% 12.87/5.51  tff(c_13346, plain, (![A_564, A_565]: (k3_tarski(k2_xboole_0(A_564, k1_tarski(A_565)))=k2_xboole_0(k3_tarski(A_564), A_565))), inference(superposition, [status(thm), theory('equality')], [c_44, c_10586])).
% 12.87/5.51  tff(c_13431, plain, (![A_38]: (k2_xboole_0(k3_tarski(A_38), A_38)=k3_tarski(k1_ordinal1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_13346])).
% 12.87/5.51  tff(c_20341, plain, (![A_694, B_695]: (r1_tarski('#skF_7'(A_694, B_695), A_694) | ~v1_ordinal1(A_694) | r1_tarski(k3_tarski(A_694), B_695))), inference(resolution, [status(thm)], [c_10439, c_58])).
% 12.87/5.51  tff(c_20392, plain, (![A_696]: (~v1_ordinal1(A_696) | r1_tarski(k3_tarski(A_696), A_696))), inference(resolution, [status(thm)], [c_20341, c_46])).
% 12.87/5.51  tff(c_20407, plain, (![A_696]: (k2_xboole_0(k3_tarski(A_696), A_696)=A_696 | ~v1_ordinal1(A_696))), inference(resolution, [status(thm)], [c_20392, c_20])).
% 12.87/5.51  tff(c_20496, plain, (![A_697]: (k3_tarski(k1_ordinal1(A_697))=A_697 | ~v1_ordinal1(A_697))), inference(demodulation, [status(thm), theory('equality')], [c_13431, c_20407])).
% 12.87/5.51  tff(c_20691, plain, (k3_tarski('#skF_9')='#skF_10' | ~v1_ordinal1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_12509, c_20496])).
% 12.87/5.51  tff(c_20709, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10089, c_10130, c_20691])).
% 12.87/5.51  tff(c_10196, plain, (![B_429, A_430]: (~r1_tarski(B_429, A_430) | ~r2_hidden(A_430, B_429))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.87/5.51  tff(c_10208, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_10081, c_10196])).
% 12.87/5.51  tff(c_20789, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20709, c_10208])).
% 12.87/5.51  tff(c_20844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10793, c_20789])).
% 12.87/5.51  tff(c_20845, plain, (r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(splitRight, [status(thm)], [c_12499])).
% 12.87/5.51  tff(c_24, plain, (![C_25, A_10, D_28]: (r2_hidden(C_25, k3_tarski(A_10)) | ~r2_hidden(D_28, A_10) | ~r2_hidden(C_25, D_28))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.87/5.51  tff(c_21312, plain, (![C_706]: (r2_hidden(C_706, k3_tarski(k1_ordinal1('#skF_10'))) | ~r2_hidden(C_706, '#skF_9'))), inference(resolution, [status(thm)], [c_20845, c_24])).
% 12.87/5.51  tff(c_21432, plain, (![C_706]: (~r1_tarski(k3_tarski(k1_ordinal1('#skF_10')), C_706) | ~r2_hidden(C_706, '#skF_9'))), inference(resolution, [status(thm)], [c_21312, c_76])).
% 12.87/5.51  tff(c_28437, plain, (~r2_hidden(k3_tarski(k1_ordinal1('#skF_10')), '#skF_9')), inference(resolution, [status(thm)], [c_28313, c_21432])).
% 12.87/5.51  tff(c_29570, plain, (~r2_hidden('#skF_10', '#skF_9') | ~v1_ordinal1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_29561, c_28437])).
% 12.87/5.51  tff(c_29816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10089, c_10081, c_29570])).
% 12.87/5.51  tff(c_29817, plain, (r1_tarski('#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_10791])).
% 12.87/5.51  tff(c_29818, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_10791])).
% 12.87/5.51  tff(c_29824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29817, c_29818])).
% 12.87/5.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.87/5.51  
% 12.87/5.51  Inference rules
% 12.87/5.51  ----------------------
% 12.87/5.51  #Ref     : 0
% 12.87/5.51  #Sup     : 7022
% 12.87/5.51  #Fact    : 24
% 12.87/5.51  #Define  : 0
% 12.87/5.51  #Split   : 23
% 12.87/5.51  #Chain   : 0
% 12.87/5.51  #Close   : 0
% 12.87/5.51  
% 12.87/5.51  Ordering : KBO
% 12.87/5.51  
% 12.87/5.51  Simplification rules
% 12.87/5.51  ----------------------
% 12.87/5.51  #Subsume      : 1658
% 12.87/5.51  #Demod        : 1982
% 12.87/5.51  #Tautology    : 538
% 12.87/5.51  #SimpNegUnit  : 40
% 12.87/5.51  #BackRed      : 108
% 12.87/5.51  
% 12.87/5.51  #Partial instantiations: 0
% 12.87/5.51  #Strategies tried      : 1
% 12.87/5.51  
% 12.87/5.51  Timing (in seconds)
% 12.87/5.51  ----------------------
% 12.87/5.51  Preprocessing        : 0.41
% 12.87/5.51  Parsing              : 0.20
% 12.87/5.51  CNF conversion       : 0.04
% 12.87/5.51  Main loop            : 4.35
% 12.87/5.51  Inferencing          : 1.00
% 12.87/5.51  Reduction            : 1.52
% 12.87/5.51  Demodulation         : 1.00
% 12.87/5.51  BG Simplification    : 0.13
% 12.87/5.51  Subsumption          : 1.35
% 12.87/5.51  Abstraction          : 0.16
% 12.87/5.51  MUC search           : 0.00
% 12.87/5.51  Cooper               : 0.00
% 12.87/5.51  Total                : 4.81
% 12.87/5.51  Index Insertion      : 0.00
% 12.87/5.51  Index Deletion       : 0.00
% 12.87/5.51  Index Matching       : 0.00
% 12.87/5.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
