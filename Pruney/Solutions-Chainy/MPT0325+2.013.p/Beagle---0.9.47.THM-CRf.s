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
% DateTime   : Thu Dec  3 09:54:22 EST 2020

% Result     : Theorem 10.75s
% Output     : CNFRefutation 10.75s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 269 expanded)
%              Number of leaves         :   27 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 497 expanded)
%              Number of equality atoms :   59 ( 145 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( ~ r1_xboole_0(A_23,B_24)
      | r1_xboole_0(k2_zfmisc_1(A_23,C_25),k2_zfmisc_1(B_24,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_95,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_95])).

tff(c_114,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [A_47,B_48] :
      ( ~ r1_xboole_0(A_47,B_48)
      | v1_xboole_0(k3_xboole_0(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_187,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_125])).

tff(c_278,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_290,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_278])).

tff(c_301,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_290])).

tff(c_371,plain,(
    ! [C_75,D_76,A_77,B_78] :
      ( ~ r1_xboole_0(C_75,D_76)
      | r1_xboole_0(k2_zfmisc_1(A_77,C_75),k2_zfmisc_1(B_78,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_383,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_371,c_278])).

tff(c_395,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_383])).

tff(c_1078,plain,(
    ! [A_101,C_102,B_103,D_104] : k3_xboole_0(k2_zfmisc_1(A_101,C_102),k2_zfmisc_1(B_103,D_104)) = k2_zfmisc_1(k3_xboole_0(A_101,B_103),k3_xboole_0(C_102,D_104)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1120,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_105])).

tff(c_30,plain,(
    ! [C_29,A_27,B_28,D_30] :
      ( C_29 = A_27
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | k2_zfmisc_1(C_29,D_30) != k2_zfmisc_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1354,plain,(
    ! [C_29,D_30] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_29
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0
      | k2_zfmisc_1(C_29,D_30) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_30])).

tff(c_1372,plain,(
    ! [C_29,D_30] :
      ( k3_xboole_0('#skF_3','#skF_5') = C_29
      | k2_zfmisc_1(C_29,D_30) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_395,c_1354])).

tff(c_7632,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1372])).

tff(c_45,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_18])).

tff(c_7925,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7632,c_60])).

tff(c_7986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_7925])).

tff(c_7987,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7991,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7987,c_12])).

tff(c_7995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_7991])).

tff(c_7996,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_7997,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_7998,plain,(
    ! [A_315,B_316] :
      ( k3_xboole_0(A_315,B_316) = A_315
      | ~ r1_tarski(A_315,B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8008,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7997,c_7998])).

tff(c_8048,plain,(
    ! [A_321,B_322,C_323] :
      ( ~ r1_xboole_0(A_321,B_322)
      | ~ r2_hidden(C_323,k3_xboole_0(A_321,B_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8054,plain,(
    ! [C_323] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_323,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8008,c_8048])).

tff(c_8066,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8054])).

tff(c_8069,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_8066])).

tff(c_8071,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8008,c_8069])).

tff(c_24,plain,(
    ! [C_25,D_26,A_23,B_24] :
      ( ~ r1_xboole_0(C_25,D_26)
      | r1_xboole_0(k2_zfmisc_1(A_23,C_25),k2_zfmisc_1(B_24,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8041,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_20])).

tff(c_8072,plain,(
    ! [A_324,B_325] :
      ( r2_hidden('#skF_2'(A_324,B_325),k3_xboole_0(A_324,B_325))
      | r1_xboole_0(A_324,B_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8121,plain,(
    ! [A_326,B_327] :
      ( ~ v1_xboole_0(k3_xboole_0(A_326,B_327))
      | r1_xboole_0(A_326,B_327) ) ),
    inference(resolution,[status(thm)],[c_8072,c_4])).

tff(c_8124,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8041,c_8121])).

tff(c_8232,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8124])).

tff(c_8139,plain,(
    ! [A_328,B_329] :
      ( ~ r1_xboole_0(A_328,B_329)
      | v1_xboole_0(k3_xboole_0(A_328,B_329)) ) ),
    inference(resolution,[status(thm)],[c_6,c_8048])).

tff(c_8148,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8041,c_8139])).

tff(c_8311,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_8232,c_8148])).

tff(c_8326,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_8311])).

tff(c_8338,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_8326])).

tff(c_9158,plain,(
    ! [A_375,C_376,B_377,D_378] : k3_xboole_0(k2_zfmisc_1(A_375,C_376),k2_zfmisc_1(B_377,D_378)) = k2_zfmisc_1(k3_xboole_0(A_375,B_377),k3_xboole_0(C_376,D_378)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9209,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_5'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9158,c_8041])).

tff(c_9251,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8008,c_9209])).

tff(c_28,plain,(
    ! [D_30,B_28,A_27,C_29] :
      ( D_30 = B_28
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | k2_zfmisc_1(C_29,D_30) != k2_zfmisc_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9266,plain,(
    ! [D_30,C_29] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_30
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1(C_29,D_30) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9251,c_28])).

tff(c_9289,plain,(
    ! [D_30,C_29] :
      ( k3_xboole_0('#skF_4','#skF_6') = D_30
      | k2_zfmisc_1(C_29,D_30) != k2_zfmisc_1('#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8071,c_8338,c_9266])).

tff(c_23110,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9289])).

tff(c_23432,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_23110,c_60])).

tff(c_23479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7996,c_23432])).

tff(c_23481,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8124])).

tff(c_23490,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23481,c_12])).

tff(c_23494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_23490])).

tff(c_23497,plain,(
    ! [C_756] : ~ r2_hidden(C_756,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8054])).

tff(c_23502,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_23497])).

tff(c_23506,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_23502,c_12])).

tff(c_23510,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23506,c_34])).

tff(c_23496,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8054])).

tff(c_8065,plain,(
    ! [A_321,B_322] :
      ( ~ r1_xboole_0(A_321,B_322)
      | v1_xboole_0(k3_xboole_0(A_321,B_322)) ) ),
    inference(resolution,[status(thm)],[c_6,c_8048])).

tff(c_23638,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8041,c_8065])).

tff(c_23808,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_23638])).

tff(c_23817,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_23808])).

tff(c_23824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23496,c_23817])).

tff(c_23825,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_23638])).

tff(c_23509,plain,(
    ! [A_9] :
      ( A_9 = '#skF_3'
      | ~ v1_xboole_0(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23506,c_12])).

tff(c_23829,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_23825,c_23509])).

tff(c_23833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23510,c_23829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.75/4.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.75/4.45  
% 10.75/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.75/4.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 10.75/4.45  
% 10.75/4.45  %Foreground sorts:
% 10.75/4.45  
% 10.75/4.45  
% 10.75/4.45  %Background operators:
% 10.75/4.45  
% 10.75/4.45  
% 10.75/4.45  %Foreground operators:
% 10.75/4.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.75/4.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.75/4.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.75/4.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.75/4.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.75/4.45  tff('#skF_5', type, '#skF_5': $i).
% 10.75/4.45  tff('#skF_6', type, '#skF_6': $i).
% 10.75/4.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.75/4.45  tff('#skF_3', type, '#skF_3': $i).
% 10.75/4.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.75/4.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.75/4.45  tff('#skF_4', type, '#skF_4': $i).
% 10.75/4.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.75/4.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.75/4.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.75/4.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.75/4.45  
% 10.75/4.47  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.75/4.47  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 10.75/4.47  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.75/4.47  tff(f_69, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 10.75/4.47  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.75/4.47  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.75/4.47  tff(f_63, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 10.75/4.47  tff(f_79, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 10.75/4.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.75/4.47  tff(f_57, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.75/4.47  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.75/4.47  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.75/4.47  tff(c_34, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.75/4.47  tff(c_32, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.75/4.47  tff(c_94, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 10.75/4.47  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.75/4.47  tff(c_26, plain, (![A_23, B_24, C_25, D_26]: (~r1_xboole_0(A_23, B_24) | r1_xboole_0(k2_zfmisc_1(A_23, C_25), k2_zfmisc_1(B_24, D_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.75/4.47  tff(c_36, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.75/4.47  tff(c_95, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.75/4.47  tff(c_105, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_95])).
% 10.75/4.47  tff(c_114, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/4.47  tff(c_125, plain, (![A_47, B_48]: (~r1_xboole_0(A_47, B_48) | v1_xboole_0(k3_xboole_0(A_47, B_48)))), inference(resolution, [status(thm)], [c_6, c_114])).
% 10.75/4.47  tff(c_187, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_125])).
% 10.75/4.47  tff(c_278, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_187])).
% 10.75/4.47  tff(c_290, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_278])).
% 10.75/4.47  tff(c_301, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_290])).
% 10.75/4.47  tff(c_371, plain, (![C_75, D_76, A_77, B_78]: (~r1_xboole_0(C_75, D_76) | r1_xboole_0(k2_zfmisc_1(A_77, C_75), k2_zfmisc_1(B_78, D_76)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.75/4.47  tff(c_383, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_371, c_278])).
% 10.75/4.47  tff(c_395, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_383])).
% 10.75/4.47  tff(c_1078, plain, (![A_101, C_102, B_103, D_104]: (k3_xboole_0(k2_zfmisc_1(A_101, C_102), k2_zfmisc_1(B_103, D_104))=k2_zfmisc_1(k3_xboole_0(A_101, B_103), k3_xboole_0(C_102, D_104)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.75/4.47  tff(c_1120, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1078, c_105])).
% 10.75/4.47  tff(c_30, plain, (![C_29, A_27, B_28, D_30]: (C_29=A_27 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | k2_zfmisc_1(C_29, D_30)!=k2_zfmisc_1(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.75/4.47  tff(c_1354, plain, (![C_29, D_30]: (k3_xboole_0('#skF_3', '#skF_5')=C_29 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k2_zfmisc_1(C_29, D_30)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1120, c_30])).
% 10.75/4.47  tff(c_1372, plain, (![C_29, D_30]: (k3_xboole_0('#skF_3', '#skF_5')=C_29 | k2_zfmisc_1(C_29, D_30)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_301, c_395, c_1354])).
% 10.75/4.47  tff(c_7632, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1372])).
% 10.75/4.47  tff(c_45, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.75/4.47  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.75/4.47  tff(c_60, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_45, c_18])).
% 10.75/4.47  tff(c_7925, plain, (r1_tarski('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7632, c_60])).
% 10.75/4.47  tff(c_7986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_7925])).
% 10.75/4.47  tff(c_7987, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_187])).
% 10.75/4.47  tff(c_12, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.75/4.47  tff(c_7991, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_7987, c_12])).
% 10.75/4.47  tff(c_7995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_7991])).
% 10.75/4.47  tff(c_7996, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 10.75/4.47  tff(c_7997, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 10.75/4.47  tff(c_7998, plain, (![A_315, B_316]: (k3_xboole_0(A_315, B_316)=A_315 | ~r1_tarski(A_315, B_316))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.75/4.47  tff(c_8008, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_7997, c_7998])).
% 10.75/4.47  tff(c_8048, plain, (![A_321, B_322, C_323]: (~r1_xboole_0(A_321, B_322) | ~r2_hidden(C_323, k3_xboole_0(A_321, B_322)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/4.47  tff(c_8054, plain, (![C_323]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_323, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8008, c_8048])).
% 10.75/4.47  tff(c_8066, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_8054])).
% 10.75/4.47  tff(c_8069, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_8066])).
% 10.75/4.47  tff(c_8071, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8008, c_8069])).
% 10.75/4.47  tff(c_24, plain, (![C_25, D_26, A_23, B_24]: (~r1_xboole_0(C_25, D_26) | r1_xboole_0(k2_zfmisc_1(A_23, C_25), k2_zfmisc_1(B_24, D_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.75/4.47  tff(c_20, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.75/4.47  tff(c_8041, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_20])).
% 10.75/4.47  tff(c_8072, plain, (![A_324, B_325]: (r2_hidden('#skF_2'(A_324, B_325), k3_xboole_0(A_324, B_325)) | r1_xboole_0(A_324, B_325))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/4.47  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.75/4.47  tff(c_8121, plain, (![A_326, B_327]: (~v1_xboole_0(k3_xboole_0(A_326, B_327)) | r1_xboole_0(A_326, B_327))), inference(resolution, [status(thm)], [c_8072, c_4])).
% 10.75/4.47  tff(c_8124, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8041, c_8121])).
% 10.75/4.47  tff(c_8232, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_8124])).
% 10.75/4.47  tff(c_8139, plain, (![A_328, B_329]: (~r1_xboole_0(A_328, B_329) | v1_xboole_0(k3_xboole_0(A_328, B_329)))), inference(resolution, [status(thm)], [c_6, c_8048])).
% 10.75/4.47  tff(c_8148, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8041, c_8139])).
% 10.75/4.47  tff(c_8311, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_8232, c_8148])).
% 10.75/4.47  tff(c_8326, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_8311])).
% 10.75/4.47  tff(c_8338, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_8326])).
% 10.75/4.47  tff(c_9158, plain, (![A_375, C_376, B_377, D_378]: (k3_xboole_0(k2_zfmisc_1(A_375, C_376), k2_zfmisc_1(B_377, D_378))=k2_zfmisc_1(k3_xboole_0(A_375, B_377), k3_xboole_0(C_376, D_378)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.75/4.47  tff(c_9209, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_5'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9158, c_8041])).
% 10.75/4.47  tff(c_9251, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8008, c_9209])).
% 10.75/4.47  tff(c_28, plain, (![D_30, B_28, A_27, C_29]: (D_30=B_28 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | k2_zfmisc_1(C_29, D_30)!=k2_zfmisc_1(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.75/4.47  tff(c_9266, plain, (![D_30, C_29]: (k3_xboole_0('#skF_4', '#skF_6')=D_30 | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1(C_29, D_30)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9251, c_28])).
% 10.75/4.47  tff(c_9289, plain, (![D_30, C_29]: (k3_xboole_0('#skF_4', '#skF_6')=D_30 | k2_zfmisc_1(C_29, D_30)!=k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_8071, c_8338, c_9266])).
% 10.75/4.47  tff(c_23110, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_9289])).
% 10.75/4.47  tff(c_23432, plain, (r1_tarski('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_23110, c_60])).
% 10.75/4.47  tff(c_23479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7996, c_23432])).
% 10.75/4.47  tff(c_23481, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_8124])).
% 10.75/4.47  tff(c_23490, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_23481, c_12])).
% 10.75/4.47  tff(c_23494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_23490])).
% 10.75/4.47  tff(c_23497, plain, (![C_756]: (~r2_hidden(C_756, '#skF_3'))), inference(splitRight, [status(thm)], [c_8054])).
% 10.75/4.47  tff(c_23502, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_23497])).
% 10.75/4.47  tff(c_23506, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_23502, c_12])).
% 10.75/4.47  tff(c_23510, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23506, c_34])).
% 10.75/4.47  tff(c_23496, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_8054])).
% 10.75/4.47  tff(c_8065, plain, (![A_321, B_322]: (~r1_xboole_0(A_321, B_322) | v1_xboole_0(k3_xboole_0(A_321, B_322)))), inference(resolution, [status(thm)], [c_6, c_8048])).
% 10.75/4.47  tff(c_23638, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8041, c_8065])).
% 10.75/4.47  tff(c_23808, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_23638])).
% 10.75/4.47  tff(c_23817, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_23808])).
% 10.75/4.47  tff(c_23824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23496, c_23817])).
% 10.75/4.47  tff(c_23825, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_23638])).
% 10.75/4.47  tff(c_23509, plain, (![A_9]: (A_9='#skF_3' | ~v1_xboole_0(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_23506, c_12])).
% 10.75/4.47  tff(c_23829, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_23825, c_23509])).
% 10.75/4.47  tff(c_23833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23510, c_23829])).
% 10.75/4.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.75/4.47  
% 10.75/4.47  Inference rules
% 10.75/4.47  ----------------------
% 10.75/4.47  #Ref     : 7
% 10.75/4.47  #Sup     : 7216
% 10.75/4.47  #Fact    : 0
% 10.75/4.47  #Define  : 0
% 10.75/4.47  #Split   : 8
% 10.75/4.47  #Chain   : 0
% 10.75/4.47  #Close   : 0
% 10.75/4.47  
% 10.75/4.47  Ordering : KBO
% 10.75/4.47  
% 10.75/4.47  Simplification rules
% 10.75/4.47  ----------------------
% 10.75/4.47  #Subsume      : 2647
% 10.75/4.47  #Demod        : 4085
% 10.75/4.47  #Tautology    : 1347
% 10.75/4.47  #SimpNegUnit  : 281
% 10.75/4.47  #BackRed      : 26
% 10.75/4.47  
% 10.75/4.47  #Partial instantiations: 0
% 10.75/4.47  #Strategies tried      : 1
% 10.75/4.47  
% 10.75/4.47  Timing (in seconds)
% 10.75/4.47  ----------------------
% 10.93/4.47  Preprocessing        : 0.36
% 10.93/4.47  Parsing              : 0.20
% 10.93/4.47  CNF conversion       : 0.02
% 10.93/4.47  Main loop            : 3.23
% 10.93/4.47  Inferencing          : 0.64
% 10.93/4.47  Reduction            : 1.59
% 10.93/4.47  Demodulation         : 1.31
% 10.93/4.47  BG Simplification    : 0.08
% 10.93/4.47  Subsumption          : 0.68
% 10.93/4.47  Abstraction          : 0.11
% 10.93/4.47  MUC search           : 0.00
% 10.93/4.47  Cooper               : 0.00
% 10.93/4.47  Total                : 3.64
% 10.93/4.47  Index Insertion      : 0.00
% 10.93/4.47  Index Deletion       : 0.00
% 10.93/4.47  Index Matching       : 0.00
% 10.93/4.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
