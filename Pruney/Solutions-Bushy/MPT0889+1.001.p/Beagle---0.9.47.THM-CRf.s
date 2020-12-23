%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:01 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 923 expanded)
%              Number of leaves         :   32 ( 303 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 (2724 expanded)
%              Number of equality atoms :  100 ( 869 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
            & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
            & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_82,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,
    ( r1_tarski('#skF_2',k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
    | r1_tarski('#skF_2',k3_zfmisc_1('#skF_3','#skF_4','#skF_2'))
    | r1_tarski('#skF_2',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_97,plain,(
    r1_tarski('#skF_2',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_18,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_122,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_136,plain,(
    ! [A_73,B_74,A_75] :
      ( m1_subset_1(A_73,B_74)
      | ~ r2_hidden(A_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_30,c_122])).

tff(c_212,plain,(
    ! [A_98,B_99,B_100] :
      ( m1_subset_1(A_98,B_99)
      | ~ r1_tarski(B_100,B_99)
      | v1_xboole_0(B_100)
      | ~ m1_subset_1(A_98,B_100) ) ),
    inference(resolution,[status(thm)],[c_18,c_136])).

tff(c_218,plain,(
    ! [A_98] :
      ( m1_subset_1(A_98,k3_zfmisc_1('#skF_2','#skF_3','#skF_4'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_98,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_97,c_212])).

tff(c_219,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_38,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_222,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_219,c_38])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_222])).

tff(c_228,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_12,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_142,plain,(
    ! [A_14,B_74] :
      ( m1_subset_1('#skF_1'(A_14),B_74)
      | ~ r1_tarski(A_14,B_74)
      | k1_xboole_0 = A_14 ) ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( m1_subset_1(k5_mcart_1(A_4,B_5,C_6,D_7),A_4)
      | ~ m1_subset_1(D_7,k3_zfmisc_1(A_4,B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_446,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k3_mcart_1(k5_mcart_1(A_137,B_138,C_139,D_140),k6_mcart_1(A_137,B_138,C_139,D_140),k7_mcart_1(A_137,B_138,C_139,D_140)) = D_140
      | ~ m1_subset_1(D_140,k3_zfmisc_1(A_137,B_138,C_139))
      | k1_xboole_0 = C_139
      | k1_xboole_0 = B_138
      | k1_xboole_0 = A_137 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_188,plain,(
    ! [C_88,A_89,D_90,E_91] :
      ( ~ r2_hidden(C_88,A_89)
      | k3_mcart_1(C_88,D_90,E_91) != '#skF_1'(A_89)
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_193,plain,(
    ! [A_28,D_90,E_91,B_29] :
      ( k3_mcart_1(A_28,D_90,E_91) != '#skF_1'(B_29)
      | k1_xboole_0 = B_29
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_18,c_188])).

tff(c_1947,plain,(
    ! [D_296,B_297,A_300,B_299,C_298] :
      ( D_296 != '#skF_1'(B_297)
      | k1_xboole_0 = B_297
      | v1_xboole_0(B_297)
      | ~ m1_subset_1(k5_mcart_1(A_300,B_299,C_298,D_296),B_297)
      | ~ m1_subset_1(D_296,k3_zfmisc_1(A_300,B_299,C_298))
      | k1_xboole_0 = C_298
      | k1_xboole_0 = B_299
      | k1_xboole_0 = A_300 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_193])).

tff(c_2078,plain,(
    ! [D_313,A_314,C_315,B_316] :
      ( D_313 != '#skF_1'(A_314)
      | v1_xboole_0(A_314)
      | k1_xboole_0 = C_315
      | k1_xboole_0 = B_316
      | k1_xboole_0 = A_314
      | ~ m1_subset_1(D_313,k3_zfmisc_1(A_314,B_316,C_315)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1947])).

tff(c_3867,plain,(
    ! [A_470,A_469,C_471,B_472] :
      ( '#skF_1'(A_470) != '#skF_1'(A_469)
      | v1_xboole_0(A_469)
      | k1_xboole_0 = C_471
      | k1_xboole_0 = B_472
      | k1_xboole_0 = A_469
      | ~ r1_tarski(A_470,k3_zfmisc_1(A_469,B_472,C_471))
      | k1_xboole_0 = A_470 ) ),
    inference(resolution,[status(thm)],[c_142,c_2078])).

tff(c_3893,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_97,c_3867])).

tff(c_3910,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_228,c_3893])).

tff(c_3911,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3910])).

tff(c_4033,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3911,c_40])).

tff(c_24,plain,(
    ! [A_30,C_32] : k3_zfmisc_1(A_30,k1_xboole_0,C_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4030,plain,(
    ! [A_30,C_32] : k3_zfmisc_1(A_30,'#skF_3',C_32) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3911,c_3911,c_24])).

tff(c_4139,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4030,c_97])).

tff(c_32,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ r1_tarski(A_35,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4028,plain,(
    ! [A_35] :
      ( A_35 = '#skF_3'
      | ~ r1_tarski(A_35,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3911,c_3911,c_32])).

tff(c_4194,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4139,c_4028])).

tff(c_4200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4033,c_4194])).

tff(c_4201,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3910])).

tff(c_4324,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4201,c_40])).

tff(c_22,plain,(
    ! [A_30,B_31] : k3_zfmisc_1(A_30,B_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4320,plain,(
    ! [A_30,B_31] : k3_zfmisc_1(A_30,B_31,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4201,c_4201,c_22])).

tff(c_4488,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4320,c_97])).

tff(c_4569,plain,(
    ! [A_493] :
      ( A_493 = '#skF_4'
      | ~ r1_tarski(A_493,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4201,c_4201,c_32])).

tff(c_4572,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4488,c_4569])).

tff(c_4584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4324,c_4572])).

tff(c_4585,plain,
    ( r1_tarski('#skF_2',k3_zfmisc_1('#skF_3','#skF_4','#skF_2'))
    | r1_tarski('#skF_2',k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_4621,plain,(
    r1_tarski('#skF_2',k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4585])).

tff(c_4622,plain,(
    ! [A_506,C_507,B_508] :
      ( m1_subset_1(A_506,C_507)
      | ~ m1_subset_1(B_508,k1_zfmisc_1(C_507))
      | ~ r2_hidden(A_506,B_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4626,plain,(
    ! [A_509,B_510,A_511] :
      ( m1_subset_1(A_509,B_510)
      | ~ r2_hidden(A_509,A_511)
      | ~ r1_tarski(A_511,B_510) ) ),
    inference(resolution,[status(thm)],[c_30,c_4622])).

tff(c_4702,plain,(
    ! [A_534,B_535,B_536] :
      ( m1_subset_1(A_534,B_535)
      | ~ r1_tarski(B_536,B_535)
      | v1_xboole_0(B_536)
      | ~ m1_subset_1(A_534,B_536) ) ),
    inference(resolution,[status(thm)],[c_18,c_4626])).

tff(c_4708,plain,(
    ! [A_534] :
      ( m1_subset_1(A_534,k3_zfmisc_1('#skF_4','#skF_2','#skF_3'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_534,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4621,c_4702])).

tff(c_4709,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4708])).

tff(c_4712,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4709,c_38])).

tff(c_4716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4712])).

tff(c_4718,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4708])).

tff(c_4632,plain,(
    ! [A_14,B_510] :
      ( m1_subset_1('#skF_1'(A_14),B_510)
      | ~ r1_tarski(A_14,B_510)
      | k1_xboole_0 = A_14 ) ),
    inference(resolution,[status(thm)],[c_12,c_4626])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( m1_subset_1(k6_mcart_1(A_8,B_9,C_10,D_11),B_9)
      | ~ m1_subset_1(D_11,k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [A_36,B_37,C_38,D_40] :
      ( k3_mcart_1(k5_mcart_1(A_36,B_37,C_38,D_40),k6_mcart_1(A_36,B_37,C_38,D_40),k7_mcart_1(A_36,B_37,C_38,D_40)) = D_40
      | ~ m1_subset_1(D_40,k3_zfmisc_1(A_36,B_37,C_38))
      | k1_xboole_0 = C_38
      | k1_xboole_0 = B_37
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4664,plain,(
    ! [D_516,A_517,C_518,E_519] :
      ( ~ r2_hidden(D_516,A_517)
      | k3_mcart_1(C_518,D_516,E_519) != '#skF_1'(A_517)
      | k1_xboole_0 = A_517 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4943,plain,(
    ! [C_569,A_570,E_571,B_572] :
      ( k3_mcart_1(C_569,A_570,E_571) != '#skF_1'(B_572)
      | k1_xboole_0 = B_572
      | v1_xboole_0(B_572)
      | ~ m1_subset_1(A_570,B_572) ) ),
    inference(resolution,[status(thm)],[c_18,c_4664])).

tff(c_6518,plain,(
    ! [C_749,D_745,B_746,B_748,A_747] :
      ( D_745 != '#skF_1'(B_746)
      | k1_xboole_0 = B_746
      | v1_xboole_0(B_746)
      | ~ m1_subset_1(k6_mcart_1(A_747,B_748,C_749,D_745),B_746)
      | ~ m1_subset_1(D_745,k3_zfmisc_1(A_747,B_748,C_749))
      | k1_xboole_0 = C_749
      | k1_xboole_0 = B_748
      | k1_xboole_0 = A_747 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4943])).

tff(c_6684,plain,(
    ! [D_761,B_762,C_763,A_764] :
      ( D_761 != '#skF_1'(B_762)
      | v1_xboole_0(B_762)
      | k1_xboole_0 = C_763
      | k1_xboole_0 = B_762
      | k1_xboole_0 = A_764
      | ~ m1_subset_1(D_761,k3_zfmisc_1(A_764,B_762,C_763)) ) ),
    inference(resolution,[status(thm)],[c_6,c_6518])).

tff(c_8266,plain,(
    ! [B_891,A_892,C_893,A_894] :
      ( '#skF_1'(B_891) != '#skF_1'(A_892)
      | v1_xboole_0(B_891)
      | k1_xboole_0 = C_893
      | k1_xboole_0 = B_891
      | k1_xboole_0 = A_894
      | ~ r1_tarski(A_892,k3_zfmisc_1(A_894,B_891,C_893))
      | k1_xboole_0 = A_892 ) ),
    inference(resolution,[status(thm)],[c_4632,c_6684])).

tff(c_8292,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4621,c_8266])).

tff(c_8309,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_4718,c_8292])).

tff(c_8310,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8309])).

tff(c_26,plain,(
    ! [B_31,C_32] : k3_zfmisc_1(k1_xboole_0,B_31,C_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8424,plain,(
    ! [B_31,C_32] : k3_zfmisc_1('#skF_4',B_31,C_32) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8310,c_8310,c_26])).

tff(c_8534,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8424,c_4621])).

tff(c_8422,plain,(
    ! [A_30,B_31] : k3_zfmisc_1(A_30,B_31,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8310,c_8310,c_22])).

tff(c_4586,plain,(
    ~ r1_tarski('#skF_2',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8604,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8422,c_4586])).

tff(c_8607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8534,c_8604])).

tff(c_8608,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8309])).

tff(c_8722,plain,(
    ! [A_30,C_32] : k3_zfmisc_1(A_30,'#skF_3',C_32) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_8608,c_24])).

tff(c_8845,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8722,c_4586])).

tff(c_8721,plain,(
    ! [A_30,B_31] : k3_zfmisc_1(A_30,B_31,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_8608,c_22])).

tff(c_8899,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8721,c_4621])).

tff(c_8901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8845,c_8899])).

tff(c_8902,plain,(
    r1_tarski('#skF_2',k3_zfmisc_1('#skF_3','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4585])).

tff(c_4590,plain,(
    ! [A_500,B_501,C_502] : k2_zfmisc_1(k2_zfmisc_1(A_500,B_501),C_502) = k3_zfmisc_1(A_500,B_501,C_502) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_12,B_13] :
      ( ~ r1_tarski(A_12,k2_zfmisc_1(B_13,A_12))
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4602,plain,(
    ! [C_502,A_500,B_501] :
      ( ~ r1_tarski(C_502,k3_zfmisc_1(A_500,B_501,C_502))
      | k1_xboole_0 = C_502 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4590,c_8])).

tff(c_8906,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8902,c_4602])).

tff(c_8910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_8906])).

%------------------------------------------------------------------------------
