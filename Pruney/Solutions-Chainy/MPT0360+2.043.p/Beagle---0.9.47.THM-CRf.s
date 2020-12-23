%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:24 EST 2020

% Result     : Theorem 14.25s
% Output     : CNFRefutation 14.43s
% Verified   : 
% Statistics : Number of formulae       :  141 (1322 expanded)
%              Number of leaves         :   32 ( 451 expanded)
%              Depth                    :   23
%              Number of atoms          :  233 (2769 expanded)
%              Number of equality atoms :   67 ( 604 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14800,plain,(
    ! [A_471,C_472,B_473] :
      ( r1_xboole_0(A_471,C_472)
      | ~ r1_tarski(A_471,k4_xboole_0(B_473,C_472)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14896,plain,(
    ! [A_480,A_481] :
      ( r1_xboole_0(A_480,k1_xboole_0)
      | ~ r1_tarski(A_480,A_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14800])).

tff(c_14903,plain,(
    r1_xboole_0('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_14896])).

tff(c_15250,plain,(
    ! [A_506,B_507,C_508] :
      ( ~ r1_xboole_0(A_506,B_507)
      | ~ r1_tarski(C_508,B_507)
      | ~ r1_tarski(C_508,A_506)
      | v1_xboole_0(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_15290,plain,(
    ! [C_510] :
      ( ~ r1_tarski(C_510,k1_xboole_0)
      | ~ r1_tarski(C_510,'#skF_4')
      | v1_xboole_0(C_510) ) ),
    inference(resolution,[status(thm)],[c_14903,c_15250])).

tff(c_15294,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_15290])).

tff(c_15297,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15294])).

tff(c_52,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14934,plain,(
    ! [A_489,B_490] :
      ( k4_xboole_0(A_489,B_490) = k3_subset_1(A_489,B_490)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(A_489)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14943,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_14934])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15064,plain,(
    ! [A_500] :
      ( r1_xboole_0(A_500,'#skF_5')
      | ~ r1_tarski(A_500,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14943,c_4])).

tff(c_15072,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_15064])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_15078,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15072,c_16])).

tff(c_20,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_15095,plain,(
    ! [A_501] :
      ( r1_xboole_0(A_501,'#skF_4')
      | ~ r1_tarski(A_501,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15078,c_20])).

tff(c_15164,plain,(
    ! [A_505] :
      ( k4_xboole_0(A_505,'#skF_4') = A_505
      | ~ r1_tarski(A_505,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_15095,c_16])).

tff(c_15174,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_15164])).

tff(c_14724,plain,(
    ! [A_463,B_464] : k4_xboole_0(A_463,k4_xboole_0(A_463,B_464)) = k3_xboole_0(A_463,B_464) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14739,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14724])).

tff(c_24,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14791,plain,(
    ! [B_469,A_470] :
      ( m1_subset_1(B_469,A_470)
      | ~ r2_hidden(B_469,A_470)
      | v1_xboole_0(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14799,plain,(
    ! [C_22,A_18] :
      ( m1_subset_1(C_22,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_14791])).

tff(c_15991,plain,(
    ! [C_543,A_544] :
      ( m1_subset_1(C_543,k1_zfmisc_1(A_544))
      | v1_xboole_0(k1_zfmisc_1(A_544))
      | ~ r1_tarski(C_543,A_544) ) ),
    inference(resolution,[status(thm)],[c_24,c_14791])).

tff(c_42,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k3_subset_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22341,plain,(
    ! [A_756,C_757] :
      ( k4_xboole_0(A_756,C_757) = k3_subset_1(A_756,C_757)
      | v1_xboole_0(k1_zfmisc_1(A_756))
      | ~ r1_tarski(C_757,A_756) ) ),
    inference(resolution,[status(thm)],[c_15991,c_42])).

tff(c_22359,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_22341])).

tff(c_22374,plain,(
    ! [A_758] :
      ( k3_subset_1(A_758,k1_xboole_0) = A_758
      | v1_xboole_0(k1_zfmisc_1(A_758)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22359])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,A_23)
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16246,plain,(
    ! [A_560,B_561] :
      ( k4_xboole_0(A_560,B_561) = k3_subset_1(A_560,B_561)
      | ~ v1_xboole_0(B_561)
      | ~ v1_xboole_0(k1_zfmisc_1(A_560)) ) ),
    inference(resolution,[status(thm)],[c_38,c_14934])).

tff(c_16248,plain,(
    ! [A_560] :
      ( k4_xboole_0(A_560,k1_xboole_0) = k3_subset_1(A_560,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_560)) ) ),
    inference(resolution,[status(thm)],[c_15297,c_16246])).

tff(c_16254,plain,(
    ! [A_560] :
      ( k3_subset_1(A_560,k1_xboole_0) = A_560
      | ~ v1_xboole_0(k1_zfmisc_1(A_560)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16248])).

tff(c_22400,plain,(
    ! [A_759] : k3_subset_1(A_759,k1_xboole_0) = A_759 ),
    inference(resolution,[status(thm)],[c_22374,c_16254])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k3_subset_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24084,plain,(
    ! [A_781] :
      ( m1_subset_1(A_781,k1_zfmisc_1(A_781))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_781)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22400,c_44])).

tff(c_24089,plain,(
    ! [A_18] :
      ( m1_subset_1(A_18,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(k1_xboole_0,A_18) ) ),
    inference(resolution,[status(thm)],[c_14799,c_24084])).

tff(c_24135,plain,(
    ! [A_784] :
      ( m1_subset_1(A_784,k1_zfmisc_1(A_784))
      | v1_xboole_0(k1_zfmisc_1(A_784)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24089])).

tff(c_24151,plain,(
    ! [A_784] :
      ( k4_xboole_0(A_784,A_784) = k3_subset_1(A_784,A_784)
      | v1_xboole_0(k1_zfmisc_1(A_784)) ) ),
    inference(resolution,[status(thm)],[c_24135,c_42])).

tff(c_26519,plain,(
    ! [A_822] :
      ( k3_xboole_0(A_822,k1_xboole_0) = k3_subset_1(A_822,A_822)
      | v1_xboole_0(k1_zfmisc_1(A_822)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14739,c_24151])).

tff(c_24092,plain,(
    ! [A_781] :
      ( m1_subset_1(A_781,k1_zfmisc_1(A_781))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_781)) ) ),
    inference(resolution,[status(thm)],[c_38,c_24084])).

tff(c_25119,plain,(
    ! [A_794] :
      ( m1_subset_1(A_794,k1_zfmisc_1(A_794))
      | ~ v1_xboole_0(k1_zfmisc_1(A_794)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15297,c_24092])).

tff(c_25135,plain,(
    ! [A_794] :
      ( k4_xboole_0(A_794,A_794) = k3_subset_1(A_794,A_794)
      | ~ v1_xboole_0(k1_zfmisc_1(A_794)) ) ),
    inference(resolution,[status(thm)],[c_25119,c_42])).

tff(c_25145,plain,(
    ! [A_794] :
      ( k3_xboole_0(A_794,k1_xboole_0) = k3_subset_1(A_794,A_794)
      | ~ v1_xboole_0(k1_zfmisc_1(A_794)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14739,c_25135])).

tff(c_26709,plain,(
    ! [A_823] : k3_xboole_0(A_823,k1_xboole_0) = k3_subset_1(A_823,A_823) ),
    inference(resolution,[status(thm)],[c_26519,c_25145])).

tff(c_15188,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15174,c_14739])).

tff(c_26845,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26709,c_15188])).

tff(c_22394,plain,(
    ! [A_758] : k3_subset_1(A_758,k1_xboole_0) = A_758 ),
    inference(resolution,[status(thm)],[c_22374,c_16254])).

tff(c_46,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(A_29,k3_subset_1(A_29,B_30)) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16000,plain,(
    ! [A_544,C_543] :
      ( k3_subset_1(A_544,k3_subset_1(A_544,C_543)) = C_543
      | v1_xboole_0(k1_zfmisc_1(A_544))
      | ~ r1_tarski(C_543,A_544) ) ),
    inference(resolution,[status(thm)],[c_15991,c_46])).

tff(c_22406,plain,(
    ! [A_759] :
      ( k3_subset_1(A_759,A_759) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_759))
      | ~ r1_tarski(k1_xboole_0,A_759) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22400,c_16000])).

tff(c_22428,plain,(
    ! [A_759] :
      ( k3_subset_1(A_759,A_759) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_759)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22406])).

tff(c_26740,plain,(
    ! [A_823] :
      ( k3_xboole_0(A_823,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_823)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26709,c_22428])).

tff(c_24100,plain,(
    ! [A_781] :
      ( m1_subset_1(A_781,k1_zfmisc_1(A_781))
      | ~ v1_xboole_0(k1_zfmisc_1(A_781)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15297,c_24092])).

tff(c_15338,plain,(
    ! [C_517] :
      ( ~ r1_tarski(C_517,'#skF_5')
      | ~ r1_tarski(C_517,'#skF_4')
      | v1_xboole_0(C_517) ) ),
    inference(resolution,[status(thm)],[c_15072,c_15250])).

tff(c_15349,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_15338])).

tff(c_15350,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15349])).

tff(c_14718,plain,(
    ! [B_461,A_462] :
      ( r2_hidden(B_461,A_462)
      | ~ m1_subset_1(B_461,A_462)
      | v1_xboole_0(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16100,plain,(
    ! [B_551,A_552] :
      ( r1_tarski(B_551,A_552)
      | ~ m1_subset_1(B_551,k1_zfmisc_1(A_552))
      | v1_xboole_0(k1_zfmisc_1(A_552)) ) ),
    inference(resolution,[status(thm)],[c_14718,c_22])).

tff(c_16115,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k3_subset_1(A_27,B_28),A_27)
      | v1_xboole_0(k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_44,c_16100])).

tff(c_26933,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26845,c_16115])).

tff(c_26950,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_15350,c_26933])).

tff(c_27471,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_26950])).

tff(c_27484,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24100,c_27471])).

tff(c_27495,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26740,c_27484])).

tff(c_27522,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15188,c_27495])).

tff(c_27524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_27522])).

tff(c_27525,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_26950])).

tff(c_15052,plain,(
    ! [A_498,B_499] :
      ( k3_subset_1(A_498,k3_subset_1(A_498,B_499)) = B_499
      | ~ m1_subset_1(B_499,k1_zfmisc_1(A_498)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_15058,plain,(
    ! [A_498,B_24] :
      ( k3_subset_1(A_498,k3_subset_1(A_498,B_24)) = B_24
      | ~ v1_xboole_0(B_24)
      | ~ v1_xboole_0(k1_zfmisc_1(A_498)) ) ),
    inference(resolution,[status(thm)],[c_38,c_15052])).

tff(c_28457,plain,(
    ! [B_858] :
      ( k3_subset_1('#skF_4',k3_subset_1('#skF_4',B_858)) = B_858
      | ~ v1_xboole_0(B_858) ) ),
    inference(resolution,[status(thm)],[c_27525,c_15058])).

tff(c_28533,plain,
    ( k3_subset_1('#skF_4','#skF_4') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22394,c_28457])).

tff(c_28585,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15297,c_26845,c_28533])).

tff(c_28587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_28585])).

tff(c_28589,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_15349])).

tff(c_29305,plain,(
    ! [C_891,A_892] :
      ( m1_subset_1(C_891,k1_zfmisc_1(A_892))
      | v1_xboole_0(k1_zfmisc_1(A_892))
      | ~ r1_tarski(C_891,A_892) ) ),
    inference(resolution,[status(thm)],[c_24,c_14791])).

tff(c_34389,plain,(
    ! [A_1067,C_1068] :
      ( k4_xboole_0(A_1067,C_1068) = k3_subset_1(A_1067,C_1068)
      | v1_xboole_0(k1_zfmisc_1(A_1067))
      | ~ r1_tarski(C_1068,A_1067) ) ),
    inference(resolution,[status(thm)],[c_29305,c_42])).

tff(c_34401,plain,
    ( k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28589,c_34389])).

tff(c_34416,plain,
    ( k3_subset_1('#skF_4','#skF_4') = '#skF_4'
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15174,c_34401])).

tff(c_34901,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_34416])).

tff(c_28588,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_15349])).

tff(c_29524,plain,(
    ! [A_901,B_902] :
      ( k4_xboole_0(A_901,B_902) = k3_subset_1(A_901,B_902)
      | ~ v1_xboole_0(B_902)
      | ~ v1_xboole_0(k1_zfmisc_1(A_901)) ) ),
    inference(resolution,[status(thm)],[c_38,c_14934])).

tff(c_29533,plain,(
    ! [A_901] :
      ( k4_xboole_0(A_901,'#skF_4') = k3_subset_1(A_901,'#skF_4')
      | ~ v1_xboole_0(k1_zfmisc_1(A_901)) ) ),
    inference(resolution,[status(thm)],[c_28588,c_29524])).

tff(c_34914,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34901,c_29533])).

tff(c_34928,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15174,c_34914])).

tff(c_34407,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_34389])).

tff(c_34423,plain,(
    ! [A_1069] :
      ( k3_subset_1(A_1069,k1_xboole_0) = A_1069
      | v1_xboole_0(k1_zfmisc_1(A_1069)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_34407])).

tff(c_29528,plain,(
    ! [A_901] :
      ( k4_xboole_0(A_901,k1_xboole_0) = k3_subset_1(A_901,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_901)) ) ),
    inference(resolution,[status(thm)],[c_15297,c_29524])).

tff(c_29535,plain,(
    ! [A_901] :
      ( k3_subset_1(A_901,k1_xboole_0) = A_901
      | ~ v1_xboole_0(k1_zfmisc_1(A_901)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_29528])).

tff(c_34448,plain,(
    ! [A_1069] : k3_subset_1(A_1069,k1_xboole_0) = A_1069 ),
    inference(resolution,[status(thm)],[c_34423,c_29535])).

tff(c_37796,plain,(
    ! [B_1107] :
      ( k3_subset_1('#skF_4',k3_subset_1('#skF_4',B_1107)) = B_1107
      | ~ v1_xboole_0(B_1107) ) ),
    inference(resolution,[status(thm)],[c_34901,c_15058])).

tff(c_37850,plain,
    ( k3_subset_1('#skF_4','#skF_4') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34448,c_37796])).

tff(c_37888,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15297,c_34928,c_37850])).

tff(c_37890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_37888])).

tff(c_37891,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34416])).

tff(c_34453,plain,(
    ! [A_1070] : k3_subset_1(A_1070,k1_xboole_0) = A_1070 ),
    inference(resolution,[status(thm)],[c_34423,c_29535])).

tff(c_29318,plain,(
    ! [A_892,C_891] :
      ( k3_subset_1(A_892,k3_subset_1(A_892,C_891)) = C_891
      | v1_xboole_0(k1_zfmisc_1(A_892))
      | ~ r1_tarski(C_891,A_892) ) ),
    inference(resolution,[status(thm)],[c_29305,c_46])).

tff(c_34459,plain,(
    ! [A_1070] :
      ( k3_subset_1(A_1070,A_1070) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_1070))
      | ~ r1_tarski(k1_xboole_0,A_1070) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34453,c_29318])).

tff(c_37914,plain,(
    ! [A_1108] :
      ( k3_subset_1(A_1108,A_1108) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_1108)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34459])).

tff(c_37892,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_34416])).

tff(c_37939,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37914,c_37892])).

tff(c_37970,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37891,c_37939])).

tff(c_37972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_37970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:39:29 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.25/6.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.34/6.66  
% 14.34/6.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.34/6.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 14.34/6.66  
% 14.34/6.66  %Foreground sorts:
% 14.34/6.66  
% 14.34/6.66  
% 14.34/6.66  %Background operators:
% 14.34/6.66  
% 14.34/6.66  
% 14.34/6.66  %Foreground operators:
% 14.34/6.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.34/6.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.34/6.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.34/6.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.34/6.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.34/6.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.34/6.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.34/6.66  tff('#skF_5', type, '#skF_5': $i).
% 14.34/6.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.34/6.66  tff('#skF_3', type, '#skF_3': $i).
% 14.34/6.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.34/6.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.34/6.66  tff('#skF_4', type, '#skF_4': $i).
% 14.34/6.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.34/6.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.34/6.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.34/6.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.34/6.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.34/6.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.34/6.66  
% 14.43/6.68  tff(f_98, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 14.43/6.68  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.43/6.68  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.43/6.68  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 14.43/6.68  tff(f_49, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 14.43/6.68  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.43/6.68  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 14.43/6.68  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 14.43/6.68  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.43/6.68  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.43/6.68  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 14.43/6.68  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.43/6.68  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.43/6.68  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.43/6.68  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.43/6.68  tff(c_50, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.43/6.68  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.43/6.68  tff(c_14800, plain, (![A_471, C_472, B_473]: (r1_xboole_0(A_471, C_472) | ~r1_tarski(A_471, k4_xboole_0(B_473, C_472)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.43/6.68  tff(c_14896, plain, (![A_480, A_481]: (r1_xboole_0(A_480, k1_xboole_0) | ~r1_tarski(A_480, A_481))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14800])).
% 14.43/6.68  tff(c_14903, plain, (r1_xboole_0('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_14896])).
% 14.43/6.68  tff(c_15250, plain, (![A_506, B_507, C_508]: (~r1_xboole_0(A_506, B_507) | ~r1_tarski(C_508, B_507) | ~r1_tarski(C_508, A_506) | v1_xboole_0(C_508))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.43/6.68  tff(c_15290, plain, (![C_510]: (~r1_tarski(C_510, k1_xboole_0) | ~r1_tarski(C_510, '#skF_4') | v1_xboole_0(C_510))), inference(resolution, [status(thm)], [c_14903, c_15250])).
% 14.43/6.68  tff(c_15294, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_15290])).
% 14.43/6.68  tff(c_15297, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15294])).
% 14.43/6.68  tff(c_52, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.43/6.68  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.43/6.68  tff(c_14934, plain, (![A_489, B_490]: (k4_xboole_0(A_489, B_490)=k3_subset_1(A_489, B_490) | ~m1_subset_1(B_490, k1_zfmisc_1(A_489)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.43/6.68  tff(c_14943, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_14934])).
% 14.43/6.68  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.43/6.68  tff(c_15064, plain, (![A_500]: (r1_xboole_0(A_500, '#skF_5') | ~r1_tarski(A_500, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_14943, c_4])).
% 14.43/6.68  tff(c_15072, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_15064])).
% 14.43/6.68  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.43/6.68  tff(c_15078, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_15072, c_16])).
% 14.43/6.68  tff(c_20, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.43/6.68  tff(c_15095, plain, (![A_501]: (r1_xboole_0(A_501, '#skF_4') | ~r1_tarski(A_501, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15078, c_20])).
% 14.43/6.68  tff(c_15164, plain, (![A_505]: (k4_xboole_0(A_505, '#skF_4')=A_505 | ~r1_tarski(A_505, '#skF_5'))), inference(resolution, [status(thm)], [c_15095, c_16])).
% 14.43/6.68  tff(c_15174, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_15164])).
% 14.43/6.68  tff(c_14724, plain, (![A_463, B_464]: (k4_xboole_0(A_463, k4_xboole_0(A_463, B_464))=k3_xboole_0(A_463, B_464))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.43/6.68  tff(c_14739, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14724])).
% 14.43/6.68  tff(c_24, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.43/6.68  tff(c_14791, plain, (![B_469, A_470]: (m1_subset_1(B_469, A_470) | ~r2_hidden(B_469, A_470) | v1_xboole_0(A_470))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.43/6.68  tff(c_14799, plain, (![C_22, A_18]: (m1_subset_1(C_22, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(resolution, [status(thm)], [c_24, c_14791])).
% 14.43/6.68  tff(c_15991, plain, (![C_543, A_544]: (m1_subset_1(C_543, k1_zfmisc_1(A_544)) | v1_xboole_0(k1_zfmisc_1(A_544)) | ~r1_tarski(C_543, A_544))), inference(resolution, [status(thm)], [c_24, c_14791])).
% 14.43/6.68  tff(c_42, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k3_subset_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.43/6.68  tff(c_22341, plain, (![A_756, C_757]: (k4_xboole_0(A_756, C_757)=k3_subset_1(A_756, C_757) | v1_xboole_0(k1_zfmisc_1(A_756)) | ~r1_tarski(C_757, A_756))), inference(resolution, [status(thm)], [c_15991, c_42])).
% 14.43/6.68  tff(c_22359, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_22341])).
% 14.43/6.68  tff(c_22374, plain, (![A_758]: (k3_subset_1(A_758, k1_xboole_0)=A_758 | v1_xboole_0(k1_zfmisc_1(A_758)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22359])).
% 14.43/6.68  tff(c_38, plain, (![B_24, A_23]: (m1_subset_1(B_24, A_23) | ~v1_xboole_0(B_24) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.43/6.68  tff(c_16246, plain, (![A_560, B_561]: (k4_xboole_0(A_560, B_561)=k3_subset_1(A_560, B_561) | ~v1_xboole_0(B_561) | ~v1_xboole_0(k1_zfmisc_1(A_560)))), inference(resolution, [status(thm)], [c_38, c_14934])).
% 14.43/6.68  tff(c_16248, plain, (![A_560]: (k4_xboole_0(A_560, k1_xboole_0)=k3_subset_1(A_560, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_560)))), inference(resolution, [status(thm)], [c_15297, c_16246])).
% 14.43/6.68  tff(c_16254, plain, (![A_560]: (k3_subset_1(A_560, k1_xboole_0)=A_560 | ~v1_xboole_0(k1_zfmisc_1(A_560)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16248])).
% 14.43/6.68  tff(c_22400, plain, (![A_759]: (k3_subset_1(A_759, k1_xboole_0)=A_759)), inference(resolution, [status(thm)], [c_22374, c_16254])).
% 14.43/6.68  tff(c_44, plain, (![A_27, B_28]: (m1_subset_1(k3_subset_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.43/6.68  tff(c_24084, plain, (![A_781]: (m1_subset_1(A_781, k1_zfmisc_1(A_781)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_781)))), inference(superposition, [status(thm), theory('equality')], [c_22400, c_44])).
% 14.43/6.68  tff(c_24089, plain, (![A_18]: (m1_subset_1(A_18, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_14799, c_24084])).
% 14.43/6.68  tff(c_24135, plain, (![A_784]: (m1_subset_1(A_784, k1_zfmisc_1(A_784)) | v1_xboole_0(k1_zfmisc_1(A_784)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24089])).
% 14.43/6.68  tff(c_24151, plain, (![A_784]: (k4_xboole_0(A_784, A_784)=k3_subset_1(A_784, A_784) | v1_xboole_0(k1_zfmisc_1(A_784)))), inference(resolution, [status(thm)], [c_24135, c_42])).
% 14.43/6.68  tff(c_26519, plain, (![A_822]: (k3_xboole_0(A_822, k1_xboole_0)=k3_subset_1(A_822, A_822) | v1_xboole_0(k1_zfmisc_1(A_822)))), inference(demodulation, [status(thm), theory('equality')], [c_14739, c_24151])).
% 14.43/6.68  tff(c_24092, plain, (![A_781]: (m1_subset_1(A_781, k1_zfmisc_1(A_781)) | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_781)))), inference(resolution, [status(thm)], [c_38, c_24084])).
% 14.43/6.68  tff(c_25119, plain, (![A_794]: (m1_subset_1(A_794, k1_zfmisc_1(A_794)) | ~v1_xboole_0(k1_zfmisc_1(A_794)))), inference(demodulation, [status(thm), theory('equality')], [c_15297, c_24092])).
% 14.43/6.68  tff(c_25135, plain, (![A_794]: (k4_xboole_0(A_794, A_794)=k3_subset_1(A_794, A_794) | ~v1_xboole_0(k1_zfmisc_1(A_794)))), inference(resolution, [status(thm)], [c_25119, c_42])).
% 14.43/6.68  tff(c_25145, plain, (![A_794]: (k3_xboole_0(A_794, k1_xboole_0)=k3_subset_1(A_794, A_794) | ~v1_xboole_0(k1_zfmisc_1(A_794)))), inference(demodulation, [status(thm), theory('equality')], [c_14739, c_25135])).
% 14.43/6.68  tff(c_26709, plain, (![A_823]: (k3_xboole_0(A_823, k1_xboole_0)=k3_subset_1(A_823, A_823))), inference(resolution, [status(thm)], [c_26519, c_25145])).
% 14.43/6.68  tff(c_15188, plain, (k3_xboole_0('#skF_4', k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15174, c_14739])).
% 14.43/6.68  tff(c_26845, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_26709, c_15188])).
% 14.43/6.68  tff(c_22394, plain, (![A_758]: (k3_subset_1(A_758, k1_xboole_0)=A_758)), inference(resolution, [status(thm)], [c_22374, c_16254])).
% 14.43/6.68  tff(c_46, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, B_30))=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.43/6.68  tff(c_16000, plain, (![A_544, C_543]: (k3_subset_1(A_544, k3_subset_1(A_544, C_543))=C_543 | v1_xboole_0(k1_zfmisc_1(A_544)) | ~r1_tarski(C_543, A_544))), inference(resolution, [status(thm)], [c_15991, c_46])).
% 14.43/6.68  tff(c_22406, plain, (![A_759]: (k3_subset_1(A_759, A_759)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_759)) | ~r1_tarski(k1_xboole_0, A_759))), inference(superposition, [status(thm), theory('equality')], [c_22400, c_16000])).
% 14.43/6.68  tff(c_22428, plain, (![A_759]: (k3_subset_1(A_759, A_759)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_759)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22406])).
% 14.43/6.68  tff(c_26740, plain, (![A_823]: (k3_xboole_0(A_823, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_823)))), inference(superposition, [status(thm), theory('equality')], [c_26709, c_22428])).
% 14.43/6.68  tff(c_24100, plain, (![A_781]: (m1_subset_1(A_781, k1_zfmisc_1(A_781)) | ~v1_xboole_0(k1_zfmisc_1(A_781)))), inference(demodulation, [status(thm), theory('equality')], [c_15297, c_24092])).
% 14.43/6.68  tff(c_15338, plain, (![C_517]: (~r1_tarski(C_517, '#skF_5') | ~r1_tarski(C_517, '#skF_4') | v1_xboole_0(C_517))), inference(resolution, [status(thm)], [c_15072, c_15250])).
% 14.43/6.68  tff(c_15349, plain, (~r1_tarski('#skF_4', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_15338])).
% 14.43/6.68  tff(c_15350, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_15349])).
% 14.43/6.68  tff(c_14718, plain, (![B_461, A_462]: (r2_hidden(B_461, A_462) | ~m1_subset_1(B_461, A_462) | v1_xboole_0(A_462))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.43/6.68  tff(c_22, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.43/6.68  tff(c_16100, plain, (![B_551, A_552]: (r1_tarski(B_551, A_552) | ~m1_subset_1(B_551, k1_zfmisc_1(A_552)) | v1_xboole_0(k1_zfmisc_1(A_552)))), inference(resolution, [status(thm)], [c_14718, c_22])).
% 14.43/6.68  tff(c_16115, plain, (![A_27, B_28]: (r1_tarski(k3_subset_1(A_27, B_28), A_27) | v1_xboole_0(k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_44, c_16100])).
% 14.43/6.68  tff(c_26933, plain, (r1_tarski('#skF_4', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26845, c_16115])).
% 14.43/6.68  tff(c_26950, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_15350, c_26933])).
% 14.43/6.68  tff(c_27471, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_26950])).
% 14.43/6.68  tff(c_27484, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_24100, c_27471])).
% 14.43/6.68  tff(c_27495, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26740, c_27484])).
% 14.43/6.68  tff(c_27522, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15188, c_27495])).
% 14.43/6.68  tff(c_27524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_27522])).
% 14.43/6.68  tff(c_27525, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_26950])).
% 14.43/6.68  tff(c_15052, plain, (![A_498, B_499]: (k3_subset_1(A_498, k3_subset_1(A_498, B_499))=B_499 | ~m1_subset_1(B_499, k1_zfmisc_1(A_498)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.43/6.68  tff(c_15058, plain, (![A_498, B_24]: (k3_subset_1(A_498, k3_subset_1(A_498, B_24))=B_24 | ~v1_xboole_0(B_24) | ~v1_xboole_0(k1_zfmisc_1(A_498)))), inference(resolution, [status(thm)], [c_38, c_15052])).
% 14.43/6.68  tff(c_28457, plain, (![B_858]: (k3_subset_1('#skF_4', k3_subset_1('#skF_4', B_858))=B_858 | ~v1_xboole_0(B_858))), inference(resolution, [status(thm)], [c_27525, c_15058])).
% 14.43/6.68  tff(c_28533, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22394, c_28457])).
% 14.43/6.68  tff(c_28585, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15297, c_26845, c_28533])).
% 14.43/6.68  tff(c_28587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_28585])).
% 14.43/6.68  tff(c_28589, plain, (r1_tarski('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_15349])).
% 14.43/6.68  tff(c_29305, plain, (![C_891, A_892]: (m1_subset_1(C_891, k1_zfmisc_1(A_892)) | v1_xboole_0(k1_zfmisc_1(A_892)) | ~r1_tarski(C_891, A_892))), inference(resolution, [status(thm)], [c_24, c_14791])).
% 14.43/6.68  tff(c_34389, plain, (![A_1067, C_1068]: (k4_xboole_0(A_1067, C_1068)=k3_subset_1(A_1067, C_1068) | v1_xboole_0(k1_zfmisc_1(A_1067)) | ~r1_tarski(C_1068, A_1067))), inference(resolution, [status(thm)], [c_29305, c_42])).
% 14.43/6.68  tff(c_34401, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_28589, c_34389])).
% 14.43/6.68  tff(c_34416, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_4' | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15174, c_34401])).
% 14.43/6.68  tff(c_34901, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_34416])).
% 14.43/6.68  tff(c_28588, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_15349])).
% 14.43/6.68  tff(c_29524, plain, (![A_901, B_902]: (k4_xboole_0(A_901, B_902)=k3_subset_1(A_901, B_902) | ~v1_xboole_0(B_902) | ~v1_xboole_0(k1_zfmisc_1(A_901)))), inference(resolution, [status(thm)], [c_38, c_14934])).
% 14.43/6.68  tff(c_29533, plain, (![A_901]: (k4_xboole_0(A_901, '#skF_4')=k3_subset_1(A_901, '#skF_4') | ~v1_xboole_0(k1_zfmisc_1(A_901)))), inference(resolution, [status(thm)], [c_28588, c_29524])).
% 14.43/6.68  tff(c_34914, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34901, c_29533])).
% 14.43/6.68  tff(c_34928, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15174, c_34914])).
% 14.43/6.68  tff(c_34407, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_34389])).
% 14.43/6.68  tff(c_34423, plain, (![A_1069]: (k3_subset_1(A_1069, k1_xboole_0)=A_1069 | v1_xboole_0(k1_zfmisc_1(A_1069)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_34407])).
% 14.43/6.68  tff(c_29528, plain, (![A_901]: (k4_xboole_0(A_901, k1_xboole_0)=k3_subset_1(A_901, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_901)))), inference(resolution, [status(thm)], [c_15297, c_29524])).
% 14.43/6.68  tff(c_29535, plain, (![A_901]: (k3_subset_1(A_901, k1_xboole_0)=A_901 | ~v1_xboole_0(k1_zfmisc_1(A_901)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_29528])).
% 14.43/6.68  tff(c_34448, plain, (![A_1069]: (k3_subset_1(A_1069, k1_xboole_0)=A_1069)), inference(resolution, [status(thm)], [c_34423, c_29535])).
% 14.43/6.68  tff(c_37796, plain, (![B_1107]: (k3_subset_1('#skF_4', k3_subset_1('#skF_4', B_1107))=B_1107 | ~v1_xboole_0(B_1107))), inference(resolution, [status(thm)], [c_34901, c_15058])).
% 14.43/6.68  tff(c_37850, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34448, c_37796])).
% 14.43/6.68  tff(c_37888, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15297, c_34928, c_37850])).
% 14.43/6.68  tff(c_37890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_37888])).
% 14.43/6.68  tff(c_37891, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_34416])).
% 14.43/6.68  tff(c_34453, plain, (![A_1070]: (k3_subset_1(A_1070, k1_xboole_0)=A_1070)), inference(resolution, [status(thm)], [c_34423, c_29535])).
% 14.43/6.68  tff(c_29318, plain, (![A_892, C_891]: (k3_subset_1(A_892, k3_subset_1(A_892, C_891))=C_891 | v1_xboole_0(k1_zfmisc_1(A_892)) | ~r1_tarski(C_891, A_892))), inference(resolution, [status(thm)], [c_29305, c_46])).
% 14.43/6.68  tff(c_34459, plain, (![A_1070]: (k3_subset_1(A_1070, A_1070)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_1070)) | ~r1_tarski(k1_xboole_0, A_1070))), inference(superposition, [status(thm), theory('equality')], [c_34453, c_29318])).
% 14.43/6.68  tff(c_37914, plain, (![A_1108]: (k3_subset_1(A_1108, A_1108)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_1108)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34459])).
% 14.43/6.68  tff(c_37892, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_34416])).
% 14.43/6.68  tff(c_37939, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_37914, c_37892])).
% 14.43/6.68  tff(c_37970, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37891, c_37939])).
% 14.43/6.68  tff(c_37972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_37970])).
% 14.43/6.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/6.68  
% 14.43/6.68  Inference rules
% 14.43/6.68  ----------------------
% 14.43/6.68  #Ref     : 0
% 14.43/6.68  #Sup     : 9722
% 14.43/6.68  #Fact    : 0
% 14.43/6.68  #Define  : 0
% 14.43/6.68  #Split   : 78
% 14.43/6.68  #Chain   : 0
% 14.43/6.68  #Close   : 0
% 14.43/6.68  
% 14.43/6.68  Ordering : KBO
% 14.43/6.68  
% 14.43/6.68  Simplification rules
% 14.43/6.68  ----------------------
% 14.43/6.68  #Subsume      : 2280
% 14.43/6.68  #Demod        : 5097
% 14.43/6.68  #Tautology    : 2531
% 14.43/6.68  #SimpNegUnit  : 65
% 14.43/6.68  #BackRed      : 54
% 14.43/6.68  
% 14.43/6.68  #Partial instantiations: 0
% 14.43/6.68  #Strategies tried      : 1
% 14.43/6.68  
% 14.43/6.68  Timing (in seconds)
% 14.43/6.68  ----------------------
% 14.43/6.68  Preprocessing        : 0.34
% 14.43/6.68  Parsing              : 0.18
% 14.43/6.68  CNF conversion       : 0.02
% 14.43/6.69  Main loop            : 5.54
% 14.43/6.69  Inferencing          : 1.28
% 14.43/6.69  Reduction            : 1.96
% 14.43/6.69  Demodulation         : 1.42
% 14.43/6.69  BG Simplification    : 0.14
% 14.43/6.69  Subsumption          : 1.76
% 14.43/6.69  Abstraction          : 0.17
% 14.43/6.69  MUC search           : 0.00
% 14.43/6.69  Cooper               : 0.00
% 14.43/6.69  Total                : 5.93
% 14.43/6.69  Index Insertion      : 0.00
% 14.43/6.69  Index Deletion       : 0.00
% 14.43/6.69  Index Matching       : 0.00
% 14.43/6.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
