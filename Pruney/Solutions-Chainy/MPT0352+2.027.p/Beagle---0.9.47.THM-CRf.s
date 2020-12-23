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
% DateTime   : Thu Dec  3 09:55:50 EST 2020

% Result     : Theorem 33.34s
% Output     : CNFRefutation 33.34s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 156 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 230 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_54,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_187,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_60])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [A_10] : k2_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_462,plain,(
    ! [A_91,B_92] : k2_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_469,plain,(
    ! [B_92] : k4_xboole_0(B_92,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_112])).

tff(c_481,plain,(
    ! [B_92] : k4_xboole_0(B_92,k1_xboole_0) = B_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_469])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_227,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_231,plain,(
    ! [B_67,A_20] :
      ( r1_tarski(B_67,A_20)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_227,c_26])).

tff(c_384,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_231])).

tff(c_397,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_384])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_235,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_279,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_20])).

tff(c_293,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_544,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_578,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_544])).

tff(c_608,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_293,c_578])).

tff(c_485,plain,(
    ! [B_93] : k4_xboole_0(B_93,k1_xboole_0) = B_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_469])).

tff(c_24,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_500,plain,(
    ! [B_93] : k4_xboole_0(B_93,B_93) = k3_xboole_0(B_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_24])).

tff(c_1014,plain,(
    ! [B_111] : k4_xboole_0(B_111,B_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_500])).

tff(c_18,plain,(
    ! [C_13,B_12,A_11] :
      ( r1_tarski(k4_xboole_0(C_13,B_12),k4_xboole_0(C_13,A_11))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3550,plain,(
    ! [B_205,B_206] :
      ( r1_tarski(k4_xboole_0(B_205,B_206),k1_xboole_0)
      | ~ r1_tarski(B_205,B_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_18])).

tff(c_577,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_544])).

tff(c_3670,plain,(
    ! [B_210,B_211] :
      ( k4_xboole_0(B_210,B_211) = k1_xboole_0
      | ~ r1_tarski(B_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_3550,c_577])).

tff(c_3784,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_397,c_3670])).

tff(c_3855,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3784,c_24])).

tff(c_3897,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_3855])).

tff(c_826,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k3_subset_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_843,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_826])).

tff(c_913,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_24])).

tff(c_938,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_913])).

tff(c_4014,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3897,c_938])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_842,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_826])).

tff(c_780,plain,(
    ! [C_101,B_102,A_103] :
      ( r1_tarski(k4_xboole_0(C_101,B_102),k4_xboole_0(C_101,A_103))
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3602,plain,(
    ! [A_207,B_208,B_209] :
      ( r1_tarski(k4_xboole_0(A_207,B_208),k3_xboole_0(A_207,B_209))
      | ~ r1_tarski(k4_xboole_0(A_207,B_209),B_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_780])).

tff(c_24968,plain,(
    ! [A_462,B_463,B_464] :
      ( r1_tarski(k4_xboole_0(A_462,B_463),k3_xboole_0(B_464,A_462))
      | ~ r1_tarski(k4_xboole_0(A_462,B_464),B_463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3602])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [A_5,A_69,B_70] :
      ( r1_tarski(A_5,A_69)
      | ~ r1_tarski(A_5,k3_xboole_0(A_69,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_12])).

tff(c_114530,plain,(
    ! [A_1166,B_1167,B_1168] :
      ( r1_tarski(k4_xboole_0(A_1166,B_1167),B_1168)
      | ~ r1_tarski(k4_xboole_0(A_1166,B_1168),B_1167) ) ),
    inference(resolution,[status(thm)],[c_24968,c_251])).

tff(c_116208,plain,(
    ! [B_1179] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_1179),'#skF_5')
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),B_1179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_114530])).

tff(c_116255,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4014,c_116208])).

tff(c_116295,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_116255])).

tff(c_116297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_116295])).

tff(c_116298,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_116299,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_116721,plain,(
    ! [A_1223,B_1224] :
      ( k4_xboole_0(A_1223,B_1224) = k3_subset_1(A_1223,B_1224)
      | ~ m1_subset_1(B_1224,k1_zfmisc_1(A_1223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_116737,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_116721])).

tff(c_116738,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_116721])).

tff(c_116860,plain,(
    ! [C_1229,B_1230,A_1231] :
      ( r1_tarski(k4_xboole_0(C_1229,B_1230),k4_xboole_0(C_1229,A_1231))
      | ~ r1_tarski(A_1231,B_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121606,plain,(
    ! [B_1386] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_1386),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_1386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116738,c_116860])).

tff(c_121631,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_116737,c_121606])).

tff(c_121652,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116299,c_121631])).

tff(c_121654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116298,c_121652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 14:25:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.34/23.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.34/23.88  
% 33.34/23.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.34/23.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 33.34/23.88  
% 33.34/23.88  %Foreground sorts:
% 33.34/23.88  
% 33.34/23.88  
% 33.34/23.88  %Background operators:
% 33.34/23.88  
% 33.34/23.88  
% 33.34/23.88  %Foreground operators:
% 33.34/23.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.34/23.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 33.34/23.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 33.34/23.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.34/23.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.34/23.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 33.34/23.88  tff('#skF_5', type, '#skF_5': $i).
% 33.34/23.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 33.34/23.88  tff('#skF_3', type, '#skF_3': $i).
% 33.34/23.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.34/23.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.34/23.88  tff('#skF_4', type, '#skF_4': $i).
% 33.34/23.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.34/23.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 33.34/23.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 33.34/23.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 33.34/23.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 33.34/23.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 33.34/23.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.34/23.88  
% 33.34/23.90  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 33.34/23.90  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 33.34/23.90  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 33.34/23.90  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 33.34/23.90  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 33.34/23.90  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 33.34/23.90  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 33.34/23.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 33.34/23.90  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 33.34/23.90  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 33.34/23.90  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 33.34/23.90  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 33.34/23.90  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 33.34/23.90  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 33.34/23.90  tff(c_54, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 33.34/23.90  tff(c_113, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 33.34/23.90  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 33.34/23.90  tff(c_187, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_113, c_60])).
% 33.34/23.90  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 33.34/23.90  tff(c_100, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 33.34/23.90  tff(c_112, plain, (![A_10]: (k2_xboole_0(k1_xboole_0, A_10)=A_10)), inference(resolution, [status(thm)], [c_16, c_100])).
% 33.34/23.90  tff(c_462, plain, (![A_91, B_92]: (k2_xboole_0(A_91, k4_xboole_0(B_92, A_91))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 33.34/23.90  tff(c_469, plain, (![B_92]: (k4_xboole_0(B_92, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_92))), inference(superposition, [status(thm), theory('equality')], [c_462, c_112])).
% 33.34/23.90  tff(c_481, plain, (![B_92]: (k4_xboole_0(B_92, k1_xboole_0)=B_92)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_469])).
% 33.34/23.90  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 33.34/23.90  tff(c_48, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 33.34/23.90  tff(c_227, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 33.34/23.90  tff(c_26, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 33.34/23.90  tff(c_231, plain, (![B_67, A_20]: (r1_tarski(B_67, A_20) | ~m1_subset_1(B_67, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_227, c_26])).
% 33.34/23.90  tff(c_384, plain, (![B_81, A_82]: (r1_tarski(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_48, c_231])).
% 33.34/23.90  tff(c_397, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_384])).
% 33.34/23.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 33.34/23.90  tff(c_235, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 33.34/23.90  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 33.34/23.90  tff(c_279, plain, (![A_71, B_72]: (r1_tarski(k3_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_235, c_20])).
% 33.34/23.90  tff(c_293, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 33.34/23.90  tff(c_544, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_33])).
% 33.34/23.90  tff(c_578, plain, (![A_97]: (k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_544])).
% 33.34/23.90  tff(c_608, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_293, c_578])).
% 33.34/23.90  tff(c_485, plain, (![B_93]: (k4_xboole_0(B_93, k1_xboole_0)=B_93)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_469])).
% 33.34/23.90  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 33.34/23.90  tff(c_500, plain, (![B_93]: (k4_xboole_0(B_93, B_93)=k3_xboole_0(B_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_485, c_24])).
% 33.34/23.90  tff(c_1014, plain, (![B_111]: (k4_xboole_0(B_111, B_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_608, c_500])).
% 33.34/23.90  tff(c_18, plain, (![C_13, B_12, A_11]: (r1_tarski(k4_xboole_0(C_13, B_12), k4_xboole_0(C_13, A_11)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 33.34/23.90  tff(c_3550, plain, (![B_205, B_206]: (r1_tarski(k4_xboole_0(B_205, B_206), k1_xboole_0) | ~r1_tarski(B_205, B_206))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_18])).
% 33.34/23.90  tff(c_577, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_544])).
% 33.34/23.90  tff(c_3670, plain, (![B_210, B_211]: (k4_xboole_0(B_210, B_211)=k1_xboole_0 | ~r1_tarski(B_210, B_211))), inference(resolution, [status(thm)], [c_3550, c_577])).
% 33.34/23.90  tff(c_3784, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_397, c_3670])).
% 33.34/23.90  tff(c_3855, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3784, c_24])).
% 33.34/23.90  tff(c_3897, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_3855])).
% 33.34/23.90  tff(c_826, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k3_subset_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 33.34/23.90  tff(c_843, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_826])).
% 33.34/23.90  tff(c_913, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_843, c_24])).
% 33.34/23.90  tff(c_938, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_913])).
% 33.34/23.90  tff(c_4014, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3897, c_938])).
% 33.34/23.90  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 33.34/23.90  tff(c_842, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_826])).
% 33.34/23.90  tff(c_780, plain, (![C_101, B_102, A_103]: (r1_tarski(k4_xboole_0(C_101, B_102), k4_xboole_0(C_101, A_103)) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_49])).
% 33.34/23.90  tff(c_3602, plain, (![A_207, B_208, B_209]: (r1_tarski(k4_xboole_0(A_207, B_208), k3_xboole_0(A_207, B_209)) | ~r1_tarski(k4_xboole_0(A_207, B_209), B_208))), inference(superposition, [status(thm), theory('equality')], [c_24, c_780])).
% 33.34/23.90  tff(c_24968, plain, (![A_462, B_463, B_464]: (r1_tarski(k4_xboole_0(A_462, B_463), k3_xboole_0(B_464, A_462)) | ~r1_tarski(k4_xboole_0(A_462, B_464), B_463))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3602])).
% 33.34/23.90  tff(c_12, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 33.34/23.90  tff(c_251, plain, (![A_5, A_69, B_70]: (r1_tarski(A_5, A_69) | ~r1_tarski(A_5, k3_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_12])).
% 33.34/23.90  tff(c_114530, plain, (![A_1166, B_1167, B_1168]: (r1_tarski(k4_xboole_0(A_1166, B_1167), B_1168) | ~r1_tarski(k4_xboole_0(A_1166, B_1168), B_1167))), inference(resolution, [status(thm)], [c_24968, c_251])).
% 33.34/23.90  tff(c_116208, plain, (![B_1179]: (r1_tarski(k4_xboole_0('#skF_3', B_1179), '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), B_1179))), inference(superposition, [status(thm), theory('equality')], [c_842, c_114530])).
% 33.34/23.90  tff(c_116255, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4014, c_116208])).
% 33.34/23.90  tff(c_116295, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_116255])).
% 33.34/23.90  tff(c_116297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_116295])).
% 33.34/23.90  tff(c_116298, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 33.34/23.90  tff(c_116299, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 33.34/23.90  tff(c_116721, plain, (![A_1223, B_1224]: (k4_xboole_0(A_1223, B_1224)=k3_subset_1(A_1223, B_1224) | ~m1_subset_1(B_1224, k1_zfmisc_1(A_1223)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 33.34/23.90  tff(c_116737, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_116721])).
% 33.34/23.90  tff(c_116738, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_116721])).
% 33.34/23.90  tff(c_116860, plain, (![C_1229, B_1230, A_1231]: (r1_tarski(k4_xboole_0(C_1229, B_1230), k4_xboole_0(C_1229, A_1231)) | ~r1_tarski(A_1231, B_1230))), inference(cnfTransformation, [status(thm)], [f_49])).
% 33.34/23.90  tff(c_121606, plain, (![B_1386]: (r1_tarski(k4_xboole_0('#skF_3', B_1386), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_1386))), inference(superposition, [status(thm), theory('equality')], [c_116738, c_116860])).
% 33.34/23.90  tff(c_121631, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_116737, c_121606])).
% 33.34/23.90  tff(c_121652, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116299, c_121631])).
% 33.34/23.90  tff(c_121654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116298, c_121652])).
% 33.34/23.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.34/23.90  
% 33.34/23.90  Inference rules
% 33.34/23.90  ----------------------
% 33.34/23.90  #Ref     : 0
% 33.34/23.90  #Sup     : 28973
% 33.34/23.90  #Fact    : 0
% 33.34/23.90  #Define  : 0
% 33.34/23.90  #Split   : 15
% 33.34/23.90  #Chain   : 0
% 33.34/23.90  #Close   : 0
% 33.34/23.90  
% 33.34/23.90  Ordering : KBO
% 33.34/23.90  
% 33.34/23.90  Simplification rules
% 33.34/23.90  ----------------------
% 33.34/23.90  #Subsume      : 2746
% 33.34/23.90  #Demod        : 33105
% 33.34/23.90  #Tautology    : 16911
% 33.34/23.90  #SimpNegUnit  : 155
% 33.34/23.90  #BackRed      : 17
% 33.34/23.90  
% 33.34/23.90  #Partial instantiations: 0
% 33.34/23.90  #Strategies tried      : 1
% 33.34/23.90  
% 33.34/23.90  Timing (in seconds)
% 33.34/23.90  ----------------------
% 33.34/23.90  Preprocessing        : 0.33
% 33.34/23.90  Parsing              : 0.17
% 33.34/23.90  CNF conversion       : 0.02
% 33.34/23.90  Main loop            : 22.79
% 33.34/23.90  Inferencing          : 2.26
% 33.34/23.90  Reduction            : 13.96
% 33.34/23.90  Demodulation         : 12.52
% 33.34/23.90  BG Simplification    : 0.23
% 33.34/23.90  Subsumption          : 5.37
% 33.34/23.90  Abstraction          : 0.39
% 33.34/23.90  MUC search           : 0.00
% 33.34/23.90  Cooper               : 0.00
% 33.34/23.90  Total                : 23.17
% 33.34/23.90  Index Insertion      : 0.00
% 33.34/23.90  Index Deletion       : 0.00
% 33.34/23.90  Index Matching       : 0.00
% 33.34/23.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
