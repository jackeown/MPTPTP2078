%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:49 EST 2020

% Result     : Theorem 13.89s
% Output     : CNFRefutation 13.99s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 160 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 257 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_52,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_18,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_49,B_50] : k2_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_2])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_372,plain,(
    ! [C_89,B_90,A_91] :
      ( r1_tarski(k4_xboole_0(C_89,B_90),k4_xboole_0(C_89,A_91))
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1374,plain,(
    ! [C_151,B_152,A_153] :
      ( k2_xboole_0(k4_xboole_0(C_151,B_152),k4_xboole_0(C_151,A_153)) = k4_xboole_0(C_151,A_153)
      | ~ r1_tarski(A_153,B_152) ) ),
    inference(resolution,[status(thm)],[c_372,c_14])).

tff(c_1426,plain,(
    ! [B_21,B_152] :
      ( k4_xboole_0(B_21,k4_xboole_0(B_21,B_152)) = k2_xboole_0(k4_xboole_0(B_21,B_152),B_21)
      | ~ r1_tarski(k4_xboole_0(B_21,B_152),B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1374])).

tff(c_10009,plain,(
    ! [B_365,B_366] :
      ( k4_xboole_0(B_365,k4_xboole_0(B_365,B_366)) = B_365
      | ~ r1_tarski(k4_xboole_0(B_365,B_366),B_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_2,c_1426])).

tff(c_10097,plain,(
    ! [A_367] : k4_xboole_0(A_367,k4_xboole_0(A_367,A_367)) = A_367 ),
    inference(resolution,[status(thm)],[c_18,c_10009])).

tff(c_10402,plain,(
    ! [A_367] : r1_tarski(A_367,A_367) ),
    inference(superposition,[status(thm),theory(equality)],[c_10097,c_18])).

tff(c_10480,plain,(
    ! [A_368] : r1_tarski(A_368,A_368) ),
    inference(superposition,[status(thm),theory(equality)],[c_10097,c_18])).

tff(c_211,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(k2_xboole_0(A_61,B_63),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_229,plain,(
    ! [B_2,C_62,A_1] :
      ( r1_tarski(B_2,C_62)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_11072,plain,(
    ! [B_379,A_380] : r1_tarski(B_379,k2_xboole_0(A_380,B_379)) ),
    inference(resolution,[status(thm)],[c_10480,c_229])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_156,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,A_58)
      | ~ m1_subset_1(B_57,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_160,plain,(
    ! [B_57,A_25] :
      ( r1_tarski(B_57,A_25)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_156,c_24])).

tff(c_169,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_160])).

tff(c_182,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_169])).

tff(c_190,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_182,c_14])).

tff(c_214,plain,(
    ! [C_62] :
      ( r1_tarski('#skF_4',C_62)
      | ~ r1_tarski('#skF_3',C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_211])).

tff(c_11244,plain,(
    ! [A_380] : r1_tarski('#skF_4',k2_xboole_0(A_380,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_11072,c_214])).

tff(c_58,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_164,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_58])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_482,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_498,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_482])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(k2_xboole_0(A_10,B_11),C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12771,plain,(
    ! [C_398,B_399,C_400,A_401] :
      ( r1_tarski(k4_xboole_0(C_398,B_399),C_400)
      | ~ r1_tarski(k4_xboole_0(C_398,A_401),C_400)
      | ~ r1_tarski(A_401,B_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1374,c_12])).

tff(c_13715,plain,(
    ! [B_410,C_411] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_410),C_411)
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_411)
      | ~ r1_tarski('#skF_5',B_410) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_12771])).

tff(c_499,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_482])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_581,plain,(
    ! [A_7] :
      ( r1_xboole_0(A_7,'#skF_4')
      | ~ r1_tarski(A_7,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_8])).

tff(c_13746,plain,(
    ! [B_410] :
      ( r1_xboole_0(k4_xboole_0('#skF_3',B_410),'#skF_4')
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_5',B_410) ) ),
    inference(resolution,[status(thm)],[c_13715,c_581])).

tff(c_33989,plain,(
    ! [B_676] :
      ( r1_xboole_0(k4_xboole_0('#skF_3',B_676),'#skF_4')
      | ~ r1_tarski('#skF_5',B_676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_13746])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35442,plain,(
    ! [B_689] :
      ( r1_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_689))
      | ~ r1_tarski('#skF_5',B_689) ) ),
    inference(resolution,[status(thm)],[c_33989,c_4])).

tff(c_682,plain,(
    ! [A_111,B_112,C_113] :
      ( r1_tarski(A_111,B_112)
      | ~ r1_xboole_0(A_111,C_113)
      | ~ r1_tarski(A_111,k2_xboole_0(B_112,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_717,plain,(
    ! [A_111,A_20,B_21] :
      ( r1_tarski(A_111,A_20)
      | ~ r1_xboole_0(A_111,k4_xboole_0(B_21,A_20))
      | ~ r1_tarski(A_111,k2_xboole_0(A_20,B_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_682])).

tff(c_35447,plain,(
    ! [B_689] :
      ( r1_tarski('#skF_4',B_689)
      | ~ r1_tarski('#skF_4',k2_xboole_0(B_689,'#skF_3'))
      | ~ r1_tarski('#skF_5',B_689) ) ),
    inference(resolution,[status(thm)],[c_35442,c_717])).

tff(c_35482,plain,(
    ! [B_690] :
      ( r1_tarski('#skF_4',B_690)
      | ~ r1_tarski('#skF_5',B_690) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11244,c_35447])).

tff(c_35534,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10402,c_35482])).

tff(c_35562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_35534])).

tff(c_35563,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_35564,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_35969,plain,(
    ! [A_763,B_764] :
      ( k4_xboole_0(A_763,B_764) = k3_subset_1(A_763,B_764)
      | ~ m1_subset_1(B_764,k1_zfmisc_1(A_763)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35985,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_35969])).

tff(c_35986,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_35969])).

tff(c_16,plain,(
    ! [C_17,B_16,A_15] :
      ( r1_tarski(k4_xboole_0(C_17,B_16),k4_xboole_0(C_17,A_15))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_37386,plain,(
    ! [B_819] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_819),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_819) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35986,c_16])).

tff(c_37404,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_35985,c_37386])).

tff(c_37412,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35564,c_37404])).

tff(c_37414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35563,c_37412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.89/6.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.89/6.40  
% 13.89/6.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.89/6.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 13.89/6.40  
% 13.89/6.40  %Foreground sorts:
% 13.89/6.40  
% 13.89/6.40  
% 13.89/6.40  %Background operators:
% 13.89/6.40  
% 13.89/6.40  
% 13.89/6.40  %Foreground operators:
% 13.89/6.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.89/6.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.89/6.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.89/6.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.89/6.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.89/6.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.89/6.40  tff('#skF_5', type, '#skF_5': $i).
% 13.89/6.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.89/6.40  tff('#skF_3', type, '#skF_3': $i).
% 13.89/6.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.89/6.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.89/6.40  tff('#skF_4', type, '#skF_4': $i).
% 13.89/6.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.89/6.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.89/6.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.89/6.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.89/6.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.89/6.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.89/6.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.89/6.40  
% 13.99/6.42  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 13.99/6.42  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.99/6.42  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.99/6.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.99/6.42  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.99/6.42  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 13.99/6.42  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.99/6.42  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 13.99/6.42  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 13.99/6.42  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.99/6.42  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 13.99/6.42  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.99/6.42  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.99/6.42  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 13.99/6.42  tff(c_52, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.99/6.42  tff(c_110, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 13.99/6.42  tff(c_18, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.99/6.42  tff(c_105, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.99/6.42  tff(c_111, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), A_49)=A_49)), inference(resolution, [status(thm)], [c_18, c_105])).
% 13.99/6.42  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.99/6.42  tff(c_117, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k4_xboole_0(A_49, B_50))=A_49)), inference(superposition, [status(thm), theory('equality')], [c_111, c_2])).
% 13.99/6.42  tff(c_20, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.99/6.42  tff(c_372, plain, (![C_89, B_90, A_91]: (r1_tarski(k4_xboole_0(C_89, B_90), k4_xboole_0(C_89, A_91)) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.99/6.42  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.99/6.42  tff(c_1374, plain, (![C_151, B_152, A_153]: (k2_xboole_0(k4_xboole_0(C_151, B_152), k4_xboole_0(C_151, A_153))=k4_xboole_0(C_151, A_153) | ~r1_tarski(A_153, B_152))), inference(resolution, [status(thm)], [c_372, c_14])).
% 13.99/6.42  tff(c_1426, plain, (![B_21, B_152]: (k4_xboole_0(B_21, k4_xboole_0(B_21, B_152))=k2_xboole_0(k4_xboole_0(B_21, B_152), B_21) | ~r1_tarski(k4_xboole_0(B_21, B_152), B_152))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1374])).
% 13.99/6.42  tff(c_10009, plain, (![B_365, B_366]: (k4_xboole_0(B_365, k4_xboole_0(B_365, B_366))=B_365 | ~r1_tarski(k4_xboole_0(B_365, B_366), B_366))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_2, c_1426])).
% 13.99/6.42  tff(c_10097, plain, (![A_367]: (k4_xboole_0(A_367, k4_xboole_0(A_367, A_367))=A_367)), inference(resolution, [status(thm)], [c_18, c_10009])).
% 13.99/6.42  tff(c_10402, plain, (![A_367]: (r1_tarski(A_367, A_367))), inference(superposition, [status(thm), theory('equality')], [c_10097, c_18])).
% 13.99/6.42  tff(c_10480, plain, (![A_368]: (r1_tarski(A_368, A_368))), inference(superposition, [status(thm), theory('equality')], [c_10097, c_18])).
% 13.99/6.42  tff(c_211, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(k2_xboole_0(A_61, B_63), C_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.99/6.42  tff(c_229, plain, (![B_2, C_62, A_1]: (r1_tarski(B_2, C_62) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_211])).
% 13.99/6.42  tff(c_11072, plain, (![B_379, A_380]: (r1_tarski(B_379, k2_xboole_0(A_380, B_379)))), inference(resolution, [status(thm)], [c_10480, c_229])).
% 13.99/6.42  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.99/6.42  tff(c_46, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.99/6.42  tff(c_156, plain, (![B_57, A_58]: (r2_hidden(B_57, A_58) | ~m1_subset_1(B_57, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.99/6.42  tff(c_24, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.99/6.42  tff(c_160, plain, (![B_57, A_25]: (r1_tarski(B_57, A_25) | ~m1_subset_1(B_57, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_156, c_24])).
% 13.99/6.42  tff(c_169, plain, (![B_59, A_60]: (r1_tarski(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(negUnitSimplification, [status(thm)], [c_46, c_160])).
% 13.99/6.42  tff(c_182, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_169])).
% 13.99/6.42  tff(c_190, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_182, c_14])).
% 13.99/6.42  tff(c_214, plain, (![C_62]: (r1_tarski('#skF_4', C_62) | ~r1_tarski('#skF_3', C_62))), inference(superposition, [status(thm), theory('equality')], [c_190, c_211])).
% 13.99/6.42  tff(c_11244, plain, (![A_380]: (r1_tarski('#skF_4', k2_xboole_0(A_380, '#skF_3')))), inference(resolution, [status(thm)], [c_11072, c_214])).
% 13.99/6.42  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.99/6.42  tff(c_164, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_110, c_58])).
% 13.99/6.42  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.99/6.42  tff(c_482, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.99/6.42  tff(c_498, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_482])).
% 13.99/6.42  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(k2_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.99/6.42  tff(c_12771, plain, (![C_398, B_399, C_400, A_401]: (r1_tarski(k4_xboole_0(C_398, B_399), C_400) | ~r1_tarski(k4_xboole_0(C_398, A_401), C_400) | ~r1_tarski(A_401, B_399))), inference(superposition, [status(thm), theory('equality')], [c_1374, c_12])).
% 13.99/6.42  tff(c_13715, plain, (![B_410, C_411]: (r1_tarski(k4_xboole_0('#skF_3', B_410), C_411) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_411) | ~r1_tarski('#skF_5', B_410))), inference(superposition, [status(thm), theory('equality')], [c_498, c_12771])).
% 13.99/6.42  tff(c_499, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_482])).
% 13.99/6.42  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.99/6.42  tff(c_581, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_4') | ~r1_tarski(A_7, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_499, c_8])).
% 13.99/6.42  tff(c_13746, plain, (![B_410]: (r1_xboole_0(k4_xboole_0('#skF_3', B_410), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_5', B_410))), inference(resolution, [status(thm)], [c_13715, c_581])).
% 13.99/6.42  tff(c_33989, plain, (![B_676]: (r1_xboole_0(k4_xboole_0('#skF_3', B_676), '#skF_4') | ~r1_tarski('#skF_5', B_676))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_13746])).
% 13.99/6.42  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.99/6.42  tff(c_35442, plain, (![B_689]: (r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_689)) | ~r1_tarski('#skF_5', B_689))), inference(resolution, [status(thm)], [c_33989, c_4])).
% 13.99/6.42  tff(c_682, plain, (![A_111, B_112, C_113]: (r1_tarski(A_111, B_112) | ~r1_xboole_0(A_111, C_113) | ~r1_tarski(A_111, k2_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.99/6.42  tff(c_717, plain, (![A_111, A_20, B_21]: (r1_tarski(A_111, A_20) | ~r1_xboole_0(A_111, k4_xboole_0(B_21, A_20)) | ~r1_tarski(A_111, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_682])).
% 13.99/6.42  tff(c_35447, plain, (![B_689]: (r1_tarski('#skF_4', B_689) | ~r1_tarski('#skF_4', k2_xboole_0(B_689, '#skF_3')) | ~r1_tarski('#skF_5', B_689))), inference(resolution, [status(thm)], [c_35442, c_717])).
% 13.99/6.42  tff(c_35482, plain, (![B_690]: (r1_tarski('#skF_4', B_690) | ~r1_tarski('#skF_5', B_690))), inference(demodulation, [status(thm), theory('equality')], [c_11244, c_35447])).
% 13.99/6.42  tff(c_35534, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10402, c_35482])).
% 13.99/6.42  tff(c_35562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_35534])).
% 13.99/6.42  tff(c_35563, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 13.99/6.42  tff(c_35564, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 13.99/6.42  tff(c_35969, plain, (![A_763, B_764]: (k4_xboole_0(A_763, B_764)=k3_subset_1(A_763, B_764) | ~m1_subset_1(B_764, k1_zfmisc_1(A_763)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.99/6.42  tff(c_35985, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_35969])).
% 13.99/6.42  tff(c_35986, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_35969])).
% 13.99/6.42  tff(c_16, plain, (![C_17, B_16, A_15]: (r1_tarski(k4_xboole_0(C_17, B_16), k4_xboole_0(C_17, A_15)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.99/6.42  tff(c_37386, plain, (![B_819]: (r1_tarski(k4_xboole_0('#skF_3', B_819), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_819))), inference(superposition, [status(thm), theory('equality')], [c_35986, c_16])).
% 13.99/6.42  tff(c_37404, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_35985, c_37386])).
% 13.99/6.42  tff(c_37412, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35564, c_37404])).
% 13.99/6.42  tff(c_37414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35563, c_37412])).
% 13.99/6.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.99/6.42  
% 13.99/6.42  Inference rules
% 13.99/6.42  ----------------------
% 13.99/6.42  #Ref     : 0
% 13.99/6.42  #Sup     : 9063
% 13.99/6.42  #Fact    : 0
% 13.99/6.42  #Define  : 0
% 13.99/6.42  #Split   : 13
% 13.99/6.42  #Chain   : 0
% 13.99/6.42  #Close   : 0
% 13.99/6.42  
% 13.99/6.42  Ordering : KBO
% 13.99/6.42  
% 13.99/6.42  Simplification rules
% 13.99/6.42  ----------------------
% 13.99/6.42  #Subsume      : 801
% 13.99/6.42  #Demod        : 6016
% 13.99/6.42  #Tautology    : 4297
% 13.99/6.42  #SimpNegUnit  : 100
% 13.99/6.42  #BackRed      : 33
% 13.99/6.42  
% 13.99/6.42  #Partial instantiations: 0
% 13.99/6.42  #Strategies tried      : 1
% 13.99/6.42  
% 13.99/6.42  Timing (in seconds)
% 13.99/6.42  ----------------------
% 13.99/6.42  Preprocessing        : 0.32
% 13.99/6.42  Parsing              : 0.17
% 13.99/6.42  CNF conversion       : 0.02
% 13.99/6.42  Main loop            : 5.32
% 13.99/6.42  Inferencing          : 1.07
% 13.99/6.42  Reduction            : 2.45
% 13.99/6.42  Demodulation         : 1.97
% 13.99/6.42  BG Simplification    : 0.12
% 13.99/6.42  Subsumption          : 1.33
% 13.99/6.42  Abstraction          : 0.15
% 13.99/6.42  MUC search           : 0.00
% 13.99/6.42  Cooper               : 0.00
% 13.99/6.43  Total                : 5.68
% 13.99/6.43  Index Insertion      : 0.00
% 13.99/6.43  Index Deletion       : 0.00
% 13.99/6.43  Index Matching       : 0.00
% 13.99/6.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
