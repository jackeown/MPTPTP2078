%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:48 EST 2020

% Result     : Theorem 29.65s
% Output     : CNFRefutation 29.75s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 181 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 286 expanded)
%              Number of equality atoms :   33 (  76 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_60,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    ! [A_38] : ~ v1_xboole_0(k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_525,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,A_82)
      | ~ m1_subset_1(B_81,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [C_33,A_29] :
      ( r1_tarski(C_33,A_29)
      | ~ r2_hidden(C_33,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_532,plain,(
    ! [B_81,A_29] :
      ( r1_tarski(B_81,A_29)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_29))
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_525,c_32])).

tff(c_537,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_532])).

tff(c_553,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_537])).

tff(c_189,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    ! [A_62,B_63] : r1_tarski(k3_xboole_0(A_62,B_63),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_20])).

tff(c_16,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_264,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_293,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_264])).

tff(c_322,plain,(
    ! [B_72] : k3_xboole_0(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_198,c_293])).

tff(c_342,plain,(
    ! [B_4] : k3_xboole_0(B_4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_322])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_866,plain,(
    ! [C_104,B_105,A_106] :
      ( r1_tarski(k4_xboole_0(C_104,B_105),k4_xboole_0(C_104,A_106))
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5188,plain,(
    ! [A_280,B_281,B_282] :
      ( r1_tarski(k4_xboole_0(A_280,B_281),k3_xboole_0(A_280,B_282))
      | ~ r1_tarski(k4_xboole_0(A_280,B_282),B_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_866])).

tff(c_5225,plain,(
    ! [B_4,B_281] :
      ( r1_tarski(k4_xboole_0(B_4,B_281),k1_xboole_0)
      | ~ r1_tarski(k4_xboole_0(B_4,k1_xboole_0),B_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_5188])).

tff(c_5421,plain,(
    ! [B_285,B_286] :
      ( r1_tarski(k4_xboole_0(B_285,B_286),k1_xboole_0)
      | ~ r1_tarski(B_285,B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5225])).

tff(c_291,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_264])).

tff(c_5542,plain,(
    ! [B_290,B_291] :
      ( k4_xboole_0(B_290,B_291) = k1_xboole_0
      | ~ r1_tarski(B_290,B_291) ) ),
    inference(resolution,[status(thm)],[c_5421,c_291])).

tff(c_5892,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_553,c_5542])).

tff(c_6062,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5892,c_28])).

tff(c_6094,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_22,c_6062])).

tff(c_1944,plain,(
    ! [A_161,B_162] :
      ( k4_xboole_0(A_161,B_162) = k3_subset_1(A_161,B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1960,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1944])).

tff(c_1998,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_28])).

tff(c_6172,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_1998])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_554,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_537])).

tff(c_5891,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_554,c_5542])).

tff(c_5963,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5891,c_28])).

tff(c_5987,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5963])).

tff(c_1961,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1944])).

tff(c_2047,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1961,c_28])).

tff(c_2053,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2047])).

tff(c_6097,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5987,c_2053])).

tff(c_66,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_210,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_66])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( r1_tarski(k4_xboole_0(C_15,B_14),k4_xboole_0(C_15,A_13))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6717,plain,(
    ! [A_300,C_301,A_302,B_303] :
      ( r1_tarski(A_300,k4_xboole_0(C_301,A_302))
      | ~ r1_tarski(A_300,k4_xboole_0(C_301,B_303))
      | ~ r1_tarski(A_302,B_303) ) ),
    inference(resolution,[status(thm)],[c_866,c_14])).

tff(c_93630,plain,(
    ! [C_954,B_955,A_956,A_957] :
      ( r1_tarski(k4_xboole_0(C_954,B_955),k4_xboole_0(C_954,A_956))
      | ~ r1_tarski(A_956,A_957)
      | ~ r1_tarski(A_957,B_955) ) ),
    inference(resolution,[status(thm)],[c_18,c_6717])).

tff(c_103451,plain,(
    ! [C_1015,B_1016] :
      ( r1_tarski(k4_xboole_0(C_1015,B_1016),k4_xboole_0(C_1015,k3_subset_1('#skF_3','#skF_5')))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),B_1016) ) ),
    inference(resolution,[status(thm)],[c_210,c_93630])).

tff(c_103739,plain,
    ( r1_tarski('#skF_4',k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')))
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6097,c_103451])).

tff(c_103956,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6172,c_103739])).

tff(c_103958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_103956])).

tff(c_103959,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_103960,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_105351,plain,(
    ! [A_1109,B_1110] :
      ( k4_xboole_0(A_1109,B_1110) = k3_subset_1(A_1109,B_1110)
      | ~ m1_subset_1(B_1110,k1_zfmisc_1(A_1109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_105367,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_105351])).

tff(c_105368,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_105351])).

tff(c_108734,plain,(
    ! [B_1238] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_1238),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_1238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105368,c_18])).

tff(c_108757,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_105367,c_108734])).

tff(c_108778,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103960,c_108757])).

tff(c_108780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103959,c_108778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.65/19.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.75/19.76  
% 29.75/19.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.75/19.76  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 29.75/19.76  
% 29.75/19.76  %Foreground sorts:
% 29.75/19.76  
% 29.75/19.76  
% 29.75/19.76  %Background operators:
% 29.75/19.76  
% 29.75/19.76  
% 29.75/19.76  %Foreground operators:
% 29.75/19.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.75/19.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.75/19.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.75/19.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.75/19.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.75/19.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.75/19.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 29.75/19.76  tff('#skF_5', type, '#skF_5': $i).
% 29.75/19.76  tff('#skF_3', type, '#skF_3': $i).
% 29.75/19.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.75/19.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.75/19.76  tff('#skF_4', type, '#skF_4': $i).
% 29.75/19.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.75/19.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.75/19.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.75/19.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.75/19.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.75/19.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 29.75/19.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.75/19.76  
% 29.75/19.78  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 29.75/19.78  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.75/19.78  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 29.75/19.78  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 29.75/19.78  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 29.75/19.78  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 29.75/19.78  tff(f_72, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 29.75/19.78  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 29.75/19.78  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 29.75/19.78  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 29.75/19.78  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 29.75/19.78  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 29.75/19.78  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 29.75/19.78  tff(c_60, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.75/19.78  tff(c_125, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 29.75/19.78  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.75/19.78  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.75/19.78  tff(c_22, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 29.75/19.78  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.75/19.78  tff(c_54, plain, (![A_38]: (~v1_xboole_0(k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.75/19.78  tff(c_525, plain, (![B_81, A_82]: (r2_hidden(B_81, A_82) | ~m1_subset_1(B_81, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_85])).
% 29.75/19.78  tff(c_32, plain, (![C_33, A_29]: (r1_tarski(C_33, A_29) | ~r2_hidden(C_33, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 29.75/19.78  tff(c_532, plain, (![B_81, A_29]: (r1_tarski(B_81, A_29) | ~m1_subset_1(B_81, k1_zfmisc_1(A_29)) | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(resolution, [status(thm)], [c_525, c_32])).
% 29.75/19.78  tff(c_537, plain, (![B_83, A_84]: (r1_tarski(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)))), inference(negUnitSimplification, [status(thm)], [c_54, c_532])).
% 29.75/19.78  tff(c_553, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_537])).
% 29.75/19.78  tff(c_189, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 29.75/19.78  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.75/19.78  tff(c_198, plain, (![A_62, B_63]: (r1_tarski(k3_xboole_0(A_62, B_63), A_62))), inference(superposition, [status(thm), theory('equality')], [c_189, c_20])).
% 29.75/19.78  tff(c_16, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.75/19.78  tff(c_264, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.75/19.78  tff(c_293, plain, (![A_71]: (k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_264])).
% 29.75/19.78  tff(c_322, plain, (![B_72]: (k3_xboole_0(k1_xboole_0, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_198, c_293])).
% 29.75/19.78  tff(c_342, plain, (![B_4]: (k3_xboole_0(B_4, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_322])).
% 29.75/19.78  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 29.75/19.78  tff(c_866, plain, (![C_104, B_105, A_106]: (r1_tarski(k4_xboole_0(C_104, B_105), k4_xboole_0(C_104, A_106)) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.75/19.78  tff(c_5188, plain, (![A_280, B_281, B_282]: (r1_tarski(k4_xboole_0(A_280, B_281), k3_xboole_0(A_280, B_282)) | ~r1_tarski(k4_xboole_0(A_280, B_282), B_281))), inference(superposition, [status(thm), theory('equality')], [c_28, c_866])).
% 29.75/19.78  tff(c_5225, plain, (![B_4, B_281]: (r1_tarski(k4_xboole_0(B_4, B_281), k1_xboole_0) | ~r1_tarski(k4_xboole_0(B_4, k1_xboole_0), B_281))), inference(superposition, [status(thm), theory('equality')], [c_342, c_5188])).
% 29.75/19.78  tff(c_5421, plain, (![B_285, B_286]: (r1_tarski(k4_xboole_0(B_285, B_286), k1_xboole_0) | ~r1_tarski(B_285, B_286))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5225])).
% 29.75/19.78  tff(c_291, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_264])).
% 29.75/19.78  tff(c_5542, plain, (![B_290, B_291]: (k4_xboole_0(B_290, B_291)=k1_xboole_0 | ~r1_tarski(B_290, B_291))), inference(resolution, [status(thm)], [c_5421, c_291])).
% 29.75/19.78  tff(c_5892, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_553, c_5542])).
% 29.75/19.78  tff(c_6062, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5892, c_28])).
% 29.75/19.78  tff(c_6094, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_22, c_6062])).
% 29.75/19.78  tff(c_1944, plain, (![A_161, B_162]: (k4_xboole_0(A_161, B_162)=k3_subset_1(A_161, B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 29.75/19.78  tff(c_1960, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_1944])).
% 29.75/19.78  tff(c_1998, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1960, c_28])).
% 29.75/19.78  tff(c_6172, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6094, c_1998])).
% 29.75/19.78  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.75/19.78  tff(c_554, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_537])).
% 29.75/19.78  tff(c_5891, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_554, c_5542])).
% 29.75/19.78  tff(c_5963, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5891, c_28])).
% 29.75/19.78  tff(c_5987, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5963])).
% 29.75/19.78  tff(c_1961, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1944])).
% 29.75/19.78  tff(c_2047, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1961, c_28])).
% 29.75/19.78  tff(c_2053, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2047])).
% 29.75/19.78  tff(c_6097, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5987, c_2053])).
% 29.75/19.78  tff(c_66, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.75/19.78  tff(c_210, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_125, c_66])).
% 29.75/19.78  tff(c_18, plain, (![C_15, B_14, A_13]: (r1_tarski(k4_xboole_0(C_15, B_14), k4_xboole_0(C_15, A_13)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.75/19.78  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.75/19.78  tff(c_6717, plain, (![A_300, C_301, A_302, B_303]: (r1_tarski(A_300, k4_xboole_0(C_301, A_302)) | ~r1_tarski(A_300, k4_xboole_0(C_301, B_303)) | ~r1_tarski(A_302, B_303))), inference(resolution, [status(thm)], [c_866, c_14])).
% 29.75/19.78  tff(c_93630, plain, (![C_954, B_955, A_956, A_957]: (r1_tarski(k4_xboole_0(C_954, B_955), k4_xboole_0(C_954, A_956)) | ~r1_tarski(A_956, A_957) | ~r1_tarski(A_957, B_955))), inference(resolution, [status(thm)], [c_18, c_6717])).
% 29.75/19.78  tff(c_103451, plain, (![C_1015, B_1016]: (r1_tarski(k4_xboole_0(C_1015, B_1016), k4_xboole_0(C_1015, k3_subset_1('#skF_3', '#skF_5'))) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), B_1016))), inference(resolution, [status(thm)], [c_210, c_93630])).
% 29.75/19.78  tff(c_103739, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6097, c_103451])).
% 29.75/19.78  tff(c_103956, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6172, c_103739])).
% 29.75/19.78  tff(c_103958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_103956])).
% 29.75/19.78  tff(c_103959, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 29.75/19.78  tff(c_103960, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 29.75/19.78  tff(c_105351, plain, (![A_1109, B_1110]: (k4_xboole_0(A_1109, B_1110)=k3_subset_1(A_1109, B_1110) | ~m1_subset_1(B_1110, k1_zfmisc_1(A_1109)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 29.75/19.78  tff(c_105367, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_105351])).
% 29.75/19.78  tff(c_105368, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_105351])).
% 29.75/19.78  tff(c_108734, plain, (![B_1238]: (r1_tarski(k4_xboole_0('#skF_3', B_1238), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_1238))), inference(superposition, [status(thm), theory('equality')], [c_105368, c_18])).
% 29.75/19.78  tff(c_108757, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_105367, c_108734])).
% 29.75/19.78  tff(c_108778, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103960, c_108757])).
% 29.75/19.78  tff(c_108780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103959, c_108778])).
% 29.75/19.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.75/19.78  
% 29.75/19.78  Inference rules
% 29.75/19.78  ----------------------
% 29.75/19.78  #Ref     : 0
% 29.75/19.78  #Sup     : 26558
% 29.75/19.78  #Fact    : 0
% 29.75/19.78  #Define  : 0
% 29.75/19.78  #Split   : 11
% 29.75/19.78  #Chain   : 0
% 29.75/19.78  #Close   : 0
% 29.75/19.78  
% 29.75/19.78  Ordering : KBO
% 29.75/19.78  
% 29.75/19.78  Simplification rules
% 29.75/19.78  ----------------------
% 29.75/19.78  #Subsume      : 4464
% 29.75/19.78  #Demod        : 21682
% 29.75/19.78  #Tautology    : 13085
% 29.75/19.78  #SimpNegUnit  : 199
% 29.75/19.78  #BackRed      : 8
% 29.75/19.78  
% 29.75/19.78  #Partial instantiations: 0
% 29.75/19.78  #Strategies tried      : 1
% 29.75/19.78  
% 29.75/19.78  Timing (in seconds)
% 29.75/19.78  ----------------------
% 29.75/19.78  Preprocessing        : 0.36
% 29.75/19.78  Parsing              : 0.19
% 29.75/19.78  CNF conversion       : 0.03
% 29.75/19.78  Main loop            : 18.63
% 29.75/19.78  Inferencing          : 1.82
% 29.75/19.78  Reduction            : 11.19
% 29.75/19.78  Demodulation         : 9.88
% 29.75/19.78  BG Simplification    : 0.19
% 29.75/19.78  Subsumption          : 4.67
% 29.75/19.78  Abstraction          : 0.28
% 29.75/19.78  MUC search           : 0.00
% 29.75/19.78  Cooper               : 0.00
% 29.75/19.78  Total                : 19.03
% 29.75/19.78  Index Insertion      : 0.00
% 29.75/19.78  Index Deletion       : 0.00
% 29.75/19.78  Index Matching       : 0.00
% 29.75/19.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
