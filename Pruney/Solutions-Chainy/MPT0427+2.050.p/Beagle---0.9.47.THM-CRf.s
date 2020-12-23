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
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 332 expanded)
%              Number of leaves         :   27 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 701 expanded)
%              Number of equality atoms :   58 ( 299 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_18,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_12] :
      ( k8_setfam_1(A_12,k1_xboole_0) = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [A_12] : k8_setfam_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_253,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k8_setfam_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_265,plain,(
    ! [A_12] :
      ( m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_253])).

tff(c_271,plain,(
    ! [A_67] : m1_subset_1(A_67,k1_zfmisc_1(A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_265])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_283,plain,(
    ! [A_67] : r1_tarski(A_67,A_67) ),
    inference(resolution,[status(thm)],[c_271,c_28])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_132,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_132])).

tff(c_365,plain,(
    ! [A_79,B_80] :
      ( k8_setfam_1(A_79,B_80) = k6_setfam_1(A_79,B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_388,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_365])).

tff(c_403,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_388])).

tff(c_409,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_149,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_132])).

tff(c_391,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_365])).

tff(c_405,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_391])).

tff(c_510,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_405])).

tff(c_511,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_424,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_3') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_44])).

tff(c_515,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_4') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_424])).

tff(c_36,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_466,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_36])).

tff(c_537,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_466])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_537])).

tff(c_541,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_543,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_466])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k8_setfam_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_547,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_24])).

tff(c_551,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_547])).

tff(c_558,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_551,c_28])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_558])).

tff(c_565,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),k1_setfam_1(A_23))
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_564,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_566,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_567,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_565])).

tff(c_284,plain,(
    ! [A_68] : r1_tarski(A_68,A_68) ),
    inference(resolution,[status(thm)],[c_271,c_28])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_293,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_284,c_10])).

tff(c_571,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_293])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,B_47)
      | ~ r2_hidden(C_48,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_806,plain,(
    ! [C_113,B_114,A_115] :
      ( ~ r2_hidden(C_113,B_114)
      | ~ r2_hidden(C_113,A_115)
      | k4_xboole_0(A_115,B_114) != A_115 ) ),
    inference(resolution,[status(thm)],[c_16,c_128])).

tff(c_1624,plain,(
    ! [A_195,B_196,A_197] :
      ( ~ r2_hidden('#skF_1'(A_195,B_196),A_197)
      | k4_xboole_0(A_197,A_195) != A_197
      | r1_xboole_0(A_195,B_196) ) ),
    inference(resolution,[status(thm)],[c_6,c_806])).

tff(c_1627,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1624])).

tff(c_1641,plain,(
    ! [A_198,B_199] :
      ( A_198 != '#skF_4'
      | r1_xboole_0(A_198,B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_1627])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1648,plain,(
    ! [A_198,B_199] :
      ( k4_xboole_0(A_198,B_199) = A_198
      | A_198 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1641,c_14])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1757,plain,(
    ! [B_202,A_203] :
      ( k4_xboole_0(B_202,A_203) != B_202
      | r1_xboole_0(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_4,c_1624])).

tff(c_1825,plain,(
    ! [A_206,B_207] :
      ( k4_xboole_0(A_206,B_207) = A_206
      | k4_xboole_0(B_207,A_206) != B_207 ) ),
    inference(resolution,[status(thm)],[c_1757,c_14])).

tff(c_1858,plain,(
    ! [B_208,A_209] :
      ( k4_xboole_0(B_208,A_209) = B_208
      | A_209 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_1825])).

tff(c_76,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_579,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_93])).

tff(c_1919,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1858,c_579])).

tff(c_1972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_1919])).

tff(c_1973,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_1983,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_36])).

tff(c_2013,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_1983])).

tff(c_2016,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2013])).

tff(c_2022,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2016])).

tff(c_2024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_2022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:41:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.77  
% 3.99/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.99/1.77  
% 3.99/1.77  %Foreground sorts:
% 3.99/1.77  
% 3.99/1.77  
% 3.99/1.77  %Background operators:
% 3.99/1.77  
% 3.99/1.77  
% 3.99/1.77  %Foreground operators:
% 3.99/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.99/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.77  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.99/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.99/1.77  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.77  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.99/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.99/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.99/1.77  
% 3.99/1.79  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.99/1.79  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.99/1.79  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.99/1.79  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.99/1.79  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.99/1.79  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.99/1.79  tff(f_90, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.99/1.79  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.99/1.79  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.99/1.79  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.99/1.79  tff(c_18, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.79  tff(c_20, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.99/1.79  tff(c_44, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 3.99/1.79  tff(c_253, plain, (![A_65, B_66]: (m1_subset_1(k8_setfam_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.99/1.79  tff(c_265, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_44, c_253])).
% 3.99/1.79  tff(c_271, plain, (![A_67]: (m1_subset_1(A_67, k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_265])).
% 3.99/1.79  tff(c_28, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.99/1.79  tff(c_283, plain, (![A_67]: (r1_tarski(A_67, A_67))), inference(resolution, [status(thm)], [c_271, c_28])).
% 3.99/1.79  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.99/1.79  tff(c_132, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.99/1.79  tff(c_148, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_132])).
% 3.99/1.79  tff(c_365, plain, (![A_79, B_80]: (k8_setfam_1(A_79, B_80)=k6_setfam_1(A_79, B_80) | k1_xboole_0=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.99/1.79  tff(c_388, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_365])).
% 3.99/1.79  tff(c_403, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_388])).
% 3.99/1.79  tff(c_409, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_403])).
% 3.99/1.79  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.99/1.79  tff(c_149, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_132])).
% 3.99/1.79  tff(c_391, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_365])).
% 3.99/1.79  tff(c_405, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_391])).
% 3.99/1.79  tff(c_510, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_409, c_405])).
% 3.99/1.79  tff(c_511, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_510])).
% 3.99/1.79  tff(c_424, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_3')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_409, c_44])).
% 3.99/1.79  tff(c_515, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_4')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_511, c_424])).
% 3.99/1.79  tff(c_36, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.99/1.79  tff(c_466, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_36])).
% 3.99/1.79  tff(c_537, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_466])).
% 3.99/1.79  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_537])).
% 3.99/1.79  tff(c_541, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_510])).
% 3.99/1.79  tff(c_543, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_466])).
% 3.99/1.79  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(k8_setfam_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.99/1.79  tff(c_547, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_541, c_24])).
% 3.99/1.79  tff(c_551, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_547])).
% 3.99/1.79  tff(c_558, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_551, c_28])).
% 3.99/1.79  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_558])).
% 3.99/1.79  tff(c_565, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_403])).
% 3.99/1.79  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.99/1.79  tff(c_34, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), k1_setfam_1(A_23)) | k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.99/1.79  tff(c_564, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_403])).
% 3.99/1.79  tff(c_566, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_405])).
% 3.99/1.79  tff(c_567, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_565])).
% 3.99/1.79  tff(c_284, plain, (![A_68]: (r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_271, c_28])).
% 3.99/1.79  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.99/1.79  tff(c_293, plain, (![A_68]: (k4_xboole_0(A_68, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_284, c_10])).
% 3.99/1.79  tff(c_571, plain, (![A_68]: (k4_xboole_0(A_68, A_68)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_293])).
% 3.99/1.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.79  tff(c_16, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.99/1.79  tff(c_128, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, B_47) | ~r2_hidden(C_48, A_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.79  tff(c_806, plain, (![C_113, B_114, A_115]: (~r2_hidden(C_113, B_114) | ~r2_hidden(C_113, A_115) | k4_xboole_0(A_115, B_114)!=A_115)), inference(resolution, [status(thm)], [c_16, c_128])).
% 3.99/1.79  tff(c_1624, plain, (![A_195, B_196, A_197]: (~r2_hidden('#skF_1'(A_195, B_196), A_197) | k4_xboole_0(A_197, A_195)!=A_197 | r1_xboole_0(A_195, B_196))), inference(resolution, [status(thm)], [c_6, c_806])).
% 3.99/1.79  tff(c_1627, plain, (![A_1, B_2]: (k4_xboole_0(A_1, A_1)!=A_1 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_1624])).
% 3.99/1.79  tff(c_1641, plain, (![A_198, B_199]: (A_198!='#skF_4' | r1_xboole_0(A_198, B_199))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_1627])).
% 3.99/1.79  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.99/1.79  tff(c_1648, plain, (![A_198, B_199]: (k4_xboole_0(A_198, B_199)=A_198 | A_198!='#skF_4')), inference(resolution, [status(thm)], [c_1641, c_14])).
% 3.99/1.79  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.79  tff(c_1757, plain, (![B_202, A_203]: (k4_xboole_0(B_202, A_203)!=B_202 | r1_xboole_0(A_203, B_202))), inference(resolution, [status(thm)], [c_4, c_1624])).
% 3.99/1.79  tff(c_1825, plain, (![A_206, B_207]: (k4_xboole_0(A_206, B_207)=A_206 | k4_xboole_0(B_207, A_206)!=B_207)), inference(resolution, [status(thm)], [c_1757, c_14])).
% 3.99/1.79  tff(c_1858, plain, (![B_208, A_209]: (k4_xboole_0(B_208, A_209)=B_208 | A_209!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1648, c_1825])).
% 3.99/1.79  tff(c_76, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.99/1.79  tff(c_93, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_76])).
% 3.99/1.79  tff(c_579, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_93])).
% 3.99/1.79  tff(c_1919, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1858, c_579])).
% 3.99/1.79  tff(c_1972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_567, c_1919])).
% 3.99/1.79  tff(c_1973, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_405])).
% 3.99/1.79  tff(c_1983, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_36])).
% 3.99/1.79  tff(c_2013, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_1983])).
% 3.99/1.79  tff(c_2016, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_2013])).
% 3.99/1.79  tff(c_2022, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2016])).
% 3.99/1.79  tff(c_2024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_2022])).
% 3.99/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.79  
% 3.99/1.79  Inference rules
% 3.99/1.79  ----------------------
% 3.99/1.79  #Ref     : 0
% 3.99/1.79  #Sup     : 444
% 3.99/1.79  #Fact    : 0
% 3.99/1.79  #Define  : 0
% 3.99/1.79  #Split   : 4
% 3.99/1.79  #Chain   : 0
% 3.99/1.79  #Close   : 0
% 3.99/1.79  
% 3.99/1.79  Ordering : KBO
% 3.99/1.79  
% 3.99/1.79  Simplification rules
% 3.99/1.79  ----------------------
% 3.99/1.79  #Subsume      : 39
% 3.99/1.79  #Demod        : 173
% 3.99/1.79  #Tautology    : 214
% 3.99/1.79  #SimpNegUnit  : 10
% 3.99/1.79  #BackRed      : 52
% 3.99/1.79  
% 3.99/1.79  #Partial instantiations: 0
% 3.99/1.79  #Strategies tried      : 1
% 3.99/1.79  
% 3.99/1.79  Timing (in seconds)
% 3.99/1.79  ----------------------
% 3.99/1.79  Preprocessing        : 0.36
% 3.99/1.79  Parsing              : 0.20
% 3.99/1.79  CNF conversion       : 0.02
% 3.99/1.79  Main loop            : 0.56
% 3.99/1.79  Inferencing          : 0.21
% 3.99/1.80  Reduction            : 0.17
% 3.99/1.80  Demodulation         : 0.12
% 3.99/1.80  BG Simplification    : 0.03
% 3.99/1.80  Subsumption          : 0.10
% 3.99/1.80  Abstraction          : 0.03
% 3.99/1.80  MUC search           : 0.00
% 3.99/1.80  Cooper               : 0.00
% 3.99/1.80  Total                : 0.96
% 3.99/1.80  Index Insertion      : 0.00
% 3.99/1.80  Index Deletion       : 0.00
% 3.99/1.80  Index Matching       : 0.00
% 3.99/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
