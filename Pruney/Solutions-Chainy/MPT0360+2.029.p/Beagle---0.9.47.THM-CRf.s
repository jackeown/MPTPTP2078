%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 17.39s
% Output     : CNFRefutation 17.55s
% Verified   : 
% Statistics : Number of formulae       :  173 (2222 expanded)
%              Number of leaves         :   35 ( 751 expanded)
%              Depth                    :   23
%              Number of atoms          :  272 (3781 expanded)
%              Number of equality atoms :   43 (1161 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_34,plain,(
    ! [A_20] : k2_subset_1(A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [A_23] : m1_subset_1(k2_subset_1(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [A_32] :
      ( r1_tarski(k3_subset_1(A_32,k2_subset_1(A_32)),k2_subset_1(A_32))
      | ~ m1_subset_1(k2_subset_1(A_32),k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    ! [A_32] : r1_tarski(k3_subset_1(A_32,k2_subset_1(A_32)),k2_subset_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_59,plain,(
    ! [A_32] : r1_tarski(k3_subset_1(A_32,A_32),A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_58])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_102,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_125,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_161,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31210,plain,(
    ! [B_448,A_449] :
      ( r1_tarski(B_448,A_449)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(A_449))
      | v1_xboole_0(k1_zfmisc_1(A_449)) ) ),
    inference(resolution,[status(thm)],[c_161,c_14])).

tff(c_31233,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_31210])).

tff(c_31243,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_31233])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31446,plain,(
    ! [A_457] :
      ( r1_tarski(A_457,'#skF_4')
      | ~ r1_tarski(A_457,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_31243,c_10])).

tff(c_31473,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_31446])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_153,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_150])).

tff(c_60,plain,(
    ! [A_23] : m1_subset_1(A_23,k1_zfmisc_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_334,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k3_subset_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_348,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k3_subset_1(A_23,A_23) ),
    inference(resolution,[status(thm)],[c_60,c_334])).

tff(c_356,plain,(
    ! [A_23] : k3_subset_1(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_348])).

tff(c_382,plain,(
    ! [A_32] : r1_tarski(k1_xboole_0,A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_59])).

tff(c_31250,plain,(
    ! [A_450] :
      ( r1_tarski(A_450,A_450)
      | v1_xboole_0(k1_zfmisc_1(A_450)) ) ),
    inference(resolution,[status(thm)],[c_60,c_31210])).

tff(c_116,plain,(
    ! [C_49,A_50] :
      ( r2_hidden(C_49,k1_zfmisc_1(A_50))
      | ~ r1_tarski(C_49,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_50,C_49] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_50))
      | ~ r1_tarski(C_49,A_50) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_31338,plain,(
    ! [C_452,A_453] :
      ( ~ r1_tarski(C_452,A_453)
      | r1_tarski(A_453,A_453) ) ),
    inference(resolution,[status(thm)],[c_31250,c_124])).

tff(c_31369,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(resolution,[status(thm)],[c_382,c_31338])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(B_53,A_54)
      | ~ r2_hidden(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_134,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_52,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_31685,plain,(
    ! [C_469,A_470,B_471] :
      ( r1_tarski(C_469,k3_subset_1(A_470,B_471))
      | ~ r1_tarski(B_471,k3_subset_1(A_470,C_469))
      | ~ m1_subset_1(C_469,k1_zfmisc_1(A_470))
      | ~ m1_subset_1(B_471,k1_zfmisc_1(A_470)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_31710,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_31685])).

tff(c_31727,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_31710])).

tff(c_31763,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_31727])).

tff(c_31766,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_31763])).

tff(c_31772,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31473,c_31766])).

tff(c_31774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_31772])).

tff(c_31776,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_31727])).

tff(c_40,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k3_subset_1(A_24,B_25),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [C_42,A_43] :
      ( r1_tarski(C_42,A_43)
      | ~ r2_hidden(C_42,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [A_43] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_43)),A_43)
      | v1_xboole_0(k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_4,c_95])).

tff(c_176,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,'#skF_6')
      | ~ r1_tarski(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_176])).

tff(c_198,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')),'#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_100,c_189])).

tff(c_218,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_226,plain,(
    ! [C_69] : ~ r1_tarski(C_69,'#skF_5') ),
    inference(resolution,[status(thm)],[c_218,c_124])).

tff(c_237,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_59,c_226])).

tff(c_239,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_383,plain,(
    ! [A_81] : k3_subset_1(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_348])).

tff(c_388,plain,(
    ! [A_81] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(A_81,k1_zfmisc_1(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_40])).

tff(c_393,plain,(
    ! [A_81] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_388])).

tff(c_358,plain,(
    ! [A_79,B_80] :
      ( k3_subset_1(A_79,k3_subset_1(A_79,B_80)) = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_374,plain,(
    ! [A_23] : k3_subset_1(A_23,k3_subset_1(A_23,A_23)) = A_23 ),
    inference(resolution,[status(thm)],[c_60,c_358])).

tff(c_31054,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_xboole_0) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_374])).

tff(c_31701,plain,(
    ! [C_469,A_470] :
      ( r1_tarski(C_469,k3_subset_1(A_470,k1_xboole_0))
      | ~ m1_subset_1(C_469,k1_zfmisc_1(A_470))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_470)) ) ),
    inference(resolution,[status(thm)],[c_382,c_31685])).

tff(c_31728,plain,(
    ! [C_472,A_473] :
      ( r1_tarski(C_472,A_473)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(A_473)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_31054,c_31701])).

tff(c_31755,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k3_subset_1(A_24,B_25),A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_40,c_31728])).

tff(c_187,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_62,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_176])).

tff(c_48,plain,(
    ! [A_32,B_33] :
      ( k2_subset_1(A_32) = B_33
      | ~ r1_tarski(k3_subset_1(A_32,B_33),B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_31099,plain,(
    ! [B_440,A_441] :
      ( B_440 = A_441
      | ~ r1_tarski(k3_subset_1(A_441,B_440),B_440)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(A_441)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48])).

tff(c_32480,plain,(
    ! [A_500] :
      ( k3_subset_1('#skF_4','#skF_6') = A_500
      | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1(A_500))
      | ~ r1_tarski(k3_subset_1(A_500,k3_subset_1('#skF_4','#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_187,c_31099])).

tff(c_32497,plain,
    ( k3_subset_1('#skF_4','#skF_6') = '#skF_5'
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_31755,c_32480])).

tff(c_32506,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32497])).

tff(c_32595,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_32506])).

tff(c_32601,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_32595])).

tff(c_42,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_subset_1(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_31790,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_31776,c_42])).

tff(c_375,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_358])).

tff(c_31105,plain,
    ( k3_subset_1('#skF_4','#skF_6') = '#skF_4'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_6'))
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_31099])).

tff(c_32332,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_31105])).

tff(c_32338,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_32332])).

tff(c_32348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32338])).

tff(c_32350,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_31105])).

tff(c_31698,plain,(
    ! [B_471] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4',B_471))
      | ~ r1_tarski(B_471,'#skF_6')
      | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_471,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_31685])).

tff(c_32612,plain,(
    ! [B_504] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4',B_504))
      | ~ r1_tarski(B_504,'#skF_6')
      | ~ m1_subset_1(B_504,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32350,c_31698])).

tff(c_32629,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_6'),'#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31790,c_32612])).

tff(c_32650,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_32601,c_32629])).

tff(c_33212,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32650])).

tff(c_33218,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_33212])).

tff(c_33228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31776,c_33218])).

tff(c_33230,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32650])).

tff(c_31775,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_31727])).

tff(c_31822,plain,(
    ! [A_478] :
      ( r1_tarski(A_478,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_478,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_31775,c_10])).

tff(c_32996,plain,(
    ! [A_513,A_514] :
      ( r1_tarski(A_513,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_513,A_514)
      | ~ r1_tarski(A_514,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_31822,c_10])).

tff(c_33052,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_32996])).

tff(c_33093,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31369,c_33052])).

tff(c_32507,plain,(
    ! [A_501,B_502] :
      ( k3_subset_1(A_501,k3_subset_1(A_501,k3_subset_1(A_501,B_502))) = k3_subset_1(A_501,B_502)
      | ~ m1_subset_1(B_502,k1_zfmisc_1(A_501)) ) ),
    inference(resolution,[status(thm)],[c_40,c_358])).

tff(c_61,plain,(
    ! [B_33,A_32] :
      ( B_33 = A_32
      | ~ r1_tarski(k3_subset_1(A_32,B_33),B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48])).

tff(c_49030,plain,(
    ! [A_754,B_755] :
      ( k3_subset_1(A_754,k3_subset_1(A_754,B_755)) = A_754
      | ~ r1_tarski(k3_subset_1(A_754,B_755),k3_subset_1(A_754,k3_subset_1(A_754,B_755)))
      | ~ m1_subset_1(k3_subset_1(A_754,k3_subset_1(A_754,B_755)),k1_zfmisc_1(A_754))
      | ~ m1_subset_1(B_755,k1_zfmisc_1(A_754)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32507,c_61])).

tff(c_49101,plain,
    ( k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))) = '#skF_4'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31790,c_49030])).

tff(c_49143,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33230,c_33230,c_31790,c_33093,c_31790,c_31790,c_49101])).

tff(c_31718,plain,(
    ! [C_469,A_470] :
      ( r1_tarski(C_469,A_470)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(A_470)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_31054,c_31701])).

tff(c_33251,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_33230,c_31718])).

tff(c_33267,plain,(
    ! [A_519] :
      ( r1_tarski(A_519,'#skF_4')
      | ~ r1_tarski(A_519,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_33251,c_10])).

tff(c_33344,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))),'#skF_4')
    | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_100,c_33267])).

tff(c_37647,plain,(
    v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_33344])).

tff(c_37666,plain,(
    ! [C_49] : ~ r1_tarski(C_49,k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_37647,c_124])).

tff(c_238,plain,(
    r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_259,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_6')
      | ~ r1_tarski(A_73,'#skF_1'(k1_zfmisc_1('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_238,c_10])).

tff(c_268,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))),'#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_100,c_259])).

tff(c_35963,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_36121,plain,(
    ! [C_566] : ~ r1_tarski(C_566,'#skF_1'(k1_zfmisc_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_35963,c_124])).

tff(c_36175,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_31369,c_36121])).

tff(c_36176,plain,(
    r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_31843,plain,(
    ! [A_9,A_478] :
      ( r1_tarski(A_9,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_9,A_478)
      | ~ r1_tarski(A_478,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_31822,c_10])).

tff(c_36183,plain,
    ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))),k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_36176,c_31843])).

tff(c_36197,plain,(
    r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))),k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31369,c_36183])).

tff(c_37715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37666,c_36197])).

tff(c_37717,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_33344])).

tff(c_42989,plain,(
    ! [B_675] :
      ( r1_tarski(k3_subset_1(k3_subset_1('#skF_4','#skF_5'),B_675),'#skF_4')
      | ~ m1_subset_1(B_675,k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_31755,c_33267])).

tff(c_43029,plain,
    ( k3_subset_1('#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_42989,c_61])).

tff(c_43100,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_43029])).

tff(c_43103,plain,
    ( v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5')))
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_134,c_43100])).

tff(c_43109,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_37717,c_43103])).

tff(c_49173,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49143,c_43109])).

tff(c_49206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31369,c_49173])).

tff(c_49207,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_43029])).

tff(c_31198,plain,(
    ! [C_446,A_447] :
      ( m1_subset_1(C_446,k1_zfmisc_1(A_447))
      | v1_xboole_0(k1_zfmisc_1(A_447))
      | ~ r1_tarski(C_446,A_447) ) ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_33592,plain,(
    ! [A_527,C_528] :
      ( k3_subset_1(A_527,k3_subset_1(A_527,C_528)) = C_528
      | v1_xboole_0(k1_zfmisc_1(A_527))
      | ~ r1_tarski(C_528,A_527) ) ),
    inference(resolution,[status(thm)],[c_31198,c_42])).

tff(c_35480,plain,(
    ! [C_555,A_556,C_557] :
      ( ~ r1_tarski(C_555,A_556)
      | k3_subset_1(A_556,k3_subset_1(A_556,C_557)) = C_557
      | ~ r1_tarski(C_557,A_556) ) ),
    inference(resolution,[status(thm)],[c_33592,c_124])).

tff(c_35604,plain,(
    ! [A_32,C_557] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,C_557)) = C_557
      | ~ r1_tarski(C_557,A_32) ) ),
    inference(resolution,[status(thm)],[c_382,c_35480])).

tff(c_49291,plain,
    ( k3_subset_1('#skF_4','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_49207,c_35604])).

tff(c_49348,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31473,c_356,c_49291])).

tff(c_49350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_49348])).

tff(c_49352,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_49357,plain,(
    ! [A_756,C_757] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_756))
      | ~ r1_tarski(C_757,A_756) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_49361,plain,(
    ! [C_758] : ~ r1_tarski(C_758,'#skF_4') ),
    inference(resolution,[status(thm)],[c_49352,c_49357])).

tff(c_49366,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_59,c_49361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.39/8.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.39/8.29  
% 17.39/8.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.39/8.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 17.39/8.29  
% 17.39/8.29  %Foreground sorts:
% 17.39/8.29  
% 17.39/8.29  
% 17.39/8.29  %Background operators:
% 17.39/8.29  
% 17.39/8.29  
% 17.39/8.29  %Foreground operators:
% 17.39/8.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.39/8.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.39/8.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.39/8.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.39/8.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.39/8.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.39/8.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.39/8.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.39/8.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.39/8.29  tff('#skF_5', type, '#skF_5': $i).
% 17.39/8.29  tff('#skF_6', type, '#skF_6': $i).
% 17.39/8.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.39/8.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.39/8.29  tff('#skF_4', type, '#skF_4': $i).
% 17.39/8.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.39/8.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.39/8.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.39/8.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 17.39/8.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.39/8.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.39/8.29  
% 17.55/8.32  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 17.55/8.32  tff(f_71, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 17.55/8.32  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 17.55/8.32  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 17.55/8.32  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 17.55/8.32  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 17.55/8.32  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 17.55/8.32  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 17.55/8.32  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 17.55/8.32  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.55/8.32  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 17.55/8.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.55/8.32  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 17.55/8.32  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 17.55/8.32  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 17.55/8.32  tff(c_34, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.55/8.32  tff(c_38, plain, (![A_23]: (m1_subset_1(k2_subset_1(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.55/8.32  tff(c_46, plain, (![A_32]: (r1_tarski(k3_subset_1(A_32, k2_subset_1(A_32)), k2_subset_1(A_32)) | ~m1_subset_1(k2_subset_1(A_32), k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 17.55/8.32  tff(c_58, plain, (![A_32]: (r1_tarski(k3_subset_1(A_32, k2_subset_1(A_32)), k2_subset_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 17.55/8.32  tff(c_59, plain, (![A_32]: (r1_tarski(k3_subset_1(A_32, A_32), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_58])).
% 17.55/8.32  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.55/8.32  tff(c_54, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.55/8.32  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.55/8.32  tff(c_102, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.55/8.32  tff(c_114, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_102])).
% 17.55/8.32  tff(c_125, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_114])).
% 17.55/8.32  tff(c_161, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | ~m1_subset_1(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.55/8.32  tff(c_14, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.55/8.32  tff(c_31210, plain, (![B_448, A_449]: (r1_tarski(B_448, A_449) | ~m1_subset_1(B_448, k1_zfmisc_1(A_449)) | v1_xboole_0(k1_zfmisc_1(A_449)))), inference(resolution, [status(thm)], [c_161, c_14])).
% 17.55/8.32  tff(c_31233, plain, (r1_tarski('#skF_6', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_31210])).
% 17.55/8.32  tff(c_31243, plain, (r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_125, c_31233])).
% 17.55/8.32  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.55/8.32  tff(c_31446, plain, (![A_457]: (r1_tarski(A_457, '#skF_4') | ~r1_tarski(A_457, '#skF_6'))), inference(resolution, [status(thm)], [c_31243, c_10])).
% 17.55/8.32  tff(c_31473, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_31446])).
% 17.55/8.32  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.55/8.32  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.55/8.32  tff(c_141, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.55/8.32  tff(c_150, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_141])).
% 17.55/8.32  tff(c_153, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_150])).
% 17.55/8.32  tff(c_60, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 17.55/8.32  tff(c_334, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k3_subset_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.55/8.32  tff(c_348, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k3_subset_1(A_23, A_23))), inference(resolution, [status(thm)], [c_60, c_334])).
% 17.55/8.32  tff(c_356, plain, (![A_23]: (k3_subset_1(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_348])).
% 17.55/8.32  tff(c_382, plain, (![A_32]: (r1_tarski(k1_xboole_0, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_59])).
% 17.55/8.32  tff(c_31250, plain, (![A_450]: (r1_tarski(A_450, A_450) | v1_xboole_0(k1_zfmisc_1(A_450)))), inference(resolution, [status(thm)], [c_60, c_31210])).
% 17.55/8.32  tff(c_116, plain, (![C_49, A_50]: (r2_hidden(C_49, k1_zfmisc_1(A_50)) | ~r1_tarski(C_49, A_50))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.55/8.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.55/8.32  tff(c_124, plain, (![A_50, C_49]: (~v1_xboole_0(k1_zfmisc_1(A_50)) | ~r1_tarski(C_49, A_50))), inference(resolution, [status(thm)], [c_116, c_2])).
% 17.55/8.32  tff(c_31338, plain, (![C_452, A_453]: (~r1_tarski(C_452, A_453) | r1_tarski(A_453, A_453))), inference(resolution, [status(thm)], [c_31250, c_124])).
% 17.55/8.32  tff(c_31369, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(resolution, [status(thm)], [c_382, c_31338])).
% 17.55/8.32  tff(c_16, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.55/8.32  tff(c_127, plain, (![B_53, A_54]: (m1_subset_1(B_53, A_54) | ~r2_hidden(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.55/8.32  tff(c_134, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_16, c_127])).
% 17.55/8.32  tff(c_52, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.55/8.32  tff(c_31685, plain, (![C_469, A_470, B_471]: (r1_tarski(C_469, k3_subset_1(A_470, B_471)) | ~r1_tarski(B_471, k3_subset_1(A_470, C_469)) | ~m1_subset_1(C_469, k1_zfmisc_1(A_470)) | ~m1_subset_1(B_471, k1_zfmisc_1(A_470)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 17.55/8.32  tff(c_31710, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_31685])).
% 17.55/8.32  tff(c_31727, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_31710])).
% 17.55/8.32  tff(c_31763, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_31727])).
% 17.55/8.32  tff(c_31766, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_134, c_31763])).
% 17.55/8.32  tff(c_31772, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31473, c_31766])).
% 17.55/8.32  tff(c_31774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_31772])).
% 17.55/8.32  tff(c_31776, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_31727])).
% 17.55/8.32  tff(c_40, plain, (![A_24, B_25]: (m1_subset_1(k3_subset_1(A_24, B_25), k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.55/8.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.55/8.32  tff(c_95, plain, (![C_42, A_43]: (r1_tarski(C_42, A_43) | ~r2_hidden(C_42, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.55/8.32  tff(c_100, plain, (![A_43]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_43)), A_43) | v1_xboole_0(k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_4, c_95])).
% 17.55/8.32  tff(c_176, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.55/8.32  tff(c_189, plain, (![A_65]: (r1_tarski(A_65, '#skF_6') | ~r1_tarski(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_176])).
% 17.55/8.32  tff(c_198, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')), '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_100, c_189])).
% 17.55/8.32  tff(c_218, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_198])).
% 17.55/8.32  tff(c_226, plain, (![C_69]: (~r1_tarski(C_69, '#skF_5'))), inference(resolution, [status(thm)], [c_218, c_124])).
% 17.55/8.32  tff(c_237, plain, $false, inference(resolution, [status(thm)], [c_59, c_226])).
% 17.55/8.32  tff(c_239, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_198])).
% 17.55/8.32  tff(c_383, plain, (![A_81]: (k3_subset_1(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_348])).
% 17.55/8.32  tff(c_388, plain, (![A_81]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_81)) | ~m1_subset_1(A_81, k1_zfmisc_1(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_383, c_40])).
% 17.55/8.32  tff(c_393, plain, (![A_81]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_388])).
% 17.55/8.32  tff(c_358, plain, (![A_79, B_80]: (k3_subset_1(A_79, k3_subset_1(A_79, B_80))=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.55/8.32  tff(c_374, plain, (![A_23]: (k3_subset_1(A_23, k3_subset_1(A_23, A_23))=A_23)), inference(resolution, [status(thm)], [c_60, c_358])).
% 17.55/8.32  tff(c_31054, plain, (![A_23]: (k3_subset_1(A_23, k1_xboole_0)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_356, c_374])).
% 17.55/8.32  tff(c_31701, plain, (![C_469, A_470]: (r1_tarski(C_469, k3_subset_1(A_470, k1_xboole_0)) | ~m1_subset_1(C_469, k1_zfmisc_1(A_470)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_470)))), inference(resolution, [status(thm)], [c_382, c_31685])).
% 17.55/8.32  tff(c_31728, plain, (![C_472, A_473]: (r1_tarski(C_472, A_473) | ~m1_subset_1(C_472, k1_zfmisc_1(A_473)))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_31054, c_31701])).
% 17.55/8.32  tff(c_31755, plain, (![A_24, B_25]: (r1_tarski(k3_subset_1(A_24, B_25), A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_40, c_31728])).
% 17.55/8.32  tff(c_187, plain, (![A_62]: (r1_tarski(A_62, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_62, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_176])).
% 17.55/8.32  tff(c_48, plain, (![A_32, B_33]: (k2_subset_1(A_32)=B_33 | ~r1_tarski(k3_subset_1(A_32, B_33), B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 17.55/8.32  tff(c_31099, plain, (![B_440, A_441]: (B_440=A_441 | ~r1_tarski(k3_subset_1(A_441, B_440), B_440) | ~m1_subset_1(B_440, k1_zfmisc_1(A_441)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48])).
% 17.55/8.32  tff(c_32480, plain, (![A_500]: (k3_subset_1('#skF_4', '#skF_6')=A_500 | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1(A_500)) | ~r1_tarski(k3_subset_1(A_500, k3_subset_1('#skF_4', '#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_187, c_31099])).
% 17.55/8.32  tff(c_32497, plain, (k3_subset_1('#skF_4', '#skF_6')='#skF_5' | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_31755, c_32480])).
% 17.55/8.32  tff(c_32506, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_32497])).
% 17.55/8.32  tff(c_32595, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_134, c_32506])).
% 17.55/8.32  tff(c_32601, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_239, c_32595])).
% 17.55/8.32  tff(c_42, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_subset_1(A_26, B_27))=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.55/8.32  tff(c_31790, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_31776, c_42])).
% 17.55/8.32  tff(c_375, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_56, c_358])).
% 17.55/8.32  tff(c_31105, plain, (k3_subset_1('#skF_4', '#skF_6')='#skF_4' | ~r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_6')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_31099])).
% 17.55/8.32  tff(c_32332, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_31105])).
% 17.55/8.32  tff(c_32338, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_32332])).
% 17.55/8.32  tff(c_32348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_32338])).
% 17.55/8.32  tff(c_32350, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_31105])).
% 17.55/8.32  tff(c_31698, plain, (![B_471]: (r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', B_471)) | ~r1_tarski(B_471, '#skF_6') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_471, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_375, c_31685])).
% 17.55/8.32  tff(c_32612, plain, (![B_504]: (r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', B_504)) | ~r1_tarski(B_504, '#skF_6') | ~m1_subset_1(B_504, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32350, c_31698])).
% 17.55/8.32  tff(c_32629, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_6'), '#skF_5') | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_31790, c_32612])).
% 17.55/8.32  tff(c_32650, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_32601, c_32629])).
% 17.55/8.32  tff(c_33212, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_32650])).
% 17.55/8.32  tff(c_33218, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_33212])).
% 17.55/8.32  tff(c_33228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31776, c_33218])).
% 17.55/8.32  tff(c_33230, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_32650])).
% 17.55/8.32  tff(c_31775, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_31727])).
% 17.55/8.32  tff(c_31822, plain, (![A_478]: (r1_tarski(A_478, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_478, '#skF_6'))), inference(resolution, [status(thm)], [c_31775, c_10])).
% 17.55/8.32  tff(c_32996, plain, (![A_513, A_514]: (r1_tarski(A_513, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_513, A_514) | ~r1_tarski(A_514, '#skF_6'))), inference(resolution, [status(thm)], [c_31822, c_10])).
% 17.55/8.32  tff(c_33052, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_32996])).
% 17.55/8.32  tff(c_33093, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_31369, c_33052])).
% 17.55/8.32  tff(c_32507, plain, (![A_501, B_502]: (k3_subset_1(A_501, k3_subset_1(A_501, k3_subset_1(A_501, B_502)))=k3_subset_1(A_501, B_502) | ~m1_subset_1(B_502, k1_zfmisc_1(A_501)))), inference(resolution, [status(thm)], [c_40, c_358])).
% 17.55/8.32  tff(c_61, plain, (![B_33, A_32]: (B_33=A_32 | ~r1_tarski(k3_subset_1(A_32, B_33), B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48])).
% 17.55/8.32  tff(c_49030, plain, (![A_754, B_755]: (k3_subset_1(A_754, k3_subset_1(A_754, B_755))=A_754 | ~r1_tarski(k3_subset_1(A_754, B_755), k3_subset_1(A_754, k3_subset_1(A_754, B_755))) | ~m1_subset_1(k3_subset_1(A_754, k3_subset_1(A_754, B_755)), k1_zfmisc_1(A_754)) | ~m1_subset_1(B_755, k1_zfmisc_1(A_754)))), inference(superposition, [status(thm), theory('equality')], [c_32507, c_61])).
% 17.55/8.32  tff(c_49101, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))='#skF_4' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))) | ~m1_subset_1(k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_31790, c_49030])).
% 17.55/8.32  tff(c_49143, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33230, c_33230, c_31790, c_33093, c_31790, c_31790, c_49101])).
% 17.55/8.32  tff(c_31718, plain, (![C_469, A_470]: (r1_tarski(C_469, A_470) | ~m1_subset_1(C_469, k1_zfmisc_1(A_470)))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_31054, c_31701])).
% 17.55/8.32  tff(c_33251, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_33230, c_31718])).
% 17.55/8.32  tff(c_33267, plain, (![A_519]: (r1_tarski(A_519, '#skF_4') | ~r1_tarski(A_519, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_33251, c_10])).
% 17.55/8.32  tff(c_33344, plain, (r1_tarski('#skF_1'(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))), '#skF_4') | v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_100, c_33267])).
% 17.55/8.32  tff(c_37647, plain, (v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_33344])).
% 17.55/8.32  tff(c_37666, plain, (![C_49]: (~r1_tarski(C_49, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_37647, c_124])).
% 17.55/8.32  tff(c_238, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_198])).
% 17.55/8.32  tff(c_259, plain, (![A_73]: (r1_tarski(A_73, '#skF_6') | ~r1_tarski(A_73, '#skF_1'(k1_zfmisc_1('#skF_5'))))), inference(resolution, [status(thm)], [c_238, c_10])).
% 17.55/8.32  tff(c_268, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))), '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5'))))), inference(resolution, [status(thm)], [c_100, c_259])).
% 17.55/8.32  tff(c_35963, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5'))))), inference(splitLeft, [status(thm)], [c_268])).
% 17.55/8.32  tff(c_36121, plain, (![C_566]: (~r1_tarski(C_566, '#skF_1'(k1_zfmisc_1('#skF_5'))))), inference(resolution, [status(thm)], [c_35963, c_124])).
% 17.55/8.32  tff(c_36175, plain, $false, inference(resolution, [status(thm)], [c_31369, c_36121])).
% 17.55/8.32  tff(c_36176, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))), '#skF_6')), inference(splitRight, [status(thm)], [c_268])).
% 17.55/8.32  tff(c_31843, plain, (![A_9, A_478]: (r1_tarski(A_9, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_9, A_478) | ~r1_tarski(A_478, '#skF_6'))), inference(resolution, [status(thm)], [c_31822, c_10])).
% 17.55/8.32  tff(c_36183, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))), k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_36176, c_31843])).
% 17.55/8.32  tff(c_36197, plain, (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_1'(k1_zfmisc_1('#skF_5')))), k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_31369, c_36183])).
% 17.55/8.32  tff(c_37715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37666, c_36197])).
% 17.55/8.32  tff(c_37717, plain, (~v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_33344])).
% 17.55/8.32  tff(c_42989, plain, (![B_675]: (r1_tarski(k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), B_675), '#skF_4') | ~m1_subset_1(B_675, k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_31755, c_33267])).
% 17.55/8.32  tff(c_43029, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_42989, c_61])).
% 17.55/8.32  tff(c_43100, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_43029])).
% 17.55/8.32  tff(c_43103, plain, (v1_xboole_0(k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))) | ~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_43100])).
% 17.55/8.32  tff(c_43109, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_37717, c_43103])).
% 17.55/8.32  tff(c_49173, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49143, c_43109])).
% 17.55/8.32  tff(c_49206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31369, c_49173])).
% 17.55/8.32  tff(c_49207, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_43029])).
% 17.55/8.32  tff(c_31198, plain, (![C_446, A_447]: (m1_subset_1(C_446, k1_zfmisc_1(A_447)) | v1_xboole_0(k1_zfmisc_1(A_447)) | ~r1_tarski(C_446, A_447))), inference(resolution, [status(thm)], [c_16, c_127])).
% 17.55/8.32  tff(c_33592, plain, (![A_527, C_528]: (k3_subset_1(A_527, k3_subset_1(A_527, C_528))=C_528 | v1_xboole_0(k1_zfmisc_1(A_527)) | ~r1_tarski(C_528, A_527))), inference(resolution, [status(thm)], [c_31198, c_42])).
% 17.55/8.32  tff(c_35480, plain, (![C_555, A_556, C_557]: (~r1_tarski(C_555, A_556) | k3_subset_1(A_556, k3_subset_1(A_556, C_557))=C_557 | ~r1_tarski(C_557, A_556))), inference(resolution, [status(thm)], [c_33592, c_124])).
% 17.55/8.32  tff(c_35604, plain, (![A_32, C_557]: (k3_subset_1(A_32, k3_subset_1(A_32, C_557))=C_557 | ~r1_tarski(C_557, A_32))), inference(resolution, [status(thm)], [c_382, c_35480])).
% 17.55/8.32  tff(c_49291, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_49207, c_35604])).
% 17.55/8.32  tff(c_49348, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31473, c_356, c_49291])).
% 17.55/8.32  tff(c_49350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_49348])).
% 17.55/8.32  tff(c_49352, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_114])).
% 17.55/8.32  tff(c_49357, plain, (![A_756, C_757]: (~v1_xboole_0(k1_zfmisc_1(A_756)) | ~r1_tarski(C_757, A_756))), inference(resolution, [status(thm)], [c_116, c_2])).
% 17.55/8.32  tff(c_49361, plain, (![C_758]: (~r1_tarski(C_758, '#skF_4'))), inference(resolution, [status(thm)], [c_49352, c_49357])).
% 17.55/8.32  tff(c_49366, plain, $false, inference(resolution, [status(thm)], [c_59, c_49361])).
% 17.55/8.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.55/8.32  
% 17.55/8.32  Inference rules
% 17.55/8.32  ----------------------
% 17.55/8.32  #Ref     : 0
% 17.55/8.32  #Sup     : 11038
% 17.55/8.32  #Fact    : 0
% 17.55/8.32  #Define  : 0
% 17.55/8.32  #Split   : 69
% 17.55/8.32  #Chain   : 0
% 17.55/8.32  #Close   : 0
% 17.55/8.32  
% 17.55/8.32  Ordering : KBO
% 17.55/8.32  
% 17.55/8.32  Simplification rules
% 17.55/8.32  ----------------------
% 17.55/8.32  #Subsume      : 3733
% 17.55/8.32  #Demod        : 6640
% 17.55/8.32  #Tautology    : 2721
% 17.55/8.32  #SimpNegUnit  : 644
% 17.55/8.32  #BackRed      : 524
% 17.55/8.32  
% 17.55/8.32  #Partial instantiations: 0
% 17.55/8.32  #Strategies tried      : 1
% 17.55/8.32  
% 17.55/8.32  Timing (in seconds)
% 17.55/8.32  ----------------------
% 17.55/8.32  Preprocessing        : 0.31
% 17.55/8.32  Parsing              : 0.16
% 17.55/8.32  CNF conversion       : 0.02
% 17.55/8.32  Main loop            : 7.24
% 17.55/8.32  Inferencing          : 1.36
% 17.55/8.32  Reduction            : 2.91
% 17.55/8.32  Demodulation         : 2.22
% 17.55/8.32  BG Simplification    : 0.15
% 17.55/8.32  Subsumption          : 2.36
% 17.55/8.32  Abstraction          : 0.27
% 17.55/8.32  MUC search           : 0.00
% 17.55/8.32  Cooper               : 0.00
% 17.55/8.32  Total                : 7.60
% 17.55/8.32  Index Insertion      : 0.00
% 17.55/8.32  Index Deletion       : 0.00
% 17.55/8.32  Index Matching       : 0.00
% 17.55/8.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
