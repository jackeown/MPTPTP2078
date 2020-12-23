%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 277 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 518 expanded)
%              Number of equality atoms :   35 ( 135 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_133,plain,(
    ! [A_42,B_43] :
      ( k7_setfam_1(A_42,k7_setfam_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_133])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k7_setfam_1(A_9,B_10),k1_zfmisc_1(k1_zfmisc_1(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_212,plain,(
    ! [A_57,B_58] :
      ( k6_setfam_1(A_57,k7_setfam_1(A_57,B_58)) = k3_subset_1(A_57,k5_setfam_1(A_57,B_58))
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_629,plain,(
    ! [A_89,B_90] :
      ( k6_setfam_1(A_89,k7_setfam_1(A_89,k7_setfam_1(A_89,B_90))) = k3_subset_1(A_89,k5_setfam_1(A_89,k7_setfam_1(A_89,B_90)))
      | k7_setfam_1(A_89,B_90) = k1_xboole_0
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_636,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_629])).

tff(c_643,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_636])).

tff(c_646,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_274,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(k7_setfam_1(A_60,B_61),C_62)
      | ~ r1_tarski(B_61,k7_setfam_1(A_60,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k1_zfmisc_1(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_332,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k7_setfam_1(A_67,B_68),k1_xboole_0)
      | ~ r1_tarski(B_68,k7_setfam_1(A_67,k1_xboole_0))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(resolution,[status(thm)],[c_12,c_274])).

tff(c_346,plain,(
    ! [A_67] :
      ( r1_tarski(k7_setfam_1(A_67,k1_xboole_0),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k7_setfam_1(A_67,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_332])).

tff(c_353,plain,(
    ! [A_69] : r1_tarski(k7_setfam_1(A_69,k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_346])).

tff(c_37,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | ~ r1_tarski(B_25,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_364,plain,(
    ! [A_69] : k7_setfam_1(A_69,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_353,c_46])).

tff(c_289,plain,(
    ! [B_63] :
      ( r1_tarski(k7_setfam_1('#skF_1',B_63),'#skF_2')
      | ~ r1_tarski(B_63,k7_setfam_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_274])).

tff(c_304,plain,
    ( r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),'#skF_2')
    | ~ r1_tarski(k1_xboole_0,k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_289])).

tff(c_310,plain,(
    r1_tarski(k7_setfam_1('#skF_1',k1_xboole_0),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_304])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_313,plain,
    ( k7_setfam_1('#skF_1',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_314,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_400,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_314])).

tff(c_288,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k7_setfam_1(A_60,B_61),k1_xboole_0)
      | ~ r1_tarski(B_61,k7_setfam_1(A_60,k1_xboole_0))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(resolution,[status(thm)],[c_12,c_274])).

tff(c_432,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k7_setfam_1(A_72,B_73),k1_xboole_0)
      | ~ r1_tarski(B_73,k1_xboole_0)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_288])).

tff(c_513,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k7_setfam_1(A_79,k7_setfam_1(A_79,B_80)),k1_xboole_0)
      | ~ r1_tarski(k7_setfam_1(A_79,B_80),k1_xboole_0)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(resolution,[status(thm)],[c_16,c_432])).

tff(c_535,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_513])).

tff(c_548,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_535])).

tff(c_549,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_548])).

tff(c_648,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_549])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_648])).

tff(c_658,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_316,plain,(
    ! [B_64,A_65,C_66] :
      ( r1_tarski(B_64,k7_setfam_1(A_65,C_66))
      | ~ r1_tarski(k7_setfam_1(A_65,B_64),C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_zfmisc_1(A_65)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_322,plain,(
    ! [C_66] :
      ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),k7_setfam_1('#skF_1',C_66))
      | ~ r1_tarski('#skF_2',C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_316])).

tff(c_660,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_663,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_660])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_663])).

tff(c_669,plain,(
    m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_94,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k5_setfam_1(A_39,B_40),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( k3_subset_1(A_4,k3_subset_1(A_4,B_5)) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [A_39,B_40] :
      ( k3_subset_1(A_39,k3_subset_1(A_39,k5_setfam_1(A_39,B_40))) = k5_setfam_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(resolution,[status(thm)],[c_94,c_10])).

tff(c_711,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_669,c_99])).

tff(c_778,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_711])).

tff(c_779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_778])).

tff(c_780,plain,(
    k7_setfam_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_144,plain,(
    ! [A_42] : k7_setfam_1(A_42,k7_setfam_1(A_42,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_888,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_144])).

tff(c_790,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_144])).

tff(c_307,plain,
    ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_289])).

tff(c_782,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_819,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_782])).

tff(c_829,plain,(
    ! [B_95,A_96,C_97] :
      ( r1_tarski(B_95,k7_setfam_1(A_96,C_97))
      | ~ r1_tarski(k7_setfam_1(A_96,B_95),C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_zfmisc_1(A_96)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_831,plain,(
    ! [C_97] :
      ( r1_tarski('#skF_2',k7_setfam_1('#skF_1',C_97))
      | ~ r1_tarski(k1_xboole_0,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_829])).

tff(c_854,plain,(
    ! [C_98] :
      ( r1_tarski('#skF_2',k7_setfam_1('#skF_1',C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8,c_831])).

tff(c_865,plain,(
    r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_854])).

tff(c_873,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_865])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_873])).

tff(c_877,plain,(
    r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_919,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_877])).

tff(c_922,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_919,c_46])).

tff(c_928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.81/1.43  
% 2.81/1.43  %Foreground sorts:
% 2.81/1.43  
% 2.81/1.43  
% 2.81/1.43  %Background operators:
% 2.81/1.43  
% 2.81/1.43  
% 2.81/1.43  %Foreground operators:
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.43  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.81/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.81/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.43  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.43  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.43  
% 2.81/1.45  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 2.81/1.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.45  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.81/1.45  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.81/1.45  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 2.81/1.45  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.81/1.45  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_setfam_1)).
% 2.81/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.45  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.81/1.45  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.81/1.45  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.45  tff(c_28, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.45  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.45  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.45  tff(c_133, plain, (![A_42, B_43]: (k7_setfam_1(A_42, k7_setfam_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.45  tff(c_143, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_133])).
% 2.81/1.45  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(k7_setfam_1(A_9, B_10), k1_zfmisc_1(k1_zfmisc_1(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.45  tff(c_212, plain, (![A_57, B_58]: (k6_setfam_1(A_57, k7_setfam_1(A_57, B_58))=k3_subset_1(A_57, k5_setfam_1(A_57, B_58)) | k1_xboole_0=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.45  tff(c_629, plain, (![A_89, B_90]: (k6_setfam_1(A_89, k7_setfam_1(A_89, k7_setfam_1(A_89, B_90)))=k3_subset_1(A_89, k5_setfam_1(A_89, k7_setfam_1(A_89, B_90))) | k7_setfam_1(A_89, B_90)=k1_xboole_0 | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(resolution, [status(thm)], [c_16, c_212])).
% 2.81/1.45  tff(c_636, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_629])).
% 2.81/1.45  tff(c_643, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_636])).
% 2.81/1.45  tff(c_646, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_643])).
% 2.81/1.45  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.45  tff(c_274, plain, (![A_60, B_61, C_62]: (r1_tarski(k7_setfam_1(A_60, B_61), C_62) | ~r1_tarski(B_61, k7_setfam_1(A_60, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(k1_zfmisc_1(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.45  tff(c_332, plain, (![A_67, B_68]: (r1_tarski(k7_setfam_1(A_67, B_68), k1_xboole_0) | ~r1_tarski(B_68, k7_setfam_1(A_67, k1_xboole_0)) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(resolution, [status(thm)], [c_12, c_274])).
% 2.81/1.45  tff(c_346, plain, (![A_67]: (r1_tarski(k7_setfam_1(A_67, k1_xboole_0), k1_xboole_0) | ~r1_tarski(k1_xboole_0, k7_setfam_1(A_67, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_332])).
% 2.81/1.45  tff(c_353, plain, (![A_69]: (r1_tarski(k7_setfam_1(A_69, k1_xboole_0), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_346])).
% 2.81/1.45  tff(c_37, plain, (![B_25, A_26]: (B_25=A_26 | ~r1_tarski(B_25, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.45  tff(c_46, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_37])).
% 2.81/1.45  tff(c_364, plain, (![A_69]: (k7_setfam_1(A_69, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_353, c_46])).
% 2.81/1.45  tff(c_289, plain, (![B_63]: (r1_tarski(k7_setfam_1('#skF_1', B_63), '#skF_2') | ~r1_tarski(B_63, k7_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_274])).
% 2.81/1.45  tff(c_304, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), '#skF_2') | ~r1_tarski(k1_xboole_0, k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_289])).
% 2.81/1.45  tff(c_310, plain, (r1_tarski(k7_setfam_1('#skF_1', k1_xboole_0), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_304])).
% 2.81/1.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.45  tff(c_313, plain, (k7_setfam_1('#skF_1', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k7_setfam_1('#skF_1', k1_xboole_0))), inference(resolution, [status(thm)], [c_310, c_2])).
% 2.81/1.45  tff(c_314, plain, (~r1_tarski('#skF_2', k7_setfam_1('#skF_1', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_313])).
% 2.81/1.45  tff(c_400, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_364, c_314])).
% 2.81/1.45  tff(c_288, plain, (![A_60, B_61]: (r1_tarski(k7_setfam_1(A_60, B_61), k1_xboole_0) | ~r1_tarski(B_61, k7_setfam_1(A_60, k1_xboole_0)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(resolution, [status(thm)], [c_12, c_274])).
% 2.81/1.45  tff(c_432, plain, (![A_72, B_73]: (r1_tarski(k7_setfam_1(A_72, B_73), k1_xboole_0) | ~r1_tarski(B_73, k1_xboole_0) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_288])).
% 2.81/1.45  tff(c_513, plain, (![A_79, B_80]: (r1_tarski(k7_setfam_1(A_79, k7_setfam_1(A_79, B_80)), k1_xboole_0) | ~r1_tarski(k7_setfam_1(A_79, B_80), k1_xboole_0) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(resolution, [status(thm)], [c_16, c_432])).
% 2.81/1.45  tff(c_535, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_143, c_513])).
% 2.81/1.45  tff(c_548, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_535])).
% 2.81/1.45  tff(c_549, plain, (~r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_400, c_548])).
% 2.81/1.45  tff(c_648, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_646, c_549])).
% 2.81/1.45  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_648])).
% 2.81/1.45  tff(c_658, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_643])).
% 2.81/1.45  tff(c_316, plain, (![B_64, A_65, C_66]: (r1_tarski(B_64, k7_setfam_1(A_65, C_66)) | ~r1_tarski(k7_setfam_1(A_65, B_64), C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_zfmisc_1(A_65))) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.45  tff(c_322, plain, (![C_66]: (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), k7_setfam_1('#skF_1', C_66)) | ~r1_tarski('#skF_2', C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_143, c_316])).
% 2.81/1.45  tff(c_660, plain, (~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_322])).
% 2.81/1.45  tff(c_663, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_660])).
% 2.81/1.45  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_663])).
% 2.81/1.45  tff(c_669, plain, (m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_322])).
% 2.81/1.45  tff(c_94, plain, (![A_39, B_40]: (m1_subset_1(k5_setfam_1(A_39, B_40), k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.45  tff(c_10, plain, (![A_4, B_5]: (k3_subset_1(A_4, k3_subset_1(A_4, B_5))=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.45  tff(c_99, plain, (![A_39, B_40]: (k3_subset_1(A_39, k3_subset_1(A_39, k5_setfam_1(A_39, B_40)))=k5_setfam_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(resolution, [status(thm)], [c_94, c_10])).
% 2.81/1.45  tff(c_711, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_669, c_99])).
% 2.81/1.45  tff(c_778, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_658, c_711])).
% 2.81/1.45  tff(c_779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_778])).
% 2.81/1.45  tff(c_780, plain, (k7_setfam_1('#skF_1', k1_xboole_0)='#skF_2'), inference(splitRight, [status(thm)], [c_313])).
% 2.81/1.45  tff(c_144, plain, (![A_42]: (k7_setfam_1(A_42, k7_setfam_1(A_42, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_133])).
% 2.81/1.45  tff(c_888, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_780, c_144])).
% 2.81/1.45  tff(c_790, plain, (k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_780, c_144])).
% 2.81/1.45  tff(c_307, plain, (r1_tarski(k7_setfam_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_289])).
% 2.81/1.45  tff(c_782, plain, (~r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_307])).
% 2.81/1.45  tff(c_819, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_790, c_782])).
% 2.81/1.45  tff(c_829, plain, (![B_95, A_96, C_97]: (r1_tarski(B_95, k7_setfam_1(A_96, C_97)) | ~r1_tarski(k7_setfam_1(A_96, B_95), C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_zfmisc_1(A_96))) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_96))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.45  tff(c_831, plain, (![C_97]: (r1_tarski('#skF_2', k7_setfam_1('#skF_1', C_97)) | ~r1_tarski(k1_xboole_0, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_790, c_829])).
% 2.81/1.45  tff(c_854, plain, (![C_98]: (r1_tarski('#skF_2', k7_setfam_1('#skF_1', C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8, c_831])).
% 2.81/1.45  tff(c_865, plain, (r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_854])).
% 2.81/1.45  tff(c_873, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_790, c_865])).
% 2.81/1.45  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_819, c_873])).
% 2.81/1.45  tff(c_877, plain, (r1_tarski('#skF_2', k7_setfam_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_307])).
% 2.81/1.45  tff(c_919, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_888, c_877])).
% 2.81/1.45  tff(c_922, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_919, c_46])).
% 2.81/1.45  tff(c_928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_922])).
% 2.81/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  Inference rules
% 2.81/1.45  ----------------------
% 2.81/1.45  #Ref     : 0
% 2.81/1.45  #Sup     : 204
% 2.81/1.45  #Fact    : 0
% 2.81/1.45  #Define  : 0
% 2.81/1.45  #Split   : 5
% 2.81/1.45  #Chain   : 0
% 2.81/1.45  #Close   : 0
% 2.81/1.45  
% 2.81/1.45  Ordering : KBO
% 2.81/1.45  
% 2.81/1.45  Simplification rules
% 2.81/1.45  ----------------------
% 2.81/1.45  #Subsume      : 19
% 2.81/1.45  #Demod        : 171
% 2.81/1.45  #Tautology    : 110
% 2.81/1.45  #SimpNegUnit  : 11
% 2.81/1.45  #BackRed      : 24
% 2.81/1.45  
% 2.81/1.45  #Partial instantiations: 0
% 2.81/1.45  #Strategies tried      : 1
% 2.81/1.45  
% 2.81/1.45  Timing (in seconds)
% 2.81/1.45  ----------------------
% 2.81/1.45  Preprocessing        : 0.30
% 2.81/1.45  Parsing              : 0.16
% 2.81/1.45  CNF conversion       : 0.02
% 2.81/1.45  Main loop            : 0.39
% 2.81/1.45  Inferencing          : 0.13
% 2.81/1.45  Reduction            : 0.13
% 2.81/1.45  Demodulation         : 0.10
% 2.81/1.45  BG Simplification    : 0.02
% 2.81/1.45  Subsumption          : 0.08
% 2.81/1.45  Abstraction          : 0.02
% 2.81/1.45  MUC search           : 0.00
% 2.81/1.45  Cooper               : 0.00
% 2.81/1.45  Total                : 0.73
% 2.81/1.45  Index Insertion      : 0.00
% 2.81/1.45  Index Deletion       : 0.00
% 2.81/1.45  Index Matching       : 0.00
% 2.81/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
