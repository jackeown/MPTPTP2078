%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 9.66s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 589 expanded)
%              Number of leaves         :   32 ( 208 expanded)
%              Depth                    :   30
%              Number of atoms          :  138 (1115 expanded)
%              Number of equality atoms :   48 ( 169 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_81,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_61,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_448,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(A_76,B_77)
      | k4_xboole_0(A_76,B_77) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_108,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_376,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k3_subset_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_388,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_376])).

tff(c_20,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,k4_xboole_0(C_19,B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_423,plain,(
    ! [A_73] :
      ( r1_xboole_0(A_73,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_73,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_20])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_172,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_44])).

tff(c_428,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_423,c_172])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_428])).

tff(c_438,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_456,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_448,c_438])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_437,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_938,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(A_125,B_126) = k3_subset_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_950,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_938])).

tff(c_14,plain,(
    ! [B_13,A_12,C_14] :
      ( r1_xboole_0(B_13,k4_xboole_0(A_12,C_14))
      | ~ r1_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5600,plain,(
    ! [A_232] :
      ( r1_xboole_0('#skF_1',k4_xboole_0(A_232,'#skF_3'))
      | ~ r1_xboole_0(A_232,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_14])).

tff(c_5650,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_437,c_5600])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_481,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,A_85)
      | ~ m1_subset_1(B_84,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_23] : k3_tarski(k1_zfmisc_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_457,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,k3_tarski(B_79))
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_463,plain,(
    ! [A_78,A_23] :
      ( r1_tarski(A_78,A_23)
      | ~ r2_hidden(A_78,k1_zfmisc_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_457])).

tff(c_485,plain,(
    ! [B_84,A_23] :
      ( r1_tarski(B_84,A_23)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_23))
      | v1_xboole_0(k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_481,c_463])).

tff(c_489,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(B_86,A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_485])).

tff(c_502,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_489])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_510,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_502,c_6])).

tff(c_789,plain,(
    ! [B_113,A_114,C_115] :
      ( r1_xboole_0(B_113,k4_xboole_0(A_114,C_115))
      | ~ r1_xboole_0(A_114,k4_xboole_0(B_113,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_815,plain,(
    ! [C_116,A_117,B_118] :
      ( r1_xboole_0(C_116,k4_xboole_0(A_117,B_118))
      | ~ r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_20,c_789])).

tff(c_843,plain,(
    ! [C_116] :
      ( r1_xboole_0(C_116,k1_xboole_0)
      | ~ r1_tarski('#skF_2','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_815])).

tff(c_858,plain,(
    ! [C_119] : r1_xboole_0(C_119,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_843])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_866,plain,(
    ! [C_119] : k4_xboole_0(C_119,k1_xboole_0) = C_119 ),
    inference(resolution,[status(thm)],[c_858,c_16])).

tff(c_877,plain,(
    ! [C_120] : k4_xboole_0(C_120,k1_xboole_0) = C_120 ),
    inference(resolution,[status(thm)],[c_858,c_16])).

tff(c_885,plain,(
    ! [C_120,A_12] :
      ( r1_xboole_0(C_120,k4_xboole_0(A_12,k1_xboole_0))
      | ~ r1_xboole_0(A_12,C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_14])).

tff(c_896,plain,(
    ! [C_120,A_12] :
      ( r1_xboole_0(C_120,A_12)
      | ~ r1_xboole_0(A_12,C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_885])).

tff(c_5670,plain,(
    r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5650,c_896])).

tff(c_5695,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_5670,c_16])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_515,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_xboole_0(A_88,k4_xboole_0(C_89,B_90))
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1233,plain,(
    ! [A_132,C_133,B_134] :
      ( k4_xboole_0(A_132,k4_xboole_0(C_133,B_134)) = A_132
      | ~ r1_tarski(A_132,B_134) ) ),
    inference(resolution,[status(thm)],[c_515,c_16])).

tff(c_2865,plain,(
    ! [A_178,C_179] :
      ( k4_xboole_0(A_178,C_179) = A_178
      | ~ r1_tarski(A_178,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_1233])).

tff(c_2868,plain,(
    ! [A_3,C_179] :
      ( k4_xboole_0(A_3,C_179) = A_3
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2865])).

tff(c_2873,plain,(
    ! [A_180,C_181] :
      ( k4_xboole_0(A_180,C_181) = A_180
      | k1_xboole_0 != A_180 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_2868])).

tff(c_854,plain,(
    ! [C_116] : r1_xboole_0(C_116,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_843])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_910,plain,(
    ! [C_123,A_124] :
      ( r1_xboole_0(C_123,A_124)
      | ~ r1_xboole_0(A_124,C_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_885])).

tff(c_952,plain,(
    ! [C_127] : r1_xboole_0(k1_xboole_0,C_127) ),
    inference(resolution,[status(thm)],[c_854,c_910])).

tff(c_968,plain,(
    ! [C_128] : k4_xboole_0(k1_xboole_0,C_128) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_952,c_16])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_986,plain,(
    ! [C_128] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_10])).

tff(c_1025,plain,(
    ! [C_129] : k3_xboole_0(k1_xboole_0,C_129) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_986])).

tff(c_1045,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1025])).

tff(c_619,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1448,plain,(
    ! [A_139,B_140] : k4_xboole_0(A_139,k3_xboole_0(A_139,B_140)) = k3_xboole_0(A_139,k4_xboole_0(A_139,B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_619])).

tff(c_1481,plain,(
    ! [B_2] : k3_xboole_0(B_2,k4_xboole_0(B_2,k1_xboole_0)) = k4_xboole_0(B_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_1448])).

tff(c_1513,plain,(
    ! [B_141] : k3_xboole_0(B_141,B_141) = B_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_866,c_1481])).

tff(c_599,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_611,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_599])).

tff(c_1530,plain,(
    ! [B_141] : k5_xboole_0(B_141,B_141) = k4_xboole_0(B_141,B_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_611])).

tff(c_1555,plain,(
    ! [B_142] : k4_xboole_0(B_142,B_142) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1530])).

tff(c_1588,plain,(
    ! [B_142,A_12] :
      ( r1_xboole_0(B_142,k4_xboole_0(A_12,B_142))
      | ~ r1_xboole_0(A_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_14])).

tff(c_1630,plain,(
    ! [B_142,A_12] : r1_xboole_0(B_142,k4_xboole_0(A_12,B_142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_1588])).

tff(c_3139,plain,(
    ! [C_181] : r1_xboole_0(C_181,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2873,c_1630])).

tff(c_803,plain,(
    ! [A_114] :
      ( r1_xboole_0('#skF_2',k4_xboole_0(A_114,'#skF_1'))
      | ~ r1_xboole_0(A_114,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_789])).

tff(c_9510,plain,(
    ! [A_114] : r1_xboole_0('#skF_2',k4_xboole_0(A_114,'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3139,c_803])).

tff(c_15906,plain,(
    r1_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5695,c_9510])).

tff(c_16070,plain,(
    k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_15906,c_16])).

tff(c_16286,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_16070,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16424,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16286,c_8])).

tff(c_16462,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16424])).

tff(c_16464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_16462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.52  
% 9.66/3.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.66/3.52  
% 9.66/3.52  %Foreground sorts:
% 9.66/3.52  
% 9.66/3.52  
% 9.66/3.52  %Background operators:
% 9.66/3.52  
% 9.66/3.52  
% 9.66/3.52  %Foreground operators:
% 9.66/3.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.66/3.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.66/3.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.66/3.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.66/3.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.66/3.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.66/3.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.66/3.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.66/3.52  tff('#skF_2', type, '#skF_2': $i).
% 9.66/3.52  tff('#skF_3', type, '#skF_3': $i).
% 9.66/3.52  tff('#skF_1', type, '#skF_1': $i).
% 9.66/3.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.66/3.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.66/3.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.66/3.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.66/3.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.66/3.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.66/3.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.66/3.52  
% 9.66/3.54  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.66/3.54  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 9.66/3.54  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 9.66/3.54  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 9.66/3.54  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.66/3.54  tff(f_45, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 9.66/3.54  tff(f_81, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.66/3.54  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.66/3.54  tff(f_61, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 9.66/3.54  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.66/3.54  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.66/3.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.66/3.54  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.66/3.54  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.66/3.54  tff(c_448, plain, (![A_76, B_77]: (r1_tarski(A_76, B_77) | k4_xboole_0(A_76, B_77)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.66/3.54  tff(c_50, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.66/3.54  tff(c_108, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 9.66/3.54  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.66/3.54  tff(c_376, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k3_subset_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.66/3.54  tff(c_388, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_376])).
% 9.66/3.54  tff(c_20, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, k4_xboole_0(C_19, B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.66/3.54  tff(c_423, plain, (![A_73]: (r1_xboole_0(A_73, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_73, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_388, c_20])).
% 9.66/3.54  tff(c_44, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.66/3.54  tff(c_172, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_44])).
% 9.66/3.54  tff(c_428, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_423, c_172])).
% 9.66/3.54  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_428])).
% 9.66/3.54  tff(c_438, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 9.66/3.54  tff(c_456, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_448, c_438])).
% 9.66/3.54  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.66/3.54  tff(c_437, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 9.66/3.54  tff(c_938, plain, (![A_125, B_126]: (k4_xboole_0(A_125, B_126)=k3_subset_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.66/3.54  tff(c_950, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_938])).
% 9.66/3.54  tff(c_14, plain, (![B_13, A_12, C_14]: (r1_xboole_0(B_13, k4_xboole_0(A_12, C_14)) | ~r1_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.66/3.54  tff(c_5600, plain, (![A_232]: (r1_xboole_0('#skF_1', k4_xboole_0(A_232, '#skF_3')) | ~r1_xboole_0(A_232, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_950, c_14])).
% 9.66/3.54  tff(c_5650, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_437, c_5600])).
% 9.66/3.54  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.66/3.54  tff(c_38, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.66/3.54  tff(c_481, plain, (![B_84, A_85]: (r2_hidden(B_84, A_85) | ~m1_subset_1(B_84, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.66/3.54  tff(c_26, plain, (![A_23]: (k3_tarski(k1_zfmisc_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.66/3.54  tff(c_457, plain, (![A_78, B_79]: (r1_tarski(A_78, k3_tarski(B_79)) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.66/3.54  tff(c_463, plain, (![A_78, A_23]: (r1_tarski(A_78, A_23) | ~r2_hidden(A_78, k1_zfmisc_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_457])).
% 9.66/3.54  tff(c_485, plain, (![B_84, A_23]: (r1_tarski(B_84, A_23) | ~m1_subset_1(B_84, k1_zfmisc_1(A_23)) | v1_xboole_0(k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_481, c_463])).
% 9.66/3.54  tff(c_489, plain, (![B_86, A_87]: (r1_tarski(B_86, A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)))), inference(negUnitSimplification, [status(thm)], [c_38, c_485])).
% 9.66/3.54  tff(c_502, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_489])).
% 9.66/3.54  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.66/3.54  tff(c_510, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_502, c_6])).
% 9.66/3.54  tff(c_789, plain, (![B_113, A_114, C_115]: (r1_xboole_0(B_113, k4_xboole_0(A_114, C_115)) | ~r1_xboole_0(A_114, k4_xboole_0(B_113, C_115)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.66/3.54  tff(c_815, plain, (![C_116, A_117, B_118]: (r1_xboole_0(C_116, k4_xboole_0(A_117, B_118)) | ~r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_20, c_789])).
% 9.66/3.54  tff(c_843, plain, (![C_116]: (r1_xboole_0(C_116, k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_510, c_815])).
% 9.66/3.54  tff(c_858, plain, (![C_119]: (r1_xboole_0(C_119, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_843])).
% 9.66/3.54  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.66/3.54  tff(c_866, plain, (![C_119]: (k4_xboole_0(C_119, k1_xboole_0)=C_119)), inference(resolution, [status(thm)], [c_858, c_16])).
% 9.66/3.54  tff(c_877, plain, (![C_120]: (k4_xboole_0(C_120, k1_xboole_0)=C_120)), inference(resolution, [status(thm)], [c_858, c_16])).
% 9.66/3.54  tff(c_885, plain, (![C_120, A_12]: (r1_xboole_0(C_120, k4_xboole_0(A_12, k1_xboole_0)) | ~r1_xboole_0(A_12, C_120))), inference(superposition, [status(thm), theory('equality')], [c_877, c_14])).
% 9.66/3.54  tff(c_896, plain, (![C_120, A_12]: (r1_xboole_0(C_120, A_12) | ~r1_xboole_0(A_12, C_120))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_885])).
% 9.66/3.54  tff(c_5670, plain, (r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_5650, c_896])).
% 9.66/3.54  tff(c_5695, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_5670, c_16])).
% 9.66/3.54  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.66/3.54  tff(c_515, plain, (![A_88, C_89, B_90]: (r1_xboole_0(A_88, k4_xboole_0(C_89, B_90)) | ~r1_tarski(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.66/3.54  tff(c_1233, plain, (![A_132, C_133, B_134]: (k4_xboole_0(A_132, k4_xboole_0(C_133, B_134))=A_132 | ~r1_tarski(A_132, B_134))), inference(resolution, [status(thm)], [c_515, c_16])).
% 9.66/3.54  tff(c_2865, plain, (![A_178, C_179]: (k4_xboole_0(A_178, C_179)=A_178 | ~r1_tarski(A_178, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_866, c_1233])).
% 9.66/3.54  tff(c_2868, plain, (![A_3, C_179]: (k4_xboole_0(A_3, C_179)=A_3 | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2865])).
% 9.66/3.54  tff(c_2873, plain, (![A_180, C_181]: (k4_xboole_0(A_180, C_181)=A_180 | k1_xboole_0!=A_180)), inference(demodulation, [status(thm), theory('equality')], [c_866, c_2868])).
% 9.66/3.54  tff(c_854, plain, (![C_116]: (r1_xboole_0(C_116, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_843])).
% 9.66/3.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.66/3.54  tff(c_910, plain, (![C_123, A_124]: (r1_xboole_0(C_123, A_124) | ~r1_xboole_0(A_124, C_123))), inference(demodulation, [status(thm), theory('equality')], [c_866, c_885])).
% 9.66/3.54  tff(c_952, plain, (![C_127]: (r1_xboole_0(k1_xboole_0, C_127))), inference(resolution, [status(thm)], [c_854, c_910])).
% 9.66/3.54  tff(c_968, plain, (![C_128]: (k4_xboole_0(k1_xboole_0, C_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_952, c_16])).
% 9.66/3.54  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.66/3.54  tff(c_986, plain, (![C_128]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, C_128))), inference(superposition, [status(thm), theory('equality')], [c_968, c_10])).
% 9.66/3.54  tff(c_1025, plain, (![C_129]: (k3_xboole_0(k1_xboole_0, C_129)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_866, c_986])).
% 9.66/3.54  tff(c_1045, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1025])).
% 9.66/3.54  tff(c_619, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.66/3.54  tff(c_1448, plain, (![A_139, B_140]: (k4_xboole_0(A_139, k3_xboole_0(A_139, B_140))=k3_xboole_0(A_139, k4_xboole_0(A_139, B_140)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_619])).
% 9.66/3.54  tff(c_1481, plain, (![B_2]: (k3_xboole_0(B_2, k4_xboole_0(B_2, k1_xboole_0))=k4_xboole_0(B_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1045, c_1448])).
% 9.66/3.54  tff(c_1513, plain, (![B_141]: (k3_xboole_0(B_141, B_141)=B_141)), inference(demodulation, [status(thm), theory('equality')], [c_866, c_866, c_1481])).
% 9.66/3.54  tff(c_599, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.66/3.54  tff(c_611, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_599])).
% 9.66/3.54  tff(c_1530, plain, (![B_141]: (k5_xboole_0(B_141, B_141)=k4_xboole_0(B_141, B_141))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_611])).
% 9.66/3.54  tff(c_1555, plain, (![B_142]: (k4_xboole_0(B_142, B_142)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1530])).
% 9.66/3.54  tff(c_1588, plain, (![B_142, A_12]: (r1_xboole_0(B_142, k4_xboole_0(A_12, B_142)) | ~r1_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_14])).
% 9.66/3.54  tff(c_1630, plain, (![B_142, A_12]: (r1_xboole_0(B_142, k4_xboole_0(A_12, B_142)))), inference(demodulation, [status(thm), theory('equality')], [c_854, c_1588])).
% 9.66/3.54  tff(c_3139, plain, (![C_181]: (r1_xboole_0(C_181, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2873, c_1630])).
% 9.66/3.54  tff(c_803, plain, (![A_114]: (r1_xboole_0('#skF_2', k4_xboole_0(A_114, '#skF_1')) | ~r1_xboole_0(A_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_510, c_789])).
% 9.66/3.54  tff(c_9510, plain, (![A_114]: (r1_xboole_0('#skF_2', k4_xboole_0(A_114, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3139, c_803])).
% 9.66/3.54  tff(c_15906, plain, (r1_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5695, c_9510])).
% 9.66/3.54  tff(c_16070, plain, (k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_15906, c_16])).
% 9.66/3.54  tff(c_16286, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_16070, c_10])).
% 9.66/3.54  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.66/3.54  tff(c_16424, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16286, c_8])).
% 9.66/3.54  tff(c_16462, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16424])).
% 9.66/3.54  tff(c_16464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_16462])).
% 9.66/3.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.54  
% 9.66/3.54  Inference rules
% 9.66/3.54  ----------------------
% 9.66/3.54  #Ref     : 1
% 9.66/3.54  #Sup     : 4469
% 9.66/3.54  #Fact    : 0
% 9.66/3.54  #Define  : 0
% 9.66/3.54  #Split   : 15
% 9.66/3.54  #Chain   : 0
% 9.66/3.54  #Close   : 0
% 9.66/3.54  
% 9.66/3.54  Ordering : KBO
% 9.66/3.54  
% 9.66/3.54  Simplification rules
% 9.66/3.54  ----------------------
% 9.66/3.54  #Subsume      : 1369
% 9.66/3.54  #Demod        : 2332
% 9.66/3.54  #Tautology    : 1650
% 9.66/3.54  #SimpNegUnit  : 194
% 9.66/3.54  #BackRed      : 14
% 9.66/3.54  
% 9.66/3.54  #Partial instantiations: 0
% 9.66/3.54  #Strategies tried      : 1
% 9.66/3.54  
% 9.66/3.54  Timing (in seconds)
% 9.66/3.54  ----------------------
% 9.66/3.54  Preprocessing        : 0.33
% 9.66/3.54  Parsing              : 0.18
% 9.66/3.54  CNF conversion       : 0.02
% 9.66/3.54  Main loop            : 2.44
% 9.66/3.54  Inferencing          : 0.59
% 9.66/3.54  Reduction            : 1.07
% 9.66/3.54  Demodulation         : 0.82
% 9.66/3.54  BG Simplification    : 0.06
% 9.66/3.54  Subsumption          : 0.55
% 9.66/3.54  Abstraction          : 0.08
% 9.66/3.54  MUC search           : 0.00
% 9.66/3.54  Cooper               : 0.00
% 9.66/3.54  Total                : 2.80
% 9.66/3.54  Index Insertion      : 0.00
% 9.66/3.54  Index Deletion       : 0.00
% 9.66/3.54  Index Matching       : 0.00
% 9.66/3.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
