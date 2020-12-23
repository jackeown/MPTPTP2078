%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:23 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 284 expanded)
%              Number of leaves         :   18 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 488 expanded)
%              Number of equality atoms :   50 ( 194 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_24,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3712,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,B_107) = A_106
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3725,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3712])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3746,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3725,c_4])).

tff(c_3838,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_tarski(k2_zfmisc_1(A_112,B_113),k2_zfmisc_1(A_112,C_114))
      | r1_tarski(B_113,C_114)
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3854,plain,
    ( r1_tarski('#skF_2','#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3746,c_3838])).

tff(c_3859,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3854])).

tff(c_12,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3862,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3859,c_3859,c_12])).

tff(c_22,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3864,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3859,c_22])).

tff(c_3881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3864])).

tff(c_3883,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3854])).

tff(c_98,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_98])).

tff(c_260,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_4])).

tff(c_443,plain,(
    ! [B_44,A_45,C_46] :
      ( ~ r1_tarski(k2_zfmisc_1(B_44,A_45),k2_zfmisc_1(C_46,A_45))
      | r1_tarski(B_44,C_46)
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_459,plain,
    ( r1_tarski('#skF_1','#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_260,c_443])).

tff(c_464,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_10,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_470,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_464,c_10])).

tff(c_471,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_22])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_471])).

tff(c_490,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r1_tarski(k2_zfmisc_1(A_9,B_10),k2_zfmisc_1(A_9,C_11))
      | r1_tarski(B_10,C_11)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_276,plain,
    ( r1_tarski('#skF_2','#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_260,c_14])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_281,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_278,c_12])).

tff(c_283,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_22])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_283])).

tff(c_340,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_531,plain,(
    ! [A_48,C_49,B_50,D_51] : k3_xboole_0(k2_zfmisc_1(A_48,C_49),k2_zfmisc_1(B_50,D_51)) = k2_zfmisc_1(k3_xboole_0(A_48,B_50),k3_xboole_0(C_49,D_51)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_573,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_531])).

tff(c_601,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_573])).

tff(c_1939,plain,(
    ! [A_76,B_77,C_78,D_79] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_76,B_77),k3_xboole_0(C_78,D_79)),k2_zfmisc_1(A_76,C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_4])).

tff(c_1993,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_1939])).

tff(c_2064,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1993,c_14])).

tff(c_2070,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_2064])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2075,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2070,c_6])).

tff(c_2136,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_2])).

tff(c_2240,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_601])).

tff(c_339,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_345,plain,(
    k3_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_339,c_6])).

tff(c_3378,plain,(
    ! [A_98,B_99] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_98,B_99),'#skF_2'),k2_zfmisc_1(A_98,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1939])).

tff(c_3590,plain,(
    ! [B_102,A_103] : r1_tarski(k2_zfmisc_1(k3_xboole_0(B_102,A_103),'#skF_2'),k2_zfmisc_1(A_103,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3378])).

tff(c_3608,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2240,c_3590])).

tff(c_16,plain,(
    ! [B_10,A_9,C_11] :
      ( ~ r1_tarski(k2_zfmisc_1(B_10,A_9),k2_zfmisc_1(C_11,A_9))
      | r1_tarski(B_10,C_11)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3692,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3608,c_16])).

tff(c_3699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_490,c_87,c_3692])).

tff(c_3700,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_3701,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_3727,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3701,c_3712])).

tff(c_4316,plain,(
    ! [A_127,C_128,B_129,D_130] : k3_xboole_0(k2_zfmisc_1(A_127,C_128),k2_zfmisc_1(B_129,D_130)) = k2_zfmisc_1(k3_xboole_0(A_127,B_129),k3_xboole_0(C_128,D_130)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4346,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4316,c_3725])).

tff(c_4395,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3727,c_4346])).

tff(c_5508,plain,(
    ! [A_151,B_152,C_153,D_154] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_151,B_152),k3_xboole_0(C_153,D_154)),k2_zfmisc_1(A_151,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4316,c_4])).

tff(c_5640,plain,(
    ! [C_155,D_156] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0(C_155,D_156)),k2_zfmisc_1('#skF_1',C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3727,c_5508])).

tff(c_5670,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4395,c_5640])).

tff(c_5723,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5670,c_14])).

tff(c_5730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3883,c_3700,c_5723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/2.01  
% 4.77/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/2.01  %$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.77/2.01  
% 4.77/2.01  %Foreground sorts:
% 4.77/2.01  
% 4.77/2.01  
% 4.77/2.01  %Background operators:
% 4.77/2.01  
% 4.77/2.01  
% 4.77/2.01  %Foreground operators:
% 4.77/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/2.01  tff('#skF_2', type, '#skF_2': $i).
% 4.77/2.01  tff('#skF_3', type, '#skF_3': $i).
% 4.77/2.01  tff('#skF_1', type, '#skF_1': $i).
% 4.77/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/2.01  tff('#skF_4', type, '#skF_4': $i).
% 4.77/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.77/2.01  
% 4.77/2.03  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 4.77/2.03  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.77/2.03  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.77/2.03  tff(f_50, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 4.77/2.03  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.77/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.77/2.03  tff(f_52, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 4.77/2.03  tff(c_24, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.77/2.03  tff(c_3712, plain, (![A_106, B_107]: (k3_xboole_0(A_106, B_107)=A_106 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/2.03  tff(c_3725, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_3712])).
% 4.77/2.03  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.77/2.03  tff(c_3746, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3725, c_4])).
% 4.77/2.03  tff(c_3838, plain, (![A_112, B_113, C_114]: (~r1_tarski(k2_zfmisc_1(A_112, B_113), k2_zfmisc_1(A_112, C_114)) | r1_tarski(B_113, C_114) | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/2.03  tff(c_3854, plain, (r1_tarski('#skF_2', '#skF_2') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3746, c_3838])).
% 4.77/2.03  tff(c_3859, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3854])).
% 4.77/2.03  tff(c_12, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.77/2.03  tff(c_3862, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3859, c_3859, c_12])).
% 4.77/2.03  tff(c_22, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.77/2.03  tff(c_3864, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3859, c_22])).
% 4.77/2.03  tff(c_3881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3864])).
% 4.77/2.03  tff(c_3883, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_3854])).
% 4.77/2.03  tff(c_98, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/2.03  tff(c_108, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_98])).
% 4.77/2.03  tff(c_260, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_4])).
% 4.77/2.03  tff(c_443, plain, (![B_44, A_45, C_46]: (~r1_tarski(k2_zfmisc_1(B_44, A_45), k2_zfmisc_1(C_46, A_45)) | r1_tarski(B_44, C_46) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/2.03  tff(c_459, plain, (r1_tarski('#skF_1', '#skF_1') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_260, c_443])).
% 4.77/2.03  tff(c_464, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_459])).
% 4.77/2.03  tff(c_10, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.77/2.03  tff(c_470, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_464, c_10])).
% 4.77/2.03  tff(c_471, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_464, c_22])).
% 4.77/2.03  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_470, c_471])).
% 4.77/2.03  tff(c_490, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_459])).
% 4.77/2.03  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.77/2.03  tff(c_87, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 4.77/2.03  tff(c_14, plain, (![A_9, B_10, C_11]: (~r1_tarski(k2_zfmisc_1(A_9, B_10), k2_zfmisc_1(A_9, C_11)) | r1_tarski(B_10, C_11) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/2.03  tff(c_276, plain, (r1_tarski('#skF_2', '#skF_2') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_260, c_14])).
% 4.77/2.03  tff(c_278, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_276])).
% 4.77/2.03  tff(c_281, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_278, c_12])).
% 4.77/2.03  tff(c_283, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_22])).
% 4.77/2.03  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_283])).
% 4.77/2.03  tff(c_340, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_276])).
% 4.77/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.77/2.03  tff(c_531, plain, (![A_48, C_49, B_50, D_51]: (k3_xboole_0(k2_zfmisc_1(A_48, C_49), k2_zfmisc_1(B_50, D_51))=k2_zfmisc_1(k3_xboole_0(A_48, B_50), k3_xboole_0(C_49, D_51)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.77/2.03  tff(c_573, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108, c_531])).
% 4.77/2.03  tff(c_601, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_573])).
% 4.77/2.03  tff(c_1939, plain, (![A_76, B_77, C_78, D_79]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_76, B_77), k3_xboole_0(C_78, D_79)), k2_zfmisc_1(A_76, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_531, c_4])).
% 4.77/2.03  tff(c_1993, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_601, c_1939])).
% 4.77/2.03  tff(c_2064, plain, (r1_tarski('#skF_2', '#skF_4') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1993, c_14])).
% 4.77/2.03  tff(c_2070, plain, (r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_340, c_2064])).
% 4.77/2.03  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/2.03  tff(c_2075, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_2070, c_6])).
% 4.77/2.03  tff(c_2136, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2075, c_2])).
% 4.77/2.03  tff(c_2240, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_601])).
% 4.77/2.03  tff(c_339, plain, (r1_tarski('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_276])).
% 4.77/2.03  tff(c_345, plain, (k3_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_339, c_6])).
% 4.77/2.03  tff(c_3378, plain, (![A_98, B_99]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_98, B_99), '#skF_2'), k2_zfmisc_1(A_98, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1939])).
% 4.77/2.03  tff(c_3590, plain, (![B_102, A_103]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(B_102, A_103), '#skF_2'), k2_zfmisc_1(A_103, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3378])).
% 4.77/2.03  tff(c_3608, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2240, c_3590])).
% 4.77/2.03  tff(c_16, plain, (![B_10, A_9, C_11]: (~r1_tarski(k2_zfmisc_1(B_10, A_9), k2_zfmisc_1(C_11, A_9)) | r1_tarski(B_10, C_11) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/2.03  tff(c_3692, plain, (r1_tarski('#skF_1', '#skF_3') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3608, c_16])).
% 4.77/2.03  tff(c_3699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_490, c_87, c_3692])).
% 4.77/2.03  tff(c_3700, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 4.77/2.03  tff(c_3701, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 4.77/2.03  tff(c_3727, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_3701, c_3712])).
% 4.77/2.03  tff(c_4316, plain, (![A_127, C_128, B_129, D_130]: (k3_xboole_0(k2_zfmisc_1(A_127, C_128), k2_zfmisc_1(B_129, D_130))=k2_zfmisc_1(k3_xboole_0(A_127, B_129), k3_xboole_0(C_128, D_130)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.77/2.03  tff(c_4346, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4316, c_3725])).
% 4.77/2.03  tff(c_4395, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3727, c_4346])).
% 4.77/2.03  tff(c_5508, plain, (![A_151, B_152, C_153, D_154]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_151, B_152), k3_xboole_0(C_153, D_154)), k2_zfmisc_1(A_151, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_4316, c_4])).
% 4.77/2.03  tff(c_5640, plain, (![C_155, D_156]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0(C_155, D_156)), k2_zfmisc_1('#skF_1', C_155)))), inference(superposition, [status(thm), theory('equality')], [c_3727, c_5508])).
% 4.77/2.03  tff(c_5670, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4395, c_5640])).
% 4.77/2.03  tff(c_5723, plain, (r1_tarski('#skF_2', '#skF_4') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_5670, c_14])).
% 4.77/2.03  tff(c_5730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3883, c_3700, c_5723])).
% 4.77/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/2.03  
% 4.77/2.03  Inference rules
% 4.77/2.03  ----------------------
% 4.77/2.03  #Ref     : 0
% 4.77/2.03  #Sup     : 1459
% 4.77/2.03  #Fact    : 0
% 4.77/2.03  #Define  : 0
% 4.77/2.03  #Split   : 8
% 4.77/2.03  #Chain   : 0
% 4.77/2.03  #Close   : 0
% 4.77/2.03  
% 4.77/2.03  Ordering : KBO
% 4.77/2.03  
% 4.77/2.03  Simplification rules
% 4.77/2.03  ----------------------
% 4.77/2.03  #Subsume      : 63
% 4.77/2.03  #Demod        : 1633
% 4.77/2.03  #Tautology    : 897
% 4.77/2.03  #SimpNegUnit  : 37
% 4.77/2.03  #BackRed      : 30
% 4.77/2.03  
% 4.77/2.03  #Partial instantiations: 0
% 4.77/2.03  #Strategies tried      : 1
% 4.77/2.03  
% 4.77/2.03  Timing (in seconds)
% 4.77/2.03  ----------------------
% 4.77/2.03  Preprocessing        : 0.27
% 4.77/2.03  Parsing              : 0.14
% 4.77/2.03  CNF conversion       : 0.02
% 4.77/2.03  Main loop            : 0.91
% 4.77/2.03  Inferencing          : 0.24
% 4.77/2.03  Reduction            : 0.46
% 4.77/2.03  Demodulation         : 0.39
% 4.77/2.03  BG Simplification    : 0.03
% 4.77/2.03  Subsumption          : 0.12
% 4.77/2.03  Abstraction          : 0.05
% 4.77/2.03  MUC search           : 0.00
% 4.77/2.03  Cooper               : 0.00
% 4.77/2.03  Total                : 1.22
% 4.77/2.03  Index Insertion      : 0.00
% 4.77/2.03  Index Deletion       : 0.00
% 4.77/2.03  Index Matching       : 0.00
% 4.77/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
