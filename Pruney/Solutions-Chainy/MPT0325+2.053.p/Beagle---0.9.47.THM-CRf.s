%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 10.29s
% Output     : CNFRefutation 10.29s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 282 expanded)
%              Number of leaves         :   24 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 405 expanded)
%              Number of equality atoms :   62 ( 271 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_2908,plain,(
    ! [A_124,B_125] :
      ( r1_tarski(A_124,B_125)
      | k4_xboole_0(A_124,B_125) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_101,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_78])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_213,plain,(
    ! [A_48,B_49,C_50] : k3_xboole_0(k3_xboole_0(A_48,B_49),C_50) = k3_xboole_0(A_48,k3_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [A_51,C_52] : k3_xboole_0(A_51,k3_xboole_0(A_51,C_52)) = k3_xboole_0(A_51,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_213])).

tff(c_287,plain,(
    ! [A_51,C_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,C_52)) = k4_xboole_0(A_51,k3_xboole_0(A_51,C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_8])).

tff(c_316,plain,(
    ! [A_51,C_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,C_52)) = k4_xboole_0(A_51,C_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_287])).

tff(c_34,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_1142,plain,(
    ! [A_83,C_84,B_85,D_86] : k3_xboole_0(k2_zfmisc_1(A_83,C_84),k2_zfmisc_1(B_85,D_86)) = k2_zfmisc_1(k3_xboole_0(A_83,B_85),k3_xboole_0(C_84,D_86)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1203,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1142])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1636,plain,(
    ! [A_92,B_93,C_94,D_95] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_92,B_93),k3_xboole_0(C_94,D_95)),k2_zfmisc_1(A_92,C_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_12])).

tff(c_2362,plain,(
    ! [A_109,C_110,D_111] : r1_tarski(k2_zfmisc_1(A_109,k3_xboole_0(C_110,D_111)),k2_zfmisc_1(A_109,C_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1636])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2534,plain,(
    ! [A_115,C_116,D_117] : k4_xboole_0(k2_zfmisc_1(A_115,k3_xboole_0(C_116,D_117)),k2_zfmisc_1(A_115,C_116)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2362,c_6])).

tff(c_2556,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_2534])).

tff(c_26,plain,(
    ! [A_21,C_23,B_22] : k4_xboole_0(k2_zfmisc_1(A_21,C_23),k2_zfmisc_1(B_22,C_23)) = k2_zfmisc_1(k4_xboole_0(A_21,B_22),C_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2628,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_3')),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2556,c_26])).

tff(c_2637,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_2628])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | k2_zfmisc_1(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2677,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2637,c_18])).

tff(c_2688,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_2677])).

tff(c_20,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2712,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2688,c_20])).

tff(c_32,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2713,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_32])).

tff(c_2905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2712,c_2713])).

tff(c_2906,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2912,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2908,c_2906])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2907,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2934,plain,(
    ! [A_128,B_129] :
      ( k3_xboole_0(A_128,B_129) = A_128
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2951,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2907,c_2934])).

tff(c_2952,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2934])).

tff(c_4224,plain,(
    ! [A_176,C_177,B_178,D_179] : k3_xboole_0(k2_zfmisc_1(A_176,C_177),k2_zfmisc_1(B_178,D_179)) = k2_zfmisc_1(k3_xboole_0(A_176,B_178),k3_xboole_0(C_177,D_179)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4283,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2952,c_4224])).

tff(c_4310,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2951,c_4283])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] : k4_xboole_0(k2_zfmisc_1(C_23,A_21),k2_zfmisc_1(C_23,B_22)) = k2_zfmisc_1(C_23,k4_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7456,plain,(
    ! [A_239,C_240,B_241,D_242] : k5_xboole_0(k2_zfmisc_1(A_239,C_240),k2_zfmisc_1(k3_xboole_0(A_239,B_241),k3_xboole_0(C_240,D_242))) = k4_xboole_0(k2_zfmisc_1(A_239,C_240),k2_zfmisc_1(B_241,D_242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4224,c_8])).

tff(c_7579,plain,(
    ! [A_1,C_240,D_242] : k5_xboole_0(k2_zfmisc_1(A_1,C_240),k2_zfmisc_1(A_1,k3_xboole_0(C_240,D_242))) = k4_xboole_0(k2_zfmisc_1(A_1,C_240),k2_zfmisc_1(A_1,D_242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7456])).

tff(c_26884,plain,(
    ! [A_412,C_413,D_414] : k5_xboole_0(k2_zfmisc_1(A_412,C_413),k2_zfmisc_1(A_412,k3_xboole_0(C_413,D_414))) = k2_zfmisc_1(A_412,k4_xboole_0(C_413,D_414)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7579])).

tff(c_26959,plain,(
    k5_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4310,c_26884])).

tff(c_27034,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26959])).

tff(c_27101,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_27034,c_18])).

tff(c_27115,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2912,c_27101])).

tff(c_22,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27197,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_1',B_16) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27115,c_27115,c_22])).

tff(c_27200,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27115,c_32])).

tff(c_27291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27197,c_27200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.29/4.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.29/4.11  
% 10.29/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.29/4.12  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.29/4.12  
% 10.29/4.12  %Foreground sorts:
% 10.29/4.12  
% 10.29/4.12  
% 10.29/4.12  %Background operators:
% 10.29/4.12  
% 10.29/4.12  
% 10.29/4.12  %Foreground operators:
% 10.29/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.29/4.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.29/4.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.29/4.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.29/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.29/4.12  tff('#skF_2', type, '#skF_2': $i).
% 10.29/4.12  tff('#skF_3', type, '#skF_3': $i).
% 10.29/4.12  tff('#skF_1', type, '#skF_1': $i).
% 10.29/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.29/4.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.29/4.12  tff('#skF_4', type, '#skF_4': $i).
% 10.29/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.29/4.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.29/4.12  
% 10.29/4.13  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.29/4.13  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 10.29/4.13  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.29/4.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.29/4.13  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 10.29/4.13  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.29/4.13  tff(f_51, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 10.29/4.13  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.29/4.13  tff(f_55, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 10.29/4.13  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.29/4.13  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.29/4.13  tff(c_2908, plain, (![A_124, B_125]: (r1_tarski(A_124, B_125) | k4_xboole_0(A_124, B_125)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.29/4.13  tff(c_93, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.29/4.13  tff(c_30, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.29/4.13  tff(c_78, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 10.29/4.13  tff(c_101, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_78])).
% 10.29/4.13  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.29/4.13  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.29/4.13  tff(c_213, plain, (![A_48, B_49, C_50]: (k3_xboole_0(k3_xboole_0(A_48, B_49), C_50)=k3_xboole_0(A_48, k3_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.29/4.13  tff(c_265, plain, (![A_51, C_52]: (k3_xboole_0(A_51, k3_xboole_0(A_51, C_52))=k3_xboole_0(A_51, C_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_213])).
% 10.29/4.13  tff(c_287, plain, (![A_51, C_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, C_52))=k4_xboole_0(A_51, k3_xboole_0(A_51, C_52)))), inference(superposition, [status(thm), theory('equality')], [c_265, c_8])).
% 10.29/4.13  tff(c_316, plain, (![A_51, C_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, C_52))=k4_xboole_0(A_51, C_52))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_287])).
% 10.29/4.13  tff(c_34, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.29/4.13  tff(c_79, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.29/4.13  tff(c_89, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_79])).
% 10.29/4.13  tff(c_1142, plain, (![A_83, C_84, B_85, D_86]: (k3_xboole_0(k2_zfmisc_1(A_83, C_84), k2_zfmisc_1(B_85, D_86))=k2_zfmisc_1(k3_xboole_0(A_83, B_85), k3_xboole_0(C_84, D_86)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.29/4.13  tff(c_1203, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_1142])).
% 10.29/4.13  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.29/4.13  tff(c_1636, plain, (![A_92, B_93, C_94, D_95]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_92, B_93), k3_xboole_0(C_94, D_95)), k2_zfmisc_1(A_92, C_94)))), inference(superposition, [status(thm), theory('equality')], [c_1142, c_12])).
% 10.29/4.13  tff(c_2362, plain, (![A_109, C_110, D_111]: (r1_tarski(k2_zfmisc_1(A_109, k3_xboole_0(C_110, D_111)), k2_zfmisc_1(A_109, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1636])).
% 10.29/4.13  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.29/4.13  tff(c_2534, plain, (![A_115, C_116, D_117]: (k4_xboole_0(k2_zfmisc_1(A_115, k3_xboole_0(C_116, D_117)), k2_zfmisc_1(A_115, C_116))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2362, c_6])).
% 10.29/4.13  tff(c_2556, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1203, c_2534])).
% 10.29/4.13  tff(c_26, plain, (![A_21, C_23, B_22]: (k4_xboole_0(k2_zfmisc_1(A_21, C_23), k2_zfmisc_1(B_22, C_23))=k2_zfmisc_1(k4_xboole_0(A_21, B_22), C_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.29/4.13  tff(c_2628, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_3')), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2556, c_26])).
% 10.29/4.13  tff(c_2637, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_316, c_2628])).
% 10.29/4.13  tff(c_18, plain, (![B_16, A_15]: (k1_xboole_0=B_16 | k1_xboole_0=A_15 | k2_zfmisc_1(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.29/4.13  tff(c_2677, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2637, c_18])).
% 10.29/4.13  tff(c_2688, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_2677])).
% 10.29/4.13  tff(c_20, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.29/4.13  tff(c_2712, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2688, c_20])).
% 10.29/4.13  tff(c_32, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.29/4.13  tff(c_2713, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_32])).
% 10.29/4.13  tff(c_2905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2712, c_2713])).
% 10.29/4.13  tff(c_2906, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 10.29/4.13  tff(c_2912, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2908, c_2906])).
% 10.29/4.13  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.29/4.13  tff(c_2907, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 10.29/4.13  tff(c_2934, plain, (![A_128, B_129]: (k3_xboole_0(A_128, B_129)=A_128 | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.29/4.13  tff(c_2951, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_2907, c_2934])).
% 10.29/4.13  tff(c_2952, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_2934])).
% 10.29/4.13  tff(c_4224, plain, (![A_176, C_177, B_178, D_179]: (k3_xboole_0(k2_zfmisc_1(A_176, C_177), k2_zfmisc_1(B_178, D_179))=k2_zfmisc_1(k3_xboole_0(A_176, B_178), k3_xboole_0(C_177, D_179)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.29/4.13  tff(c_4283, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2952, c_4224])).
% 10.29/4.13  tff(c_4310, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2951, c_4283])).
% 10.29/4.13  tff(c_28, plain, (![C_23, A_21, B_22]: (k4_xboole_0(k2_zfmisc_1(C_23, A_21), k2_zfmisc_1(C_23, B_22))=k2_zfmisc_1(C_23, k4_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.29/4.13  tff(c_7456, plain, (![A_239, C_240, B_241, D_242]: (k5_xboole_0(k2_zfmisc_1(A_239, C_240), k2_zfmisc_1(k3_xboole_0(A_239, B_241), k3_xboole_0(C_240, D_242)))=k4_xboole_0(k2_zfmisc_1(A_239, C_240), k2_zfmisc_1(B_241, D_242)))), inference(superposition, [status(thm), theory('equality')], [c_4224, c_8])).
% 10.29/4.13  tff(c_7579, plain, (![A_1, C_240, D_242]: (k5_xboole_0(k2_zfmisc_1(A_1, C_240), k2_zfmisc_1(A_1, k3_xboole_0(C_240, D_242)))=k4_xboole_0(k2_zfmisc_1(A_1, C_240), k2_zfmisc_1(A_1, D_242)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7456])).
% 10.29/4.13  tff(c_26884, plain, (![A_412, C_413, D_414]: (k5_xboole_0(k2_zfmisc_1(A_412, C_413), k2_zfmisc_1(A_412, k3_xboole_0(C_413, D_414)))=k2_zfmisc_1(A_412, k4_xboole_0(C_413, D_414)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7579])).
% 10.29/4.13  tff(c_26959, plain, (k5_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4310, c_26884])).
% 10.29/4.13  tff(c_27034, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26959])).
% 10.29/4.13  tff(c_27101, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_27034, c_18])).
% 10.29/4.13  tff(c_27115, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2912, c_27101])).
% 10.29/4.13  tff(c_22, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.29/4.13  tff(c_27197, plain, (![B_16]: (k2_zfmisc_1('#skF_1', B_16)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27115, c_27115, c_22])).
% 10.29/4.13  tff(c_27200, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27115, c_32])).
% 10.29/4.13  tff(c_27291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27197, c_27200])).
% 10.29/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.29/4.13  
% 10.29/4.13  Inference rules
% 10.29/4.13  ----------------------
% 10.29/4.13  #Ref     : 0
% 10.29/4.13  #Sup     : 6593
% 10.29/4.13  #Fact    : 0
% 10.29/4.13  #Define  : 0
% 10.29/4.13  #Split   : 5
% 10.29/4.13  #Chain   : 0
% 10.29/4.13  #Close   : 0
% 10.29/4.13  
% 10.29/4.13  Ordering : KBO
% 10.29/4.13  
% 10.29/4.13  Simplification rules
% 10.29/4.13  ----------------------
% 10.29/4.13  #Subsume      : 12
% 10.29/4.13  #Demod        : 9534
% 10.29/4.13  #Tautology    : 4742
% 10.29/4.13  #SimpNegUnit  : 2
% 10.29/4.13  #BackRed      : 142
% 10.29/4.13  
% 10.29/4.13  #Partial instantiations: 0
% 10.29/4.13  #Strategies tried      : 1
% 10.29/4.13  
% 10.29/4.13  Timing (in seconds)
% 10.29/4.13  ----------------------
% 10.29/4.14  Preprocessing        : 0.30
% 10.29/4.14  Parsing              : 0.17
% 10.29/4.14  CNF conversion       : 0.02
% 10.29/4.14  Main loop            : 3.04
% 10.29/4.14  Inferencing          : 0.64
% 10.29/4.14  Reduction            : 1.75
% 10.29/4.14  Demodulation         : 1.55
% 10.29/4.14  BG Simplification    : 0.08
% 10.29/4.14  Subsumption          : 0.41
% 10.29/4.14  Abstraction          : 0.14
% 10.29/4.14  MUC search           : 0.00
% 10.29/4.14  Cooper               : 0.00
% 10.29/4.14  Total                : 3.37
% 10.29/4.14  Index Insertion      : 0.00
% 10.29/4.14  Index Deletion       : 0.00
% 10.29/4.14  Index Matching       : 0.00
% 10.29/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
