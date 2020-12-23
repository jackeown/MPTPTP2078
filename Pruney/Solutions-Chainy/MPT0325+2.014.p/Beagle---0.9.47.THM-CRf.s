%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:22 EST 2020

% Result     : Theorem 10.56s
% Output     : CNFRefutation 10.84s
% Verified   : 
% Statistics : Number of formulae       :  238 (1354 expanded)
%              Number of leaves         :   24 ( 452 expanded)
%              Depth                    :   16
%              Number of atoms          :  326 (2679 expanded)
%              Number of equality atoms :  165 (1316 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k3_xboole_0(A,B),C) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_32,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_149,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [A_43] : k3_xboole_0(A_43,A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_149,c_28])).

tff(c_34,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_755,plain,(
    ! [C_93,A_94,B_95] : k3_xboole_0(k2_zfmisc_1(C_93,A_94),k2_zfmisc_1(C_93,B_95)) = k2_zfmisc_1(C_93,k3_xboole_0(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_813,plain,(
    ! [A_16,B_95] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_16,B_95)) = k2_zfmisc_1(A_16,k3_xboole_0(k1_xboole_0,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_755])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1328,plain,(
    ! [A_108,C_109,B_110,D_111] : k3_xboole_0(k2_zfmisc_1(A_108,C_109),k2_zfmisc_1(B_110,D_111)) = k2_zfmisc_1(k3_xboole_0(A_108,B_110),k3_xboole_0(C_109,D_111)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1413,plain,(
    ! [A_108,A_16,C_109] : k2_zfmisc_1(k3_xboole_0(A_108,A_16),k3_xboole_0(C_109,k1_xboole_0)) = k3_xboole_0(k2_zfmisc_1(A_108,C_109),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1328])).

tff(c_2686,plain,(
    ! [A_147,A_148,C_149] : k2_zfmisc_1(k3_xboole_0(A_147,A_148),k3_xboole_0(C_149,k1_xboole_0)) = k2_zfmisc_1(A_147,k3_xboole_0(k1_xboole_0,C_149)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_2,c_1413])).

tff(c_245,plain,(
    ! [A_58,C_59,B_60] : k3_xboole_0(k2_zfmisc_1(A_58,C_59),k2_zfmisc_1(B_60,C_59)) = k2_zfmisc_1(k3_xboole_0(A_58,B_60),C_59) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_289,plain,(
    ! [B_60,B_17] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_60,B_17)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_60),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_245])).

tff(c_832,plain,(
    ! [B_60,B_17] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_60),B_17) = k2_zfmisc_1(B_60,k3_xboole_0(k1_xboole_0,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_289])).

tff(c_2738,plain,(
    ! [A_148,C_149] : k2_zfmisc_1(A_148,k3_xboole_0(k1_xboole_0,k3_xboole_0(C_149,k1_xboole_0))) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2686,c_832])).

tff(c_2904,plain,(
    ! [A_153,C_154] : k2_zfmisc_1(A_153,k3_xboole_0(k1_xboole_0,k3_xboole_0(C_154,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2738])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k1_xboole_0 = B_17
      | k1_xboole_0 = A_16
      | k2_zfmisc_1(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3072,plain,(
    ! [C_154,A_153] :
      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(C_154,k1_xboole_0)) = k1_xboole_0
      | k1_xboole_0 = A_153 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2904,c_30])).

tff(c_3164,plain,(
    ! [A_156] : k1_xboole_0 = A_156 ),
    inference(splitLeft,[status(thm)],[c_3072])).

tff(c_50,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_28])).

tff(c_1352,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_111])).

tff(c_512,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_tarski(k2_zfmisc_1(A_82,B_83),k2_zfmisc_1(A_82,C_84))
      | r1_tarski(B_83,C_84)
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_522,plain,(
    ! [A_16,B_83] :
      ( ~ r1_tarski(k2_zfmisc_1(A_16,B_83),k1_xboole_0)
      | r1_tarski(B_83,k1_xboole_0)
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_512])).

tff(c_1556,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0)
    | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1352,c_522])).

tff(c_1672,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1556])).

tff(c_3278,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3164,c_1672])).

tff(c_3528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_3278])).

tff(c_3532,plain,(
    ! [C_782] : k3_xboole_0(k1_xboole_0,k3_xboole_0(C_782,k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3072])).

tff(c_816,plain,(
    ! [A_16,A_94] : k3_xboole_0(k2_zfmisc_1(A_16,A_94),k1_xboole_0) = k2_zfmisc_1(A_16,k3_xboole_0(A_94,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_755])).

tff(c_292,plain,(
    ! [A_58,B_17] : k3_xboole_0(k2_zfmisc_1(A_58,B_17),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(A_58,k1_xboole_0),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_245])).

tff(c_1013,plain,(
    ! [A_102,B_103] : k2_zfmisc_1(k3_xboole_0(A_102,k1_xboole_0),B_103) = k2_zfmisc_1(A_102,k3_xboole_0(B_103,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_292])).

tff(c_1087,plain,(
    ! [A_1,B_103] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,A_1),B_103) = k2_zfmisc_1(A_1,k3_xboole_0(B_103,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1013])).

tff(c_3545,plain,(
    ! [C_782,B_103] : k2_zfmisc_1(k3_xboole_0(C_782,k1_xboole_0),k3_xboole_0(B_103,k1_xboole_0)) = k2_zfmisc_1(k1_xboole_0,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_3532,c_1087])).

tff(c_3763,plain,(
    ! [C_791,B_792] : k2_zfmisc_1(k3_xboole_0(C_791,k1_xboole_0),k3_xboole_0(B_792,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3545])).

tff(c_1437,plain,(
    ! [A_108,A_16,C_109] : k2_zfmisc_1(k3_xboole_0(A_108,A_16),k3_xboole_0(C_109,k1_xboole_0)) = k2_zfmisc_1(A_108,k3_xboole_0(k1_xboole_0,C_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_2,c_1413])).

tff(c_3768,plain,(
    ! [C_791,B_792] : k2_zfmisc_1(C_791,k3_xboole_0(k1_xboole_0,B_792)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3763,c_1437])).

tff(c_920,plain,(
    ! [B_100,B_101] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_100),B_101) = k2_zfmisc_1(B_100,k3_xboole_0(k1_xboole_0,B_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_289])).

tff(c_990,plain,(
    ! [B_2,B_101] : k2_zfmisc_1(k3_xboole_0(B_2,k1_xboole_0),B_101) = k2_zfmisc_1(B_2,k3_xboole_0(k1_xboole_0,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_920])).

tff(c_4320,plain,(
    ! [B_800,B_801] : k2_zfmisc_1(k3_xboole_0(B_800,k1_xboole_0),B_801) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_990])).

tff(c_4443,plain,(
    ! [B_801,B_800] :
      ( k1_xboole_0 = B_801
      | k3_xboole_0(B_800,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4320,c_30])).

tff(c_4919,plain,(
    ! [B_811] : k3_xboole_0(B_811,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4443])).

tff(c_4955,plain,(
    ! [B_811] : k3_xboole_0(k1_xboole_0,B_811) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4919,c_2])).

tff(c_137,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5617,plain,(
    ! [A_826,B_827,B_828] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_826,B_827),B_828),B_827)
      | r1_tarski(k3_xboole_0(A_826,B_827),B_828) ) ),
    inference(resolution,[status(thm)],[c_137,c_12])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5714,plain,(
    ! [A_829,B_830] : r1_tarski(k3_xboole_0(A_829,B_830),B_830) ),
    inference(resolution,[status(thm)],[c_5617,c_6])).

tff(c_5736,plain,(
    ! [B_811] : r1_tarski(k1_xboole_0,B_811) ),
    inference(superposition,[status(thm),theory(equality)],[c_4955,c_5714])).

tff(c_184,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_187,plain,(
    ! [A_3,B_4,B_49] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_49)
      | ~ r1_tarski(A_3,B_49)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_184])).

tff(c_188,plain,(
    ! [D_51] :
      ( r2_hidden(D_51,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_51,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_561,plain,(
    ! [A_89] :
      ( r1_tarski(A_89,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden('#skF_1'(A_89,k2_zfmisc_1('#skF_6','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_188,c_6])).

tff(c_726,plain,(
    ! [A_92] :
      ( ~ r1_tarski(A_92,k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(A_92,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_187,c_561])).

tff(c_363,plain,(
    ! [B_65,A_66,C_67] :
      ( ~ r1_tarski(k2_zfmisc_1(B_65,A_66),k2_zfmisc_1(C_67,A_66))
      | r1_tarski(B_65,C_67)
      | k1_xboole_0 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_376,plain,(
    ! [C_67,B_17] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(C_67,B_17))
      | r1_tarski(k1_xboole_0,C_67)
      | k1_xboole_0 = B_17 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_363])).

tff(c_752,plain,
    ( r1_tarski(k1_xboole_0,'#skF_6')
    | k1_xboole_0 = '#skF_7'
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_726,c_376])).

tff(c_1011,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_5778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5736,c_1011])).

tff(c_5780,plain,(
    ! [B_831] : k1_xboole_0 = B_831 ),
    inference(splitRight,[status(thm)],[c_4443])).

tff(c_48,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [B_19,A_18,C_20] :
      ( ~ r1_tarski(k2_zfmisc_1(B_19,A_18),k2_zfmisc_1(C_20,A_18))
      | r1_tarski(B_19,C_20)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1574,plain,(
    ! [C_20] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(C_20,k3_xboole_0('#skF_5','#skF_7')))
      | r1_tarski(k3_xboole_0('#skF_4','#skF_6'),C_20)
      | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1352,c_38])).

tff(c_4309,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1574])).

tff(c_4312,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k1_xboole_0) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4309,c_1352])).

tff(c_4315,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4312])).

tff(c_4317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4315])).

tff(c_4319,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1574])).

tff(c_5935,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5780,c_4319])).

tff(c_5937,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1556])).

tff(c_379,plain,(
    ! [B_65,B_17] :
      ( ~ r1_tarski(k2_zfmisc_1(B_65,B_17),k1_xboole_0)
      | r1_tarski(B_65,k1_xboole_0)
      | k1_xboole_0 = B_17 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_363])).

tff(c_5965,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5937,c_379])).

tff(c_6146,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5965])).

tff(c_6168,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6146,c_6146,c_32])).

tff(c_6170,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6146,c_48])).

tff(c_6248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6168,c_6170])).

tff(c_6249,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5965])).

tff(c_6254,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6249,c_28])).

tff(c_1416,plain,(
    ! [B_110,B_17,D_111] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_110),k3_xboole_0(B_17,D_111)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_110,D_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1328])).

tff(c_9523,plain,(
    ! [B_1441,B_1442,D_1443] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_1441),k3_xboole_0(B_1442,D_1443)) = k2_zfmisc_1(B_1441,k3_xboole_0(k1_xboole_0,D_1443)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_1416])).

tff(c_9682,plain,(
    ! [B_1441] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_1441),'#skF_4') = k2_zfmisc_1(B_1441,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6254,c_9523])).

tff(c_9788,plain,(
    ! [B_1441] : k2_zfmisc_1(B_1441,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_153,c_6254,c_1087,c_9682])).

tff(c_5964,plain,
    ( r1_tarski('#skF_5',k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5937,c_522])).

tff(c_5968,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5964])).

tff(c_6040,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_4',B_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_5968,c_34])).

tff(c_6041,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_48])).

tff(c_6118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6040,c_6041])).

tff(c_6120,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5964])).

tff(c_867,plain,(
    ! [A_58,B_17] : k2_zfmisc_1(k3_xboole_0(A_58,k1_xboole_0),B_17) = k2_zfmisc_1(A_58,k3_xboole_0(B_17,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_292])).

tff(c_6731,plain,(
    ! [B_1382] : k2_zfmisc_1('#skF_4',k3_xboole_0(B_1382,k1_xboole_0)) = k2_zfmisc_1('#skF_4',B_1382) ),
    inference(superposition,[status(thm),theory(equality)],[c_6254,c_867])).

tff(c_6798,plain,(
    ! [B_1382] :
      ( k3_xboole_0(B_1382,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 = '#skF_4'
      | k2_zfmisc_1('#skF_4',B_1382) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6731,c_30])).

tff(c_7882,plain,(
    ! [B_1413] :
      ( k3_xboole_0(B_1413,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_4',B_1413) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_6120,c_6798])).

tff(c_7915,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_zfmisc_1('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7882,c_6254])).

tff(c_8011,plain,(
    k2_zfmisc_1('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6120,c_7915])).

tff(c_9807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9788,c_8011])).

tff(c_9809,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_519,plain,(
    ! [A_16,C_84] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_16,C_84))
      | r1_tarski(k1_xboole_0,C_84)
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_512])).

tff(c_749,plain,
    ( r1_tarski(k1_xboole_0,'#skF_7')
    | k1_xboole_0 = '#skF_6'
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_726,c_519])).

tff(c_9815,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_749])).

tff(c_9965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9809,c_9815])).

tff(c_9967,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_749])).

tff(c_10037,plain,
    ( r1_tarski(k1_xboole_0,'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9967,c_376])).

tff(c_10399,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_10037])).

tff(c_10422,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10399,c_10399,c_32])).

tff(c_10424,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10399,c_48])).

tff(c_10478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10422,c_10424])).

tff(c_10480,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10037])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_280,plain,(
    ! [B_60,C_59,A_58] : k3_xboole_0(k2_zfmisc_1(B_60,C_59),k2_zfmisc_1(A_58,C_59)) = k2_zfmisc_1(k3_xboole_0(A_58,B_60),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_12971,plain,(
    ! [A_1546,B_1547,B_1548] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_1546,B_1547),B_1548),B_1547)
      | r1_tarski(k3_xboole_0(A_1546,B_1547),B_1548) ) ),
    inference(resolution,[status(thm)],[c_137,c_12])).

tff(c_13064,plain,(
    ! [A_1549,B_1550] : r1_tarski(k3_xboole_0(A_1549,B_1550),B_1550) ),
    inference(resolution,[status(thm)],[c_12971,c_6])).

tff(c_15321,plain,(
    ! [A_1588,B_1589,C_1590] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_1588,B_1589),C_1590),k2_zfmisc_1(A_1588,C_1590)) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_13064])).

tff(c_10039,plain,(
    ! [A_1449,C_1450,B_1451,D_1452] : k3_xboole_0(k2_zfmisc_1(A_1449,C_1450),k2_zfmisc_1(B_1451,D_1452)) = k2_zfmisc_1(k3_xboole_0(A_1449,B_1451),k3_xboole_0(C_1450,D_1452)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10094,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10039])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_tarski(k2_zfmisc_1(A_18,B_19),k2_zfmisc_1(A_18,C_20))
      | r1_tarski(B_19,C_20)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10188,plain,(
    ! [C_20] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),C_20))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_20)
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10094,c_36])).

tff(c_11318,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10188])).

tff(c_11321,plain,(
    k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11318,c_10094])).

tff(c_11324,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_11321])).

tff(c_11326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_11324])).

tff(c_11328,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10188])).

tff(c_10191,plain,(
    ! [B_19] :
      ( ~ r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),B_19),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_19,k3_xboole_0('#skF_5','#skF_7'))
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10094,c_36])).

tff(c_11380,plain,(
    ! [B_19] :
      ( ~ r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),B_19),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_19,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11328,c_10191])).

tff(c_15444,plain,(
    r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_15321,c_11380])).

tff(c_15469,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15444,c_28])).

tff(c_13125,plain,(
    ! [B_1551,A_1552] : r1_tarski(k3_xboole_0(B_1551,A_1552),B_1551) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13064])).

tff(c_13447,plain,(
    ! [B_1559,A_1560] : k3_xboole_0(k3_xboole_0(B_1559,A_1560),B_1559) = k3_xboole_0(B_1559,A_1560) ),
    inference(resolution,[status(thm)],[c_13125,c_28])).

tff(c_13576,plain,(
    ! [A_1,A_1560] : k3_xboole_0(A_1,k3_xboole_0(A_1,A_1560)) = k3_xboole_0(A_1,A_1560) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13447])).

tff(c_15530,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_15469,c_13576])).

tff(c_15615,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),'#skF_5') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15530,c_10094])).

tff(c_40,plain,(
    ! [A_21,C_23,B_22] : k3_xboole_0(k2_zfmisc_1(A_21,C_23),k2_zfmisc_1(B_22,C_23)) = k2_zfmisc_1(k3_xboole_0(A_21,B_22),C_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_13104,plain,(
    ! [A_21,B_22,C_23] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_21,B_22),C_23),k2_zfmisc_1(B_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_13064])).

tff(c_16071,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15615,c_13104])).

tff(c_16151,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16071,c_38])).

tff(c_16158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10480,c_73,c_16151])).

tff(c_16159,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16224,plain,(
    ! [A_1608,B_1609] :
      ( ~ r2_hidden('#skF_1'(A_1608,B_1609),B_1609)
      | r1_tarski(A_1608,B_1609) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16233,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_16224])).

tff(c_16242,plain,(
    ! [A_1610] : r1_tarski(A_1610,A_1610) ),
    inference(resolution,[status(thm)],[c_8,c_16224])).

tff(c_16246,plain,(
    ! [A_1610] : k3_xboole_0(A_1610,A_1610) = A_1610 ),
    inference(resolution,[status(thm)],[c_16242,c_28])).

tff(c_16420,plain,(
    ! [C_1634,A_1635,B_1636] : k3_xboole_0(k2_zfmisc_1(C_1634,A_1635),k2_zfmisc_1(C_1634,B_1636)) = k2_zfmisc_1(C_1634,k3_xboole_0(A_1635,B_1636)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16458,plain,(
    ! [A_16,B_1636] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_16,B_1636)) = k2_zfmisc_1(A_16,k3_xboole_0(k1_xboole_0,B_1636)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_16420])).

tff(c_16631,plain,(
    ! [A_1649,C_1650,B_1651] : k3_xboole_0(k2_zfmisc_1(A_1649,C_1650),k2_zfmisc_1(B_1651,C_1650)) = k2_zfmisc_1(k3_xboole_0(A_1649,B_1651),C_1650) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16683,plain,(
    ! [B_1651,B_17] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_1651,B_17)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_1651),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_16631])).

tff(c_16695,plain,(
    ! [B_1651,B_17] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_1651),B_17) = k2_zfmisc_1(B_1651,k3_xboole_0(k1_xboole_0,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16458,c_16683])).

tff(c_16461,plain,(
    ! [A_16,A_1635] : k3_xboole_0(k2_zfmisc_1(A_16,A_1635),k1_xboole_0) = k2_zfmisc_1(A_16,k3_xboole_0(A_1635,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_16420])).

tff(c_16686,plain,(
    ! [A_1649,B_17] : k3_xboole_0(k2_zfmisc_1(A_1649,B_17),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(A_1649,k1_xboole_0),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_16631])).

tff(c_16768,plain,(
    ! [A_1654,B_1655] : k2_zfmisc_1(k3_xboole_0(A_1654,k1_xboole_0),B_1655) = k2_zfmisc_1(A_1654,k3_xboole_0(B_1655,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16461,c_16686])).

tff(c_16998,plain,(
    ! [B_1662,B_1663] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_1662),B_1663) = k2_zfmisc_1(B_1662,k3_xboole_0(B_1663,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16768])).

tff(c_17062,plain,(
    ! [B_1651,B_17] : k2_zfmisc_1(B_1651,k3_xboole_0(k1_xboole_0,B_17)) = k2_zfmisc_1(B_1651,k3_xboole_0(B_17,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16695,c_16998])).

tff(c_17579,plain,(
    ! [A_1681,C_1682,B_1683,D_1684] : k3_xboole_0(k2_zfmisc_1(A_1681,C_1682),k2_zfmisc_1(B_1683,D_1684)) = k2_zfmisc_1(k3_xboole_0(A_1681,B_1683),k3_xboole_0(C_1682,D_1684)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_17682,plain,(
    ! [A_1681,C_1682,B_17] : k2_zfmisc_1(k3_xboole_0(A_1681,k1_xboole_0),k3_xboole_0(C_1682,B_17)) = k3_xboole_0(k2_zfmisc_1(A_1681,C_1682),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_17579])).

tff(c_17779,plain,(
    ! [A_1686,C_1687,B_1688] : k2_zfmisc_1(k3_xboole_0(A_1686,k1_xboole_0),k3_xboole_0(C_1687,B_1688)) = k2_zfmisc_1(A_1686,k3_xboole_0(k1_xboole_0,C_1687)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16458,c_2,c_17682])).

tff(c_17879,plain,(
    ! [A_1686,B_17] : k2_zfmisc_1(k3_xboole_0(A_1686,k1_xboole_0),k3_xboole_0(B_17,k1_xboole_0)) = k2_zfmisc_1(A_1686,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17062,c_17779])).

tff(c_18762,plain,(
    ! [A_2298,B_2299] : k2_zfmisc_1(k3_xboole_0(A_2298,k1_xboole_0),k3_xboole_0(B_2299,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16246,c_17879])).

tff(c_17704,plain,(
    ! [A_1681,C_1682,B_17] : k2_zfmisc_1(k3_xboole_0(A_1681,k1_xboole_0),k3_xboole_0(C_1682,B_17)) = k2_zfmisc_1(A_1681,k3_xboole_0(k1_xboole_0,C_1682)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16458,c_2,c_17682])).

tff(c_18767,plain,(
    ! [A_2298,B_2299] : k2_zfmisc_1(A_2298,k3_xboole_0(k1_xboole_0,B_2299)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18762,c_17704])).

tff(c_18932,plain,(
    ! [B_1651,B_17] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_1651),B_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18767,c_16695])).

tff(c_16829,plain,(
    ! [B_2,B_1655] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_2),B_1655) = k2_zfmisc_1(B_2,k3_xboole_0(B_1655,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16768])).

tff(c_19168,plain,(
    ! [B_2,B_1655] : k2_zfmisc_1(B_2,k3_xboole_0(B_1655,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18932,c_16829])).

tff(c_16194,plain,(
    ! [A_1600,B_1601] :
      ( k3_xboole_0(A_1600,B_1601) = A_1600
      | ~ r1_tarski(A_1600,B_1601) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16202,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_16194])).

tff(c_17923,plain,(
    ! [A_1686] : k2_zfmisc_1(k3_xboole_0(A_1686,k1_xboole_0),k2_zfmisc_1('#skF_4','#skF_5')) = k2_zfmisc_1(A_1686,k3_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16202,c_17779])).

tff(c_18626,plain,(
    ! [A_2297] : k2_zfmisc_1(k3_xboole_0(A_2297,k1_xboole_0),k2_zfmisc_1('#skF_4','#skF_5')) = k2_zfmisc_1(A_2297,k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16458,c_17923])).

tff(c_18697,plain,(
    ! [A_2297] :
      ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
      | k3_xboole_0(A_2297,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1(A_2297,k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5',k1_xboole_0))) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18626,c_30])).

tff(c_18752,plain,(
    ! [A_2297] :
      ( k3_xboole_0(A_2297,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1(A_2297,k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5',k1_xboole_0))) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_18697])).

tff(c_19464,plain,(
    ! [A_2297] :
      ( k3_xboole_0(A_2297,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1(A_2297,k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19168,c_18752])).

tff(c_19468,plain,(
    ! [A_2297] : k3_xboole_0(A_2297,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_19464])).

tff(c_16259,plain,(
    ! [D_1612,A_1613,B_1614] :
      ( r2_hidden(D_1612,A_1613)
      | ~ r2_hidden(D_1612,k3_xboole_0(A_1613,B_1614)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20141,plain,(
    ! [A_2350,B_2351,B_2352] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_2350,B_2351),B_2352),A_2350)
      | r1_tarski(k3_xboole_0(A_2350,B_2351),B_2352) ) ),
    inference(resolution,[status(thm)],[c_8,c_16259])).

tff(c_20221,plain,(
    ! [A_2353,B_2354] : r1_tarski(k3_xboole_0(A_2353,B_2354),A_2353) ),
    inference(resolution,[status(thm)],[c_20141,c_6])).

tff(c_20241,plain,(
    ! [A_2297] : r1_tarski(k1_xboole_0,A_2297) ),
    inference(superposition,[status(thm),theory(equality)],[c_19468,c_20221])).

tff(c_16291,plain,(
    ! [C_1617,B_1618,A_1619] :
      ( r2_hidden(C_1617,B_1618)
      | ~ r2_hidden(C_1617,A_1619)
      | ~ r1_tarski(A_1619,B_1618) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16296,plain,(
    ! [A_3,B_4,B_1618] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_1618)
      | ~ r1_tarski(A_3,B_1618)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_16291])).

tff(c_16310,plain,(
    ! [D_1623] :
      ( r2_hidden(D_1623,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_1623,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16202,c_12])).

tff(c_16933,plain,(
    ! [A_1658] :
      ( r1_tarski(A_1658,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden('#skF_1'(A_1658,k2_zfmisc_1('#skF_6','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16310,c_6])).

tff(c_16947,plain,(
    ! [A_3] :
      ( ~ r1_tarski(A_3,k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(A_3,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_16296,c_16933])).

tff(c_17438,plain,(
    ! [A_1674,B_1675,C_1676] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1674,B_1675),k2_zfmisc_1(A_1674,C_1676))
      | r1_tarski(B_1675,C_1676)
      | k1_xboole_0 = A_1674 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_17512,plain,(
    ! [A_1677,C_1678] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_1677,C_1678))
      | r1_tarski(k1_xboole_0,C_1678)
      | k1_xboole_0 = A_1677 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17438])).

tff(c_17541,plain,
    ( r1_tarski(k1_xboole_0,'#skF_7')
    | k1_xboole_0 = '#skF_6'
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16947,c_17512])).

tff(c_17578,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_17541])).

tff(c_20281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20241,c_17578])).

tff(c_20283,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_17541])).

tff(c_17485,plain,(
    ! [A_16,C_1676] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_16,C_1676))
      | r1_tarski(k1_xboole_0,C_1676)
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17438])).

tff(c_20492,plain,
    ( r1_tarski(k1_xboole_0,'#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20283,c_17485])).

tff(c_20564,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20492])).

tff(c_20587,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_4',B_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20564,c_20564,c_34])).

tff(c_20588,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20564,c_48])).

tff(c_20702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20587,c_20588])).

tff(c_20704,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20492])).

tff(c_16160,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16201,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16160,c_16194])).

tff(c_20356,plain,(
    ! [A_2355,C_2356,B_2357,D_2358] : k3_xboole_0(k2_zfmisc_1(A_2355,C_2356),k2_zfmisc_1(B_2357,D_2358)) = k2_zfmisc_1(k3_xboole_0(A_2355,B_2357),k3_xboole_0(C_2356,D_2358)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20380,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20356,c_16202])).

tff(c_20464,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16201,c_20380])).

tff(c_20513,plain,(
    ! [B_19] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_19),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_19,k3_xboole_0('#skF_5','#skF_7'))
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20464,c_36])).

tff(c_22162,plain,(
    ! [B_2408] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_2408),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_2408,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20704,c_20513])).

tff(c_22176,plain,(
    r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_16233,c_22162])).

tff(c_22182,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22176,c_28])).

tff(c_20510,plain,(
    ! [C_20] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_20))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_20)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20464,c_36])).

tff(c_22045,plain,(
    ! [C_2404] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_2404))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_2404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20704,c_20510])).

tff(c_22059,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_16233,c_22045])).

tff(c_22063,plain,(
    k3_xboole_0(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') = k3_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_22059,c_28])).

tff(c_22418,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = k3_xboole_0('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_22063,c_2])).

tff(c_22430,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22182,c_22418])).

tff(c_22512,plain,(
    ! [A_2418,B_2419,B_2420] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_2418,B_2419),B_2420),A_2418)
      | r1_tarski(k3_xboole_0(A_2418,B_2419),B_2420) ) ),
    inference(resolution,[status(thm)],[c_8,c_16259])).

tff(c_22600,plain,(
    ! [A_2421,B_2422] : r1_tarski(k3_xboole_0(A_2421,B_2422),A_2421) ),
    inference(resolution,[status(thm)],[c_22512,c_6])).

tff(c_22674,plain,(
    ! [B_2424,A_2425] : r1_tarski(k3_xboole_0(B_2424,A_2425),A_2425) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22600])).

tff(c_22684,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_22430,c_22674])).

tff(c_22724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16159,c_22684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.56/3.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.56/3.94  
% 10.56/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.56/3.95  %$ r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.56/3.95  
% 10.56/3.95  %Foreground sorts:
% 10.56/3.95  
% 10.56/3.95  
% 10.56/3.95  %Background operators:
% 10.56/3.95  
% 10.56/3.95  
% 10.56/3.95  %Foreground operators:
% 10.56/3.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.56/3.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.56/3.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.56/3.95  tff('#skF_7', type, '#skF_7': $i).
% 10.56/3.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.56/3.95  tff('#skF_5', type, '#skF_5': $i).
% 10.56/3.95  tff('#skF_6', type, '#skF_6': $i).
% 10.56/3.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.56/3.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.56/3.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.56/3.95  tff('#skF_4', type, '#skF_4': $i).
% 10.56/3.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.56/3.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.56/3.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.56/3.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.56/3.95  
% 10.84/3.98  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.84/3.98  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.84/3.98  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.84/3.98  tff(f_68, axiom, (![A, B, C]: ((k2_zfmisc_1(k3_xboole_0(A, B), C) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_zfmisc_1)).
% 10.84/3.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.84/3.98  tff(f_70, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 10.84/3.98  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 10.84/3.98  tff(f_64, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 10.84/3.98  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.84/3.98  tff(c_32, plain, (![A_16]: (k2_zfmisc_1(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.84/3.98  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_143, plain, (![A_41, B_42]: (~r2_hidden('#skF_1'(A_41, B_42), B_42) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_149, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_8, c_143])).
% 10.84/3.98  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.84/3.98  tff(c_153, plain, (![A_43]: (k3_xboole_0(A_43, A_43)=A_43)), inference(resolution, [status(thm)], [c_149, c_28])).
% 10.84/3.98  tff(c_34, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.84/3.98  tff(c_148, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_143])).
% 10.84/3.98  tff(c_755, plain, (![C_93, A_94, B_95]: (k3_xboole_0(k2_zfmisc_1(C_93, A_94), k2_zfmisc_1(C_93, B_95))=k2_zfmisc_1(C_93, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.84/3.98  tff(c_813, plain, (![A_16, B_95]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_16, B_95))=k2_zfmisc_1(A_16, k3_xboole_0(k1_xboole_0, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_755])).
% 10.84/3.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.84/3.98  tff(c_1328, plain, (![A_108, C_109, B_110, D_111]: (k3_xboole_0(k2_zfmisc_1(A_108, C_109), k2_zfmisc_1(B_110, D_111))=k2_zfmisc_1(k3_xboole_0(A_108, B_110), k3_xboole_0(C_109, D_111)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.84/3.98  tff(c_1413, plain, (![A_108, A_16, C_109]: (k2_zfmisc_1(k3_xboole_0(A_108, A_16), k3_xboole_0(C_109, k1_xboole_0))=k3_xboole_0(k2_zfmisc_1(A_108, C_109), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1328])).
% 10.84/3.98  tff(c_2686, plain, (![A_147, A_148, C_149]: (k2_zfmisc_1(k3_xboole_0(A_147, A_148), k3_xboole_0(C_149, k1_xboole_0))=k2_zfmisc_1(A_147, k3_xboole_0(k1_xboole_0, C_149)))), inference(demodulation, [status(thm), theory('equality')], [c_813, c_2, c_1413])).
% 10.84/3.98  tff(c_245, plain, (![A_58, C_59, B_60]: (k3_xboole_0(k2_zfmisc_1(A_58, C_59), k2_zfmisc_1(B_60, C_59))=k2_zfmisc_1(k3_xboole_0(A_58, B_60), C_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.84/3.98  tff(c_289, plain, (![B_60, B_17]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_60, B_17))=k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_60), B_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_245])).
% 10.84/3.98  tff(c_832, plain, (![B_60, B_17]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_60), B_17)=k2_zfmisc_1(B_60, k3_xboole_0(k1_xboole_0, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_813, c_289])).
% 10.84/3.98  tff(c_2738, plain, (![A_148, C_149]: (k2_zfmisc_1(A_148, k3_xboole_0(k1_xboole_0, k3_xboole_0(C_149, k1_xboole_0)))=k2_zfmisc_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_2686, c_832])).
% 10.84/3.98  tff(c_2904, plain, (![A_153, C_154]: (k2_zfmisc_1(A_153, k3_xboole_0(k1_xboole_0, k3_xboole_0(C_154, k1_xboole_0)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2738])).
% 10.84/3.98  tff(c_30, plain, (![B_17, A_16]: (k1_xboole_0=B_17 | k1_xboole_0=A_16 | k2_zfmisc_1(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.84/3.98  tff(c_3072, plain, (![C_154, A_153]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(C_154, k1_xboole_0))=k1_xboole_0 | k1_xboole_0=A_153)), inference(superposition, [status(thm), theory('equality')], [c_2904, c_30])).
% 10.84/3.98  tff(c_3164, plain, (![A_156]: (k1_xboole_0=A_156)), inference(splitLeft, [status(thm)], [c_3072])).
% 10.84/3.98  tff(c_50, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.84/3.98  tff(c_111, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_28])).
% 10.84/3.98  tff(c_1352, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1328, c_111])).
% 10.84/3.98  tff(c_512, plain, (![A_82, B_83, C_84]: (~r1_tarski(k2_zfmisc_1(A_82, B_83), k2_zfmisc_1(A_82, C_84)) | r1_tarski(B_83, C_84) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.84/3.98  tff(c_522, plain, (![A_16, B_83]: (~r1_tarski(k2_zfmisc_1(A_16, B_83), k1_xboole_0) | r1_tarski(B_83, k1_xboole_0) | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_32, c_512])).
% 10.84/3.98  tff(c_1556, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1352, c_522])).
% 10.84/3.98  tff(c_1672, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1556])).
% 10.84/3.98  tff(c_3278, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3164, c_1672])).
% 10.84/3.98  tff(c_3528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_3278])).
% 10.84/3.98  tff(c_3532, plain, (![C_782]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(C_782, k1_xboole_0))=k1_xboole_0)), inference(splitRight, [status(thm)], [c_3072])).
% 10.84/3.98  tff(c_816, plain, (![A_16, A_94]: (k3_xboole_0(k2_zfmisc_1(A_16, A_94), k1_xboole_0)=k2_zfmisc_1(A_16, k3_xboole_0(A_94, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_755])).
% 10.84/3.98  tff(c_292, plain, (![A_58, B_17]: (k3_xboole_0(k2_zfmisc_1(A_58, B_17), k1_xboole_0)=k2_zfmisc_1(k3_xboole_0(A_58, k1_xboole_0), B_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_245])).
% 10.84/3.98  tff(c_1013, plain, (![A_102, B_103]: (k2_zfmisc_1(k3_xboole_0(A_102, k1_xboole_0), B_103)=k2_zfmisc_1(A_102, k3_xboole_0(B_103, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_292])).
% 10.84/3.98  tff(c_1087, plain, (![A_1, B_103]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, A_1), B_103)=k2_zfmisc_1(A_1, k3_xboole_0(B_103, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1013])).
% 10.84/3.98  tff(c_3545, plain, (![C_782, B_103]: (k2_zfmisc_1(k3_xboole_0(C_782, k1_xboole_0), k3_xboole_0(B_103, k1_xboole_0))=k2_zfmisc_1(k1_xboole_0, B_103))), inference(superposition, [status(thm), theory('equality')], [c_3532, c_1087])).
% 10.84/3.98  tff(c_3763, plain, (![C_791, B_792]: (k2_zfmisc_1(k3_xboole_0(C_791, k1_xboole_0), k3_xboole_0(B_792, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3545])).
% 10.84/3.98  tff(c_1437, plain, (![A_108, A_16, C_109]: (k2_zfmisc_1(k3_xboole_0(A_108, A_16), k3_xboole_0(C_109, k1_xboole_0))=k2_zfmisc_1(A_108, k3_xboole_0(k1_xboole_0, C_109)))), inference(demodulation, [status(thm), theory('equality')], [c_813, c_2, c_1413])).
% 10.84/3.98  tff(c_3768, plain, (![C_791, B_792]: (k2_zfmisc_1(C_791, k3_xboole_0(k1_xboole_0, B_792))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3763, c_1437])).
% 10.84/3.98  tff(c_920, plain, (![B_100, B_101]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_100), B_101)=k2_zfmisc_1(B_100, k3_xboole_0(k1_xboole_0, B_101)))), inference(demodulation, [status(thm), theory('equality')], [c_813, c_289])).
% 10.84/3.98  tff(c_990, plain, (![B_2, B_101]: (k2_zfmisc_1(k3_xboole_0(B_2, k1_xboole_0), B_101)=k2_zfmisc_1(B_2, k3_xboole_0(k1_xboole_0, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_920])).
% 10.84/3.98  tff(c_4320, plain, (![B_800, B_801]: (k2_zfmisc_1(k3_xboole_0(B_800, k1_xboole_0), B_801)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_990])).
% 10.84/3.98  tff(c_4443, plain, (![B_801, B_800]: (k1_xboole_0=B_801 | k3_xboole_0(B_800, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4320, c_30])).
% 10.84/3.98  tff(c_4919, plain, (![B_811]: (k3_xboole_0(B_811, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4443])).
% 10.84/3.98  tff(c_4955, plain, (![B_811]: (k3_xboole_0(k1_xboole_0, B_811)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4919, c_2])).
% 10.84/3.98  tff(c_137, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.84/3.98  tff(c_5617, plain, (![A_826, B_827, B_828]: (r2_hidden('#skF_1'(k3_xboole_0(A_826, B_827), B_828), B_827) | r1_tarski(k3_xboole_0(A_826, B_827), B_828))), inference(resolution, [status(thm)], [c_137, c_12])).
% 10.84/3.98  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_5714, plain, (![A_829, B_830]: (r1_tarski(k3_xboole_0(A_829, B_830), B_830))), inference(resolution, [status(thm)], [c_5617, c_6])).
% 10.84/3.98  tff(c_5736, plain, (![B_811]: (r1_tarski(k1_xboole_0, B_811))), inference(superposition, [status(thm), theory('equality')], [c_4955, c_5714])).
% 10.84/3.98  tff(c_184, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_187, plain, (![A_3, B_4, B_49]: (r2_hidden('#skF_1'(A_3, B_4), B_49) | ~r1_tarski(A_3, B_49) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_184])).
% 10.84/3.98  tff(c_188, plain, (![D_51]: (r2_hidden(D_51, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(D_51, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_12])).
% 10.84/3.98  tff(c_561, plain, (![A_89]: (r1_tarski(A_89, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden('#skF_1'(A_89, k2_zfmisc_1('#skF_6', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_188, c_6])).
% 10.84/3.98  tff(c_726, plain, (![A_92]: (~r1_tarski(A_92, k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(A_92, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_187, c_561])).
% 10.84/3.98  tff(c_363, plain, (![B_65, A_66, C_67]: (~r1_tarski(k2_zfmisc_1(B_65, A_66), k2_zfmisc_1(C_67, A_66)) | r1_tarski(B_65, C_67) | k1_xboole_0=A_66)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.84/3.98  tff(c_376, plain, (![C_67, B_17]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(C_67, B_17)) | r1_tarski(k1_xboole_0, C_67) | k1_xboole_0=B_17)), inference(superposition, [status(thm), theory('equality')], [c_34, c_363])).
% 10.84/3.98  tff(c_752, plain, (r1_tarski(k1_xboole_0, '#skF_6') | k1_xboole_0='#skF_7' | ~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_726, c_376])).
% 10.84/3.98  tff(c_1011, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_752])).
% 10.84/3.98  tff(c_5778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5736, c_1011])).
% 10.84/3.98  tff(c_5780, plain, (![B_831]: (k1_xboole_0=B_831)), inference(splitRight, [status(thm)], [c_4443])).
% 10.84/3.98  tff(c_48, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.84/3.98  tff(c_38, plain, (![B_19, A_18, C_20]: (~r1_tarski(k2_zfmisc_1(B_19, A_18), k2_zfmisc_1(C_20, A_18)) | r1_tarski(B_19, C_20) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.84/3.98  tff(c_1574, plain, (![C_20]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(C_20, k3_xboole_0('#skF_5', '#skF_7'))) | r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), C_20) | k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1352, c_38])).
% 10.84/3.98  tff(c_4309, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1574])).
% 10.84/3.98  tff(c_4312, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k1_xboole_0)=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4309, c_1352])).
% 10.84/3.98  tff(c_4315, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4312])).
% 10.84/3.98  tff(c_4317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_4315])).
% 10.84/3.98  tff(c_4319, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1574])).
% 10.84/3.98  tff(c_5935, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5780, c_4319])).
% 10.84/3.98  tff(c_5937, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1556])).
% 10.84/3.98  tff(c_379, plain, (![B_65, B_17]: (~r1_tarski(k2_zfmisc_1(B_65, B_17), k1_xboole_0) | r1_tarski(B_65, k1_xboole_0) | k1_xboole_0=B_17)), inference(superposition, [status(thm), theory('equality')], [c_34, c_363])).
% 10.84/3.98  tff(c_5965, plain, (r1_tarski('#skF_4', k1_xboole_0) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5937, c_379])).
% 10.84/3.98  tff(c_6146, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_5965])).
% 10.84/3.98  tff(c_6168, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6146, c_6146, c_32])).
% 10.84/3.98  tff(c_6170, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6146, c_48])).
% 10.84/3.98  tff(c_6248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6168, c_6170])).
% 10.84/3.98  tff(c_6249, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5965])).
% 10.84/3.98  tff(c_6254, plain, (k3_xboole_0('#skF_4', k1_xboole_0)='#skF_4'), inference(resolution, [status(thm)], [c_6249, c_28])).
% 10.84/3.98  tff(c_1416, plain, (![B_110, B_17, D_111]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_110), k3_xboole_0(B_17, D_111))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_110, D_111)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1328])).
% 10.84/3.98  tff(c_9523, plain, (![B_1441, B_1442, D_1443]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_1441), k3_xboole_0(B_1442, D_1443))=k2_zfmisc_1(B_1441, k3_xboole_0(k1_xboole_0, D_1443)))), inference(demodulation, [status(thm), theory('equality')], [c_813, c_1416])).
% 10.84/3.98  tff(c_9682, plain, (![B_1441]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_1441), '#skF_4')=k2_zfmisc_1(B_1441, k3_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6254, c_9523])).
% 10.84/3.98  tff(c_9788, plain, (![B_1441]: (k2_zfmisc_1(B_1441, '#skF_4')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_153, c_6254, c_1087, c_9682])).
% 10.84/3.98  tff(c_5964, plain, (r1_tarski('#skF_5', k1_xboole_0) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5937, c_522])).
% 10.84/3.98  tff(c_5968, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5964])).
% 10.84/3.98  tff(c_6040, plain, (![B_17]: (k2_zfmisc_1('#skF_4', B_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_5968, c_34])).
% 10.84/3.98  tff(c_6041, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_48])).
% 10.84/3.98  tff(c_6118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6040, c_6041])).
% 10.84/3.98  tff(c_6120, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5964])).
% 10.84/3.98  tff(c_867, plain, (![A_58, B_17]: (k2_zfmisc_1(k3_xboole_0(A_58, k1_xboole_0), B_17)=k2_zfmisc_1(A_58, k3_xboole_0(B_17, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_292])).
% 10.84/3.98  tff(c_6731, plain, (![B_1382]: (k2_zfmisc_1('#skF_4', k3_xboole_0(B_1382, k1_xboole_0))=k2_zfmisc_1('#skF_4', B_1382))), inference(superposition, [status(thm), theory('equality')], [c_6254, c_867])).
% 10.84/3.98  tff(c_6798, plain, (![B_1382]: (k3_xboole_0(B_1382, k1_xboole_0)=k1_xboole_0 | k1_xboole_0='#skF_4' | k2_zfmisc_1('#skF_4', B_1382)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6731, c_30])).
% 10.84/3.98  tff(c_7882, plain, (![B_1413]: (k3_xboole_0(B_1413, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1('#skF_4', B_1413)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_6120, c_6798])).
% 10.84/3.98  tff(c_7915, plain, (k1_xboole_0='#skF_4' | k2_zfmisc_1('#skF_4', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7882, c_6254])).
% 10.84/3.98  tff(c_8011, plain, (k2_zfmisc_1('#skF_4', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6120, c_7915])).
% 10.84/3.98  tff(c_9807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9788, c_8011])).
% 10.84/3.98  tff(c_9809, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_752])).
% 10.84/3.98  tff(c_519, plain, (![A_16, C_84]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_16, C_84)) | r1_tarski(k1_xboole_0, C_84) | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_32, c_512])).
% 10.84/3.98  tff(c_749, plain, (r1_tarski(k1_xboole_0, '#skF_7') | k1_xboole_0='#skF_6' | ~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_726, c_519])).
% 10.84/3.98  tff(c_9815, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_749])).
% 10.84/3.98  tff(c_9965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9809, c_9815])).
% 10.84/3.98  tff(c_9967, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_749])).
% 10.84/3.98  tff(c_10037, plain, (r1_tarski(k1_xboole_0, '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_9967, c_376])).
% 10.84/3.98  tff(c_10399, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_10037])).
% 10.84/3.98  tff(c_10422, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10399, c_10399, c_32])).
% 10.84/3.98  tff(c_10424, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10399, c_48])).
% 10.84/3.98  tff(c_10478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10422, c_10424])).
% 10.84/3.98  tff(c_10480, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_10037])).
% 10.84/3.98  tff(c_46, plain, (~r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.84/3.98  tff(c_73, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_46])).
% 10.84/3.98  tff(c_280, plain, (![B_60, C_59, A_58]: (k3_xboole_0(k2_zfmisc_1(B_60, C_59), k2_zfmisc_1(A_58, C_59))=k2_zfmisc_1(k3_xboole_0(A_58, B_60), C_59))), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 10.84/3.98  tff(c_12971, plain, (![A_1546, B_1547, B_1548]: (r2_hidden('#skF_1'(k3_xboole_0(A_1546, B_1547), B_1548), B_1547) | r1_tarski(k3_xboole_0(A_1546, B_1547), B_1548))), inference(resolution, [status(thm)], [c_137, c_12])).
% 10.84/3.98  tff(c_13064, plain, (![A_1549, B_1550]: (r1_tarski(k3_xboole_0(A_1549, B_1550), B_1550))), inference(resolution, [status(thm)], [c_12971, c_6])).
% 10.84/3.98  tff(c_15321, plain, (![A_1588, B_1589, C_1590]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_1588, B_1589), C_1590), k2_zfmisc_1(A_1588, C_1590)))), inference(superposition, [status(thm), theory('equality')], [c_280, c_13064])).
% 10.84/3.98  tff(c_10039, plain, (![A_1449, C_1450, B_1451, D_1452]: (k3_xboole_0(k2_zfmisc_1(A_1449, C_1450), k2_zfmisc_1(B_1451, D_1452))=k2_zfmisc_1(k3_xboole_0(A_1449, B_1451), k3_xboole_0(C_1450, D_1452)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.84/3.98  tff(c_10094, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_111, c_10039])).
% 10.84/3.98  tff(c_36, plain, (![A_18, B_19, C_20]: (~r1_tarski(k2_zfmisc_1(A_18, B_19), k2_zfmisc_1(A_18, C_20)) | r1_tarski(B_19, C_20) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.84/3.98  tff(c_10188, plain, (![C_20]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), C_20)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_20) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10094, c_36])).
% 10.84/3.98  tff(c_11318, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10188])).
% 10.84/3.98  tff(c_11321, plain, (k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11318, c_10094])).
% 10.84/3.98  tff(c_11324, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_11321])).
% 10.84/3.98  tff(c_11326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_11324])).
% 10.84/3.98  tff(c_11328, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_10188])).
% 10.84/3.98  tff(c_10191, plain, (![B_19]: (~r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), B_19), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_19, k3_xboole_0('#skF_5', '#skF_7')) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10094, c_36])).
% 10.84/3.98  tff(c_11380, plain, (![B_19]: (~r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), B_19), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_19, k3_xboole_0('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_11328, c_10191])).
% 10.84/3.98  tff(c_15444, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_15321, c_11380])).
% 10.84/3.98  tff(c_15469, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(resolution, [status(thm)], [c_15444, c_28])).
% 10.84/3.98  tff(c_13125, plain, (![B_1551, A_1552]: (r1_tarski(k3_xboole_0(B_1551, A_1552), B_1551))), inference(superposition, [status(thm), theory('equality')], [c_2, c_13064])).
% 10.84/3.98  tff(c_13447, plain, (![B_1559, A_1560]: (k3_xboole_0(k3_xboole_0(B_1559, A_1560), B_1559)=k3_xboole_0(B_1559, A_1560))), inference(resolution, [status(thm)], [c_13125, c_28])).
% 10.84/3.98  tff(c_13576, plain, (![A_1, A_1560]: (k3_xboole_0(A_1, k3_xboole_0(A_1, A_1560))=k3_xboole_0(A_1, A_1560))), inference(superposition, [status(thm), theory('equality')], [c_2, c_13447])).
% 10.84/3.98  tff(c_15530, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_15469, c_13576])).
% 10.84/3.98  tff(c_15615, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15530, c_10094])).
% 10.84/3.98  tff(c_40, plain, (![A_21, C_23, B_22]: (k3_xboole_0(k2_zfmisc_1(A_21, C_23), k2_zfmisc_1(B_22, C_23))=k2_zfmisc_1(k3_xboole_0(A_21, B_22), C_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.84/3.98  tff(c_13104, plain, (![A_21, B_22, C_23]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_21, B_22), C_23), k2_zfmisc_1(B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_13064])).
% 10.84/3.98  tff(c_16071, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15615, c_13104])).
% 10.84/3.98  tff(c_16151, plain, (r1_tarski('#skF_4', '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16071, c_38])).
% 10.84/3.98  tff(c_16158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10480, c_73, c_16151])).
% 10.84/3.98  tff(c_16159, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 10.84/3.98  tff(c_16224, plain, (![A_1608, B_1609]: (~r2_hidden('#skF_1'(A_1608, B_1609), B_1609) | r1_tarski(A_1608, B_1609))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_16233, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_16224])).
% 10.84/3.98  tff(c_16242, plain, (![A_1610]: (r1_tarski(A_1610, A_1610))), inference(resolution, [status(thm)], [c_8, c_16224])).
% 10.84/3.98  tff(c_16246, plain, (![A_1610]: (k3_xboole_0(A_1610, A_1610)=A_1610)), inference(resolution, [status(thm)], [c_16242, c_28])).
% 10.84/3.98  tff(c_16420, plain, (![C_1634, A_1635, B_1636]: (k3_xboole_0(k2_zfmisc_1(C_1634, A_1635), k2_zfmisc_1(C_1634, B_1636))=k2_zfmisc_1(C_1634, k3_xboole_0(A_1635, B_1636)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.84/3.98  tff(c_16458, plain, (![A_16, B_1636]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_16, B_1636))=k2_zfmisc_1(A_16, k3_xboole_0(k1_xboole_0, B_1636)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_16420])).
% 10.84/3.98  tff(c_16631, plain, (![A_1649, C_1650, B_1651]: (k3_xboole_0(k2_zfmisc_1(A_1649, C_1650), k2_zfmisc_1(B_1651, C_1650))=k2_zfmisc_1(k3_xboole_0(A_1649, B_1651), C_1650))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.84/3.98  tff(c_16683, plain, (![B_1651, B_17]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_1651, B_17))=k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_1651), B_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_16631])).
% 10.84/3.98  tff(c_16695, plain, (![B_1651, B_17]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_1651), B_17)=k2_zfmisc_1(B_1651, k3_xboole_0(k1_xboole_0, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_16458, c_16683])).
% 10.84/3.98  tff(c_16461, plain, (![A_16, A_1635]: (k3_xboole_0(k2_zfmisc_1(A_16, A_1635), k1_xboole_0)=k2_zfmisc_1(A_16, k3_xboole_0(A_1635, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_16420])).
% 10.84/3.98  tff(c_16686, plain, (![A_1649, B_17]: (k3_xboole_0(k2_zfmisc_1(A_1649, B_17), k1_xboole_0)=k2_zfmisc_1(k3_xboole_0(A_1649, k1_xboole_0), B_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_16631])).
% 10.84/3.98  tff(c_16768, plain, (![A_1654, B_1655]: (k2_zfmisc_1(k3_xboole_0(A_1654, k1_xboole_0), B_1655)=k2_zfmisc_1(A_1654, k3_xboole_0(B_1655, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16461, c_16686])).
% 10.84/3.98  tff(c_16998, plain, (![B_1662, B_1663]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_1662), B_1663)=k2_zfmisc_1(B_1662, k3_xboole_0(B_1663, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16768])).
% 10.84/3.98  tff(c_17062, plain, (![B_1651, B_17]: (k2_zfmisc_1(B_1651, k3_xboole_0(k1_xboole_0, B_17))=k2_zfmisc_1(B_1651, k3_xboole_0(B_17, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16695, c_16998])).
% 10.84/3.98  tff(c_17579, plain, (![A_1681, C_1682, B_1683, D_1684]: (k3_xboole_0(k2_zfmisc_1(A_1681, C_1682), k2_zfmisc_1(B_1683, D_1684))=k2_zfmisc_1(k3_xboole_0(A_1681, B_1683), k3_xboole_0(C_1682, D_1684)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.84/3.98  tff(c_17682, plain, (![A_1681, C_1682, B_17]: (k2_zfmisc_1(k3_xboole_0(A_1681, k1_xboole_0), k3_xboole_0(C_1682, B_17))=k3_xboole_0(k2_zfmisc_1(A_1681, C_1682), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_17579])).
% 10.84/3.98  tff(c_17779, plain, (![A_1686, C_1687, B_1688]: (k2_zfmisc_1(k3_xboole_0(A_1686, k1_xboole_0), k3_xboole_0(C_1687, B_1688))=k2_zfmisc_1(A_1686, k3_xboole_0(k1_xboole_0, C_1687)))), inference(demodulation, [status(thm), theory('equality')], [c_16458, c_2, c_17682])).
% 10.84/3.98  tff(c_17879, plain, (![A_1686, B_17]: (k2_zfmisc_1(k3_xboole_0(A_1686, k1_xboole_0), k3_xboole_0(B_17, k1_xboole_0))=k2_zfmisc_1(A_1686, k3_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_17062, c_17779])).
% 10.84/3.98  tff(c_18762, plain, (![A_2298, B_2299]: (k2_zfmisc_1(k3_xboole_0(A_2298, k1_xboole_0), k3_xboole_0(B_2299, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16246, c_17879])).
% 10.84/3.98  tff(c_17704, plain, (![A_1681, C_1682, B_17]: (k2_zfmisc_1(k3_xboole_0(A_1681, k1_xboole_0), k3_xboole_0(C_1682, B_17))=k2_zfmisc_1(A_1681, k3_xboole_0(k1_xboole_0, C_1682)))), inference(demodulation, [status(thm), theory('equality')], [c_16458, c_2, c_17682])).
% 10.84/3.98  tff(c_18767, plain, (![A_2298, B_2299]: (k2_zfmisc_1(A_2298, k3_xboole_0(k1_xboole_0, B_2299))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18762, c_17704])).
% 10.84/3.98  tff(c_18932, plain, (![B_1651, B_17]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_1651), B_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18767, c_16695])).
% 10.84/3.98  tff(c_16829, plain, (![B_2, B_1655]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_2), B_1655)=k2_zfmisc_1(B_2, k3_xboole_0(B_1655, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16768])).
% 10.84/3.98  tff(c_19168, plain, (![B_2, B_1655]: (k2_zfmisc_1(B_2, k3_xboole_0(B_1655, k1_xboole_0))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18932, c_16829])).
% 10.84/3.98  tff(c_16194, plain, (![A_1600, B_1601]: (k3_xboole_0(A_1600, B_1601)=A_1600 | ~r1_tarski(A_1600, B_1601))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.84/3.98  tff(c_16202, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_16194])).
% 10.84/3.98  tff(c_17923, plain, (![A_1686]: (k2_zfmisc_1(k3_xboole_0(A_1686, k1_xboole_0), k2_zfmisc_1('#skF_4', '#skF_5'))=k2_zfmisc_1(A_1686, k3_xboole_0(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_16202, c_17779])).
% 10.84/3.98  tff(c_18626, plain, (![A_2297]: (k2_zfmisc_1(k3_xboole_0(A_2297, k1_xboole_0), k2_zfmisc_1('#skF_4', '#skF_5'))=k2_zfmisc_1(A_2297, k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', k1_xboole_0))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16458, c_17923])).
% 10.84/3.98  tff(c_18697, plain, (![A_2297]: (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_xboole_0(A_2297, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1(A_2297, k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', k1_xboole_0)))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18626, c_30])).
% 10.84/3.98  tff(c_18752, plain, (![A_2297]: (k3_xboole_0(A_2297, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1(A_2297, k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', k1_xboole_0)))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_18697])).
% 10.84/3.98  tff(c_19464, plain, (![A_2297]: (k3_xboole_0(A_2297, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1(A_2297, k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_19168, c_18752])).
% 10.84/3.98  tff(c_19468, plain, (![A_2297]: (k3_xboole_0(A_2297, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_19464])).
% 10.84/3.98  tff(c_16259, plain, (![D_1612, A_1613, B_1614]: (r2_hidden(D_1612, A_1613) | ~r2_hidden(D_1612, k3_xboole_0(A_1613, B_1614)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.84/3.98  tff(c_20141, plain, (![A_2350, B_2351, B_2352]: (r2_hidden('#skF_1'(k3_xboole_0(A_2350, B_2351), B_2352), A_2350) | r1_tarski(k3_xboole_0(A_2350, B_2351), B_2352))), inference(resolution, [status(thm)], [c_8, c_16259])).
% 10.84/3.98  tff(c_20221, plain, (![A_2353, B_2354]: (r1_tarski(k3_xboole_0(A_2353, B_2354), A_2353))), inference(resolution, [status(thm)], [c_20141, c_6])).
% 10.84/3.98  tff(c_20241, plain, (![A_2297]: (r1_tarski(k1_xboole_0, A_2297))), inference(superposition, [status(thm), theory('equality')], [c_19468, c_20221])).
% 10.84/3.98  tff(c_16291, plain, (![C_1617, B_1618, A_1619]: (r2_hidden(C_1617, B_1618) | ~r2_hidden(C_1617, A_1619) | ~r1_tarski(A_1619, B_1618))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.84/3.98  tff(c_16296, plain, (![A_3, B_4, B_1618]: (r2_hidden('#skF_1'(A_3, B_4), B_1618) | ~r1_tarski(A_3, B_1618) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_16291])).
% 10.84/3.98  tff(c_16310, plain, (![D_1623]: (r2_hidden(D_1623, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(D_1623, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_16202, c_12])).
% 10.84/3.98  tff(c_16933, plain, (![A_1658]: (r1_tarski(A_1658, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden('#skF_1'(A_1658, k2_zfmisc_1('#skF_6', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_16310, c_6])).
% 10.84/3.98  tff(c_16947, plain, (![A_3]: (~r1_tarski(A_3, k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(A_3, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_16296, c_16933])).
% 10.84/3.98  tff(c_17438, plain, (![A_1674, B_1675, C_1676]: (~r1_tarski(k2_zfmisc_1(A_1674, B_1675), k2_zfmisc_1(A_1674, C_1676)) | r1_tarski(B_1675, C_1676) | k1_xboole_0=A_1674)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.84/3.98  tff(c_17512, plain, (![A_1677, C_1678]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_1677, C_1678)) | r1_tarski(k1_xboole_0, C_1678) | k1_xboole_0=A_1677)), inference(superposition, [status(thm), theory('equality')], [c_32, c_17438])).
% 10.84/3.98  tff(c_17541, plain, (r1_tarski(k1_xboole_0, '#skF_7') | k1_xboole_0='#skF_6' | ~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16947, c_17512])).
% 10.84/3.98  tff(c_17578, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_17541])).
% 10.84/3.98  tff(c_20281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20241, c_17578])).
% 10.84/3.98  tff(c_20283, plain, (r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_17541])).
% 10.84/3.98  tff(c_17485, plain, (![A_16, C_1676]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_16, C_1676)) | r1_tarski(k1_xboole_0, C_1676) | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_32, c_17438])).
% 10.84/3.98  tff(c_20492, plain, (r1_tarski(k1_xboole_0, '#skF_5') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20283, c_17485])).
% 10.84/3.98  tff(c_20564, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_20492])).
% 10.84/3.98  tff(c_20587, plain, (![B_17]: (k2_zfmisc_1('#skF_4', B_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20564, c_20564, c_34])).
% 10.84/3.98  tff(c_20588, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20564, c_48])).
% 10.84/3.98  tff(c_20702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20587, c_20588])).
% 10.84/3.98  tff(c_20704, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_20492])).
% 10.84/3.98  tff(c_16160, plain, (r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 10.84/3.98  tff(c_16201, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_16160, c_16194])).
% 10.84/3.98  tff(c_20356, plain, (![A_2355, C_2356, B_2357, D_2358]: (k3_xboole_0(k2_zfmisc_1(A_2355, C_2356), k2_zfmisc_1(B_2357, D_2358))=k2_zfmisc_1(k3_xboole_0(A_2355, B_2357), k3_xboole_0(C_2356, D_2358)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.84/3.98  tff(c_20380, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20356, c_16202])).
% 10.84/3.98  tff(c_20464, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16201, c_20380])).
% 10.84/3.98  tff(c_20513, plain, (![B_19]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_19), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_19, k3_xboole_0('#skF_5', '#skF_7')) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20464, c_36])).
% 10.84/3.98  tff(c_22162, plain, (![B_2408]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_2408), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_2408, k3_xboole_0('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_20704, c_20513])).
% 10.84/3.98  tff(c_22176, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_16233, c_22162])).
% 10.84/3.98  tff(c_22182, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(resolution, [status(thm)], [c_22176, c_28])).
% 10.84/3.98  tff(c_20510, plain, (![C_20]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_20)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_20) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20464, c_36])).
% 10.84/3.98  tff(c_22045, plain, (![C_2404]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_2404)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_2404))), inference(negUnitSimplification, [status(thm)], [c_20704, c_20510])).
% 10.84/3.98  tff(c_22059, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_16233, c_22045])).
% 10.84/3.98  tff(c_22063, plain, (k3_xboole_0(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')=k3_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_22059, c_28])).
% 10.84/3.98  tff(c_22418, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))=k3_xboole_0('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_22063, c_2])).
% 10.84/3.98  tff(c_22430, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22182, c_22418])).
% 10.84/3.98  tff(c_22512, plain, (![A_2418, B_2419, B_2420]: (r2_hidden('#skF_1'(k3_xboole_0(A_2418, B_2419), B_2420), A_2418) | r1_tarski(k3_xboole_0(A_2418, B_2419), B_2420))), inference(resolution, [status(thm)], [c_8, c_16259])).
% 10.84/3.98  tff(c_22600, plain, (![A_2421, B_2422]: (r1_tarski(k3_xboole_0(A_2421, B_2422), A_2421))), inference(resolution, [status(thm)], [c_22512, c_6])).
% 10.84/3.98  tff(c_22674, plain, (![B_2424, A_2425]: (r1_tarski(k3_xboole_0(B_2424, A_2425), A_2425))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22600])).
% 10.84/3.98  tff(c_22684, plain, (r1_tarski('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_22430, c_22674])).
% 10.84/3.98  tff(c_22724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16159, c_22684])).
% 10.84/3.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.84/3.98  
% 10.84/3.98  Inference rules
% 10.84/3.98  ----------------------
% 10.84/3.98  #Ref     : 0
% 10.84/3.98  #Sup     : 5641
% 10.84/3.98  #Fact    : 0
% 10.84/3.98  #Define  : 0
% 10.84/3.98  #Split   : 30
% 10.84/3.98  #Chain   : 0
% 10.84/3.98  #Close   : 0
% 10.84/3.98  
% 10.84/3.98  Ordering : KBO
% 10.84/3.98  
% 10.84/3.98  Simplification rules
% 10.84/3.98  ----------------------
% 10.84/3.98  #Subsume      : 475
% 10.84/3.98  #Demod        : 4529
% 10.84/3.98  #Tautology    : 2299
% 10.84/3.98  #SimpNegUnit  : 94
% 10.84/3.98  #BackRed      : 273
% 10.84/3.98  
% 10.84/3.98  #Partial instantiations: 576
% 10.84/3.98  #Strategies tried      : 1
% 10.84/3.98  
% 10.84/3.98  Timing (in seconds)
% 10.84/3.98  ----------------------
% 10.84/3.98  Preprocessing        : 0.38
% 10.84/3.98  Parsing              : 0.19
% 10.84/3.98  CNF conversion       : 0.03
% 10.84/3.98  Main loop            : 2.73
% 10.84/3.98  Inferencing          : 0.71
% 10.84/3.98  Reduction            : 1.25
% 10.84/3.98  Demodulation         : 1.04
% 10.84/3.98  BG Simplification    : 0.10
% 10.84/3.98  Subsumption          : 0.48
% 10.84/3.98  Abstraction          : 0.14
% 10.84/3.98  MUC search           : 0.00
% 10.84/3.98  Cooper               : 0.00
% 10.84/3.98  Total                : 3.18
% 10.84/3.98  Index Insertion      : 0.00
% 10.84/3.98  Index Deletion       : 0.00
% 10.84/3.98  Index Matching       : 0.00
% 10.84/3.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
