%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 16.44s
% Output     : CNFRefutation 16.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 175 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :   97 ( 236 expanded)
%              Number of equality atoms :   63 ( 159 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k3_xboole_0('#skF_6','#skF_8') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,(
    k3_xboole_0('#skF_8','#skF_6') != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_74,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_235,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_244,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,k3_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_40])).

tff(c_274,plain,(
    ! [A_69,B_70] : k3_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_244])).

tff(c_78,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_165,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_174,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_165])).

tff(c_763,plain,(
    ! [A_103,B_104,C_105] : k4_xboole_0(k3_xboole_0(A_103,B_104),C_105) = k3_xboole_0(A_103,k4_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1391,plain,(
    ! [C_130] : k3_xboole_0('#skF_6',k4_xboole_0('#skF_7',C_130)) = k4_xboole_0('#skF_6',C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_763])).

tff(c_38,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1424,plain,(
    ! [C_130] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_7',C_130)) = k4_xboole_0('#skF_6',k4_xboole_0('#skF_6',C_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_38])).

tff(c_1448,plain,(
    ! [C_130] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_7',C_130)) = k3_xboole_0('#skF_6',C_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1424])).

tff(c_4650,plain,(
    ! [C_5567] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_7',C_5567)) = k3_xboole_0('#skF_6',C_5567) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1424])).

tff(c_4692,plain,(
    ! [B_21] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_7',B_21)) = k3_xboole_0('#skF_6',k3_xboole_0('#skF_7',B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4650])).

tff(c_4704,plain,(
    ! [B_21] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_7',B_21)) = k3_xboole_0('#skF_6',B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_4692])).

tff(c_783,plain,(
    ! [A_103,B_104,C_105] : k4_xboole_0(k3_xboole_0(A_103,B_104),k3_xboole_0(A_103,k4_xboole_0(B_104,C_105))) = k3_xboole_0(k3_xboole_0(A_103,B_104),C_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_40])).

tff(c_1264,plain,(
    ! [A_127,B_128,C_129] : k4_xboole_0(k3_xboole_0(A_127,B_128),k3_xboole_0(A_127,C_129)) = k3_xboole_0(A_127,k4_xboole_0(B_128,C_129)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1292,plain,(
    ! [A_127,B_128,C_129] : k4_xboole_0(k3_xboole_0(A_127,B_128),k3_xboole_0(A_127,k4_xboole_0(B_128,C_129))) = k3_xboole_0(k3_xboole_0(A_127,B_128),k3_xboole_0(A_127,C_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_40])).

tff(c_38255,plain,(
    ! [A_29460,B_29461,C_29462] : k3_xboole_0(k3_xboole_0(A_29460,B_29461),k3_xboole_0(A_29460,C_29462)) = k3_xboole_0(k3_xboole_0(A_29460,B_29461),C_29462) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1292])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42933,plain,(
    ! [A_30528,C_30529] : k3_xboole_0(k3_xboole_0(A_30528,C_30529),C_30529) = k3_xboole_0(A_30528,C_30529) ),
    inference(superposition,[status(thm),theory(equality)],[c_38255,c_28])).

tff(c_44522,plain,(
    ! [A_30758,B_30759] : k3_xboole_0(k3_xboole_0(A_30758,B_30759),A_30758) = k3_xboole_0(B_30759,A_30758) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_42933])).

tff(c_46753,plain,(
    ! [A_31143,B_31144] : k3_xboole_0(A_31143,k3_xboole_0(A_31143,B_31144)) = k3_xboole_0(B_31144,A_31143) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44522])).

tff(c_47251,plain,(
    ! [B_21] : k3_xboole_0(k3_xboole_0('#skF_7',B_21),'#skF_6') = k3_xboole_0('#skF_6',k3_xboole_0('#skF_6',B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4704,c_46753])).

tff(c_49554,plain,(
    ! [B_31753] : k3_xboole_0(k3_xboole_0('#skF_7',B_31753),'#skF_6') = k3_xboole_0('#skF_6',B_31753) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_47251])).

tff(c_49831,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),'#skF_6') = k3_xboole_0('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_49554])).

tff(c_49903,plain,(
    k3_xboole_0(k1_tarski('#skF_9'),'#skF_6') = k3_xboole_0('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_49831])).

tff(c_2668,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_2'(A_155,B_156,C_157),A_155)
      | r2_hidden('#skF_3'(A_155,B_156,C_157),C_157)
      | k4_xboole_0(A_155,B_156) = C_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9941,plain,(
    ! [A_9909,C_9910] :
      ( r2_hidden('#skF_3'(A_9909,A_9909,C_9910),C_9910)
      | k4_xboole_0(A_9909,A_9909) = C_9910 ) ),
    inference(resolution,[status(thm)],[c_2668,c_24])).

tff(c_97,plain,(
    ! [A_47] : k2_tarski(A_47,A_47) = k1_tarski(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,(
    ! [D_35,B_31] : r2_hidden(D_35,k2_tarski(D_35,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_103,plain,(
    ! [A_47] : r2_hidden(A_47,k1_tarski(A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_50])).

tff(c_1483,plain,(
    ! [C_131] : k4_xboole_0(k1_tarski('#skF_9'),k3_xboole_0('#skF_7',C_131)) = k3_xboole_0('#skF_7',k4_xboole_0('#skF_8',C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1264])).

tff(c_1559,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k3_xboole_0('#skF_7',k4_xboole_0('#skF_8','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1483])).

tff(c_70,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),B_40) = k1_xboole_0
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1727,plain,
    ( k3_xboole_0('#skF_7',k4_xboole_0('#skF_8','#skF_8')) = k1_xboole_0
    | ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_70])).

tff(c_1754,plain,(
    k3_xboole_0('#skF_7',k4_xboole_0('#skF_8','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1727])).

tff(c_1761,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_1559])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1874,plain,(
    ! [D_13] :
      ( r2_hidden(D_13,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1761,c_14])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2862,plain,(
    ! [D_158] :
      ( ~ r2_hidden(D_158,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_158,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1761,c_12])).

tff(c_2897,plain,(
    ! [D_13] : ~ r2_hidden(D_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1874,c_2862])).

tff(c_10054,plain,(
    ! [A_9961] : k4_xboole_0(A_9961,A_9961) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9941,c_2897])).

tff(c_10164,plain,(
    ! [A_9961] : k4_xboole_0(A_9961,k1_xboole_0) = k3_xboole_0(A_9961,A_9961) ),
    inference(superposition,[status(thm),theory(equality)],[c_10054,c_40])).

tff(c_10221,plain,(
    ! [A_9961] : k4_xboole_0(A_9961,k1_xboole_0) = A_9961 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10164])).

tff(c_335,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(k1_tarski(A_71),B_72) = k1_xboole_0
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_348,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(k1_tarski(A_71),k1_xboole_0) = k3_xboole_0(k1_tarski(A_71),B_72)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_40])).

tff(c_13026,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(k1_tarski(A_71),B_72) = k1_tarski(A_71)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10221,c_348])).

tff(c_50006,plain,
    ( k3_xboole_0('#skF_8','#skF_6') = k1_tarski('#skF_9')
    | ~ r2_hidden('#skF_9','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_49903,c_13026])).

tff(c_50172,plain,(
    k3_xboole_0('#skF_8','#skF_6') = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_50006])).

tff(c_50174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_50172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.44/7.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.44/7.79  
% 16.44/7.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.44/7.79  %$ r2_hidden > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 16.44/7.79  
% 16.44/7.79  %Foreground sorts:
% 16.44/7.79  
% 16.44/7.79  
% 16.44/7.79  %Background operators:
% 16.44/7.79  
% 16.44/7.79  
% 16.44/7.79  %Foreground operators:
% 16.44/7.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.44/7.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.44/7.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.44/7.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.44/7.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.44/7.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 16.44/7.79  tff('#skF_7', type, '#skF_7': $i).
% 16.44/7.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.44/7.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.44/7.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.44/7.79  tff('#skF_6', type, '#skF_6': $i).
% 16.44/7.79  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 16.44/7.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.44/7.79  tff('#skF_9', type, '#skF_9': $i).
% 16.44/7.79  tff('#skF_8', type, '#skF_8': $i).
% 16.44/7.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.44/7.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.44/7.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.44/7.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.44/7.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.44/7.79  
% 16.44/7.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.44/7.81  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 16.44/7.81  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.44/7.81  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 16.44/7.81  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 16.44/7.81  tff(f_62, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 16.44/7.81  tff(f_64, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 16.44/7.81  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 16.44/7.81  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.44/7.81  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 16.44/7.81  tff(f_73, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 16.44/7.81  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 16.44/7.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.44/7.81  tff(c_72, plain, (k3_xboole_0('#skF_6', '#skF_8')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.44/7.81  tff(c_80, plain, (k3_xboole_0('#skF_8', '#skF_6')!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_72])).
% 16.44/7.81  tff(c_74, plain, (r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.44/7.81  tff(c_76, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.44/7.81  tff(c_40, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.44/7.81  tff(c_235, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.44/7.81  tff(c_244, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, k3_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_40])).
% 16.44/7.81  tff(c_274, plain, (![A_69, B_70]: (k3_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_244])).
% 16.44/7.81  tff(c_78, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.44/7.81  tff(c_165, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.44/7.81  tff(c_174, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_78, c_165])).
% 16.44/7.81  tff(c_763, plain, (![A_103, B_104, C_105]: (k4_xboole_0(k3_xboole_0(A_103, B_104), C_105)=k3_xboole_0(A_103, k4_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.44/7.81  tff(c_1391, plain, (![C_130]: (k3_xboole_0('#skF_6', k4_xboole_0('#skF_7', C_130))=k4_xboole_0('#skF_6', C_130))), inference(superposition, [status(thm), theory('equality')], [c_174, c_763])).
% 16.44/7.81  tff(c_38, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.44/7.81  tff(c_1424, plain, (![C_130]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_7', C_130))=k4_xboole_0('#skF_6', k4_xboole_0('#skF_6', C_130)))), inference(superposition, [status(thm), theory('equality')], [c_1391, c_38])).
% 16.44/7.81  tff(c_1448, plain, (![C_130]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_7', C_130))=k3_xboole_0('#skF_6', C_130))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1424])).
% 16.44/7.81  tff(c_4650, plain, (![C_5567]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_7', C_5567))=k3_xboole_0('#skF_6', C_5567))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1424])).
% 16.44/7.81  tff(c_4692, plain, (![B_21]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_7', B_21))=k3_xboole_0('#skF_6', k3_xboole_0('#skF_7', B_21)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4650])).
% 16.44/7.81  tff(c_4704, plain, (![B_21]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_7', B_21))=k3_xboole_0('#skF_6', B_21))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_4692])).
% 16.44/7.81  tff(c_783, plain, (![A_103, B_104, C_105]: (k4_xboole_0(k3_xboole_0(A_103, B_104), k3_xboole_0(A_103, k4_xboole_0(B_104, C_105)))=k3_xboole_0(k3_xboole_0(A_103, B_104), C_105))), inference(superposition, [status(thm), theory('equality')], [c_763, c_40])).
% 16.44/7.81  tff(c_1264, plain, (![A_127, B_128, C_129]: (k4_xboole_0(k3_xboole_0(A_127, B_128), k3_xboole_0(A_127, C_129))=k3_xboole_0(A_127, k4_xboole_0(B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.44/7.81  tff(c_1292, plain, (![A_127, B_128, C_129]: (k4_xboole_0(k3_xboole_0(A_127, B_128), k3_xboole_0(A_127, k4_xboole_0(B_128, C_129)))=k3_xboole_0(k3_xboole_0(A_127, B_128), k3_xboole_0(A_127, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_40])).
% 16.44/7.81  tff(c_38255, plain, (![A_29460, B_29461, C_29462]: (k3_xboole_0(k3_xboole_0(A_29460, B_29461), k3_xboole_0(A_29460, C_29462))=k3_xboole_0(k3_xboole_0(A_29460, B_29461), C_29462))), inference(demodulation, [status(thm), theory('equality')], [c_783, c_1292])).
% 16.44/7.81  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.44/7.81  tff(c_42933, plain, (![A_30528, C_30529]: (k3_xboole_0(k3_xboole_0(A_30528, C_30529), C_30529)=k3_xboole_0(A_30528, C_30529))), inference(superposition, [status(thm), theory('equality')], [c_38255, c_28])).
% 16.44/7.81  tff(c_44522, plain, (![A_30758, B_30759]: (k3_xboole_0(k3_xboole_0(A_30758, B_30759), A_30758)=k3_xboole_0(B_30759, A_30758))), inference(superposition, [status(thm), theory('equality')], [c_2, c_42933])).
% 16.44/7.81  tff(c_46753, plain, (![A_31143, B_31144]: (k3_xboole_0(A_31143, k3_xboole_0(A_31143, B_31144))=k3_xboole_0(B_31144, A_31143))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44522])).
% 16.44/7.81  tff(c_47251, plain, (![B_21]: (k3_xboole_0(k3_xboole_0('#skF_7', B_21), '#skF_6')=k3_xboole_0('#skF_6', k3_xboole_0('#skF_6', B_21)))), inference(superposition, [status(thm), theory('equality')], [c_4704, c_46753])).
% 16.44/7.81  tff(c_49554, plain, (![B_31753]: (k3_xboole_0(k3_xboole_0('#skF_7', B_31753), '#skF_6')=k3_xboole_0('#skF_6', B_31753))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_47251])).
% 16.44/7.81  tff(c_49831, plain, (k3_xboole_0(k1_tarski('#skF_9'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_76, c_49554])).
% 16.44/7.81  tff(c_49903, plain, (k3_xboole_0(k1_tarski('#skF_9'), '#skF_6')=k3_xboole_0('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_49831])).
% 16.44/7.81  tff(c_2668, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_2'(A_155, B_156, C_157), A_155) | r2_hidden('#skF_3'(A_155, B_156, C_157), C_157) | k4_xboole_0(A_155, B_156)=C_157)), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.44/7.81  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.44/7.81  tff(c_9941, plain, (![A_9909, C_9910]: (r2_hidden('#skF_3'(A_9909, A_9909, C_9910), C_9910) | k4_xboole_0(A_9909, A_9909)=C_9910)), inference(resolution, [status(thm)], [c_2668, c_24])).
% 16.44/7.81  tff(c_97, plain, (![A_47]: (k2_tarski(A_47, A_47)=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.44/7.81  tff(c_50, plain, (![D_35, B_31]: (r2_hidden(D_35, k2_tarski(D_35, B_31)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.44/7.81  tff(c_103, plain, (![A_47]: (r2_hidden(A_47, k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_50])).
% 16.44/7.81  tff(c_1483, plain, (![C_131]: (k4_xboole_0(k1_tarski('#skF_9'), k3_xboole_0('#skF_7', C_131))=k3_xboole_0('#skF_7', k4_xboole_0('#skF_8', C_131)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1264])).
% 16.44/7.81  tff(c_1559, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k3_xboole_0('#skF_7', k4_xboole_0('#skF_8', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1483])).
% 16.44/7.81  tff(c_70, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), B_40)=k1_xboole_0 | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.44/7.81  tff(c_1727, plain, (k3_xboole_0('#skF_7', k4_xboole_0('#skF_8', '#skF_8'))=k1_xboole_0 | ~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_70])).
% 16.44/7.81  tff(c_1754, plain, (k3_xboole_0('#skF_7', k4_xboole_0('#skF_8', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1727])).
% 16.44/7.81  tff(c_1761, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_1559])).
% 16.44/7.81  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.44/7.81  tff(c_1874, plain, (![D_13]: (r2_hidden(D_13, k1_tarski('#skF_9')) | ~r2_hidden(D_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1761, c_14])).
% 16.44/7.81  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.44/7.81  tff(c_2862, plain, (![D_158]: (~r2_hidden(D_158, k1_tarski('#skF_9')) | ~r2_hidden(D_158, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1761, c_12])).
% 16.44/7.81  tff(c_2897, plain, (![D_13]: (~r2_hidden(D_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_1874, c_2862])).
% 16.44/7.81  tff(c_10054, plain, (![A_9961]: (k4_xboole_0(A_9961, A_9961)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9941, c_2897])).
% 16.44/7.81  tff(c_10164, plain, (![A_9961]: (k4_xboole_0(A_9961, k1_xboole_0)=k3_xboole_0(A_9961, A_9961))), inference(superposition, [status(thm), theory('equality')], [c_10054, c_40])).
% 16.44/7.81  tff(c_10221, plain, (![A_9961]: (k4_xboole_0(A_9961, k1_xboole_0)=A_9961)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10164])).
% 16.44/7.81  tff(c_335, plain, (![A_71, B_72]: (k4_xboole_0(k1_tarski(A_71), B_72)=k1_xboole_0 | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.44/7.81  tff(c_348, plain, (![A_71, B_72]: (k4_xboole_0(k1_tarski(A_71), k1_xboole_0)=k3_xboole_0(k1_tarski(A_71), B_72) | ~r2_hidden(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_335, c_40])).
% 16.44/7.81  tff(c_13026, plain, (![A_71, B_72]: (k3_xboole_0(k1_tarski(A_71), B_72)=k1_tarski(A_71) | ~r2_hidden(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_10221, c_348])).
% 16.44/7.81  tff(c_50006, plain, (k3_xboole_0('#skF_8', '#skF_6')=k1_tarski('#skF_9') | ~r2_hidden('#skF_9', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_49903, c_13026])).
% 16.44/7.81  tff(c_50172, plain, (k3_xboole_0('#skF_8', '#skF_6')=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_50006])).
% 16.44/7.81  tff(c_50174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_50172])).
% 16.44/7.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.44/7.81  
% 16.44/7.81  Inference rules
% 16.44/7.81  ----------------------
% 16.44/7.81  #Ref     : 0
% 16.44/7.81  #Sup     : 11373
% 16.44/7.81  #Fact    : 10
% 16.44/7.81  #Define  : 0
% 16.44/7.81  #Split   : 5
% 16.44/7.81  #Chain   : 0
% 16.44/7.81  #Close   : 0
% 16.44/7.81  
% 16.44/7.81  Ordering : KBO
% 16.44/7.81  
% 16.44/7.81  Simplification rules
% 16.44/7.81  ----------------------
% 16.44/7.81  #Subsume      : 2920
% 16.44/7.81  #Demod        : 11041
% 16.44/7.81  #Tautology    : 4581
% 16.44/7.81  #SimpNegUnit  : 343
% 16.44/7.81  #BackRed      : 30
% 16.44/7.81  
% 16.44/7.81  #Partial instantiations: 18750
% 16.44/7.81  #Strategies tried      : 1
% 16.44/7.81  
% 16.44/7.81  Timing (in seconds)
% 16.44/7.81  ----------------------
% 16.44/7.81  Preprocessing        : 0.33
% 16.44/7.81  Parsing              : 0.17
% 16.44/7.81  CNF conversion       : 0.03
% 16.44/7.81  Main loop            : 6.70
% 16.44/7.81  Inferencing          : 1.36
% 16.44/7.81  Reduction            : 3.61
% 16.44/7.81  Demodulation         : 3.03
% 16.44/7.81  BG Simplification    : 0.12
% 16.44/7.81  Subsumption          : 1.29
% 16.44/7.81  Abstraction          : 0.18
% 16.44/7.81  MUC search           : 0.00
% 16.44/7.81  Cooper               : 0.00
% 16.44/7.81  Total                : 7.07
% 16.44/7.81  Index Insertion      : 0.00
% 16.44/7.81  Index Deletion       : 0.00
% 16.44/7.81  Index Matching       : 0.00
% 16.44/7.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
