%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:35 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 317 expanded)
%              Number of leaves         :   21 ( 112 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 600 expanded)
%              Number of equality atoms :   27 ( 114 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_40])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_104,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_914,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_16,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_935,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_939,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_935,c_4])).

tff(c_951,plain,(
    ! [A_95,B_96,C_97] : k2_xboole_0(k3_xboole_0(A_95,B_96),k3_xboole_0(A_95,C_97)) = k3_xboole_0(A_95,k2_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_976,plain,(
    ! [C_97] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_97)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_951])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_24])).

tff(c_944,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_950,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_944])).

tff(c_1559,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_950])).

tff(c_1563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_914,c_1559])).

tff(c_1564,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1737,plain,(
    ! [A_139,C_140,B_141,D_142] :
      ( r1_xboole_0(A_139,C_140)
      | ~ r1_xboole_0(B_141,D_142)
      | ~ r1_tarski(C_140,D_142)
      | ~ r1_tarski(A_139,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1922,plain,(
    ! [A_159,C_160] :
      ( r1_xboole_0(A_159,C_160)
      | ~ r1_tarski(C_160,k2_xboole_0('#skF_3','#skF_2'))
      | ~ r1_tarski(A_159,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1564,c_1737])).

tff(c_1943,plain,(
    ! [A_162] :
      ( r1_xboole_0(A_162,'#skF_3')
      | ~ r1_tarski(A_162,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_1922])).

tff(c_45,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_21,B_20] : r1_tarski(A_21,k2_xboole_0(B_20,A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_14])).

tff(c_118,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_122,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_109,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_161,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k3_xboole_0(A_34,B_35),k3_xboole_0(A_34,C_36)) = k3_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_296,plain,(
    ! [A_45,C_46,B_47] : k2_xboole_0(k3_xboole_0(A_45,C_46),k3_xboole_0(A_45,B_47)) = k3_xboole_0(A_45,k2_xboole_0(B_47,C_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_336,plain,(
    ! [B_47] : k3_xboole_0('#skF_4',k2_xboole_0(B_47,'#skF_5')) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_296])).

tff(c_128,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_132,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_406,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_132])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_122,c_406])).

tff(c_411,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_634,plain,(
    ! [A_65,C_66,B_67,D_68] :
      ( r1_xboole_0(A_65,C_66)
      | ~ r1_xboole_0(B_67,D_68)
      | ~ r1_tarski(C_66,D_68)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_705,plain,(
    ! [A_75,C_76] :
      ( r1_xboole_0(A_75,C_76)
      | ~ r1_tarski(C_76,k2_xboole_0('#skF_3','#skF_2'))
      | ~ r1_tarski(A_75,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_411,c_634])).

tff(c_718,plain,(
    ! [A_77] :
      ( r1_xboole_0(A_77,'#skF_2')
      | ~ r1_tarski(A_77,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_705])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_723,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_718,c_105])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_723])).

tff(c_732,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_799,plain,(
    ! [A_81,C_82,B_83,D_84] :
      ( r1_xboole_0(A_81,C_82)
      | ~ r1_xboole_0(B_83,D_84)
      | ~ r1_tarski(C_82,D_84)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_882,plain,(
    ! [A_92,C_93] :
      ( r1_xboole_0(A_92,C_93)
      | ~ r1_tarski(C_93,k2_xboole_0('#skF_3','#skF_2'))
      | ~ r1_tarski(A_92,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_732,c_799])).

tff(c_895,plain,(
    ! [A_94] :
      ( r1_xboole_0(A_94,'#skF_2')
      | ~ r1_tarski(A_94,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_882])).

tff(c_900,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_895,c_105])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_900])).

tff(c_910,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_920,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_18])).

tff(c_921,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_1948,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1943,c_921])).

tff(c_1956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_1948])).

tff(c_1957,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_1978,plain,(
    ! [A_163,C_164,B_165,D_166] :
      ( r1_xboole_0(A_163,C_164)
      | ~ r1_xboole_0(B_165,D_166)
      | ~ r1_tarski(C_164,D_166)
      | ~ r1_tarski(A_163,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2187,plain,(
    ! [A_181,C_182] :
      ( r1_xboole_0(A_181,C_182)
      | ~ r1_tarski(C_182,k2_xboole_0('#skF_3','#skF_2'))
      | ~ r1_tarski(A_181,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1957,c_1978])).

tff(c_2208,plain,(
    ! [A_184] :
      ( r1_xboole_0(A_184,'#skF_3')
      | ~ r1_tarski(A_184,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_2187])).

tff(c_2213,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2208,c_921])).

tff(c_2221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_2213])).

tff(c_2222,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_2227,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2222,c_4])).

tff(c_2300,plain,(
    ! [A_193,B_194,C_195] : k2_xboole_0(k3_xboole_0(A_193,B_194),k3_xboole_0(A_193,C_195)) = k3_xboole_0(A_193,k2_xboole_0(B_194,C_195)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2337,plain,(
    ! [C_195] : k3_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_195)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4',C_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2227,c_2300])).

tff(c_2250,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2254,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2250])).

tff(c_3275,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_2254])).

tff(c_3279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_914,c_3275])).

tff(c_3281,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2223,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_27,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_3291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3281,c_910,c_2223,c_27])).

tff(c_3292,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3492,plain,(
    ! [A_252,C_253,B_254,D_255] :
      ( r1_xboole_0(A_252,C_253)
      | ~ r1_xboole_0(B_254,D_255)
      | ~ r1_tarski(C_253,D_255)
      | ~ r1_tarski(A_252,B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3609,plain,(
    ! [A_265,C_266] :
      ( r1_xboole_0(A_265,C_266)
      | ~ r1_tarski(C_266,k2_xboole_0('#skF_3','#skF_2'))
      | ~ r1_tarski(A_265,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3292,c_3492])).

tff(c_3630,plain,(
    ! [A_268] :
      ( r1_xboole_0(A_268,'#skF_3')
      | ~ r1_tarski(A_268,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_3609])).

tff(c_3416,plain,(
    ! [A_244,C_245,B_246,D_247] :
      ( r1_xboole_0(A_244,C_245)
      | ~ r1_xboole_0(B_246,D_247)
      | ~ r1_tarski(C_245,D_247)
      | ~ r1_tarski(A_244,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3441,plain,(
    ! [A_249,C_250] :
      ( r1_xboole_0(A_249,C_250)
      | ~ r1_tarski(C_250,k2_xboole_0('#skF_3','#skF_2'))
      | ~ r1_tarski(A_249,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3292,c_3416])).

tff(c_3454,plain,(
    ! [A_251] :
      ( r1_xboole_0(A_251,'#skF_2')
      | ~ r1_tarski(A_251,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_3441])).

tff(c_3293,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3302,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3293,c_22])).

tff(c_3303,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3302])).

tff(c_3459,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3454,c_3303])).

tff(c_3467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_3459])).

tff(c_3468,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3302])).

tff(c_3635,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3630,c_3468])).

tff(c_3643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_3635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.90  
% 4.50/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.90  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.50/1.90  
% 4.50/1.90  %Foreground sorts:
% 4.50/1.90  
% 4.50/1.90  
% 4.50/1.90  %Background operators:
% 4.50/1.90  
% 4.50/1.90  
% 4.50/1.90  %Foreground operators:
% 4.50/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.50/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.50/1.90  
% 4.86/1.92  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.86/1.92  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.86/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.86/1.92  tff(f_62, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.86/1.92  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.86/1.92  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 4.86/1.92  tff(f_43, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 4.86/1.92  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.86/1.92  tff(c_40, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.86/1.92  tff(c_43, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_40])).
% 4.86/1.92  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.86/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.92  tff(c_20, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.86/1.92  tff(c_28, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 4.86/1.92  tff(c_104, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 4.86/1.92  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.92  tff(c_914, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_4])).
% 4.86/1.92  tff(c_16, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.86/1.92  tff(c_29, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 4.86/1.92  tff(c_935, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_29])).
% 4.86/1.92  tff(c_939, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_935, c_4])).
% 4.86/1.92  tff(c_951, plain, (![A_95, B_96, C_97]: (k2_xboole_0(k3_xboole_0(A_95, B_96), k3_xboole_0(A_95, C_97))=k3_xboole_0(A_95, k2_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.92  tff(c_976, plain, (![C_97]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_97))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_97)))), inference(superposition, [status(thm), theory('equality')], [c_939, c_951])).
% 4.86/1.92  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.92  tff(c_24, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.86/1.92  tff(c_30, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_24])).
% 4.86/1.92  tff(c_944, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_30])).
% 4.86/1.92  tff(c_950, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_944])).
% 4.86/1.92  tff(c_1559, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_976, c_950])).
% 4.86/1.92  tff(c_1563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_914, c_1559])).
% 4.86/1.92  tff(c_1564, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 4.86/1.92  tff(c_1737, plain, (![A_139, C_140, B_141, D_142]: (r1_xboole_0(A_139, C_140) | ~r1_xboole_0(B_141, D_142) | ~r1_tarski(C_140, D_142) | ~r1_tarski(A_139, B_141))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.92  tff(c_1922, plain, (![A_159, C_160]: (r1_xboole_0(A_159, C_160) | ~r1_tarski(C_160, k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(A_159, '#skF_1'))), inference(resolution, [status(thm)], [c_1564, c_1737])).
% 4.86/1.92  tff(c_1943, plain, (![A_162]: (r1_xboole_0(A_162, '#skF_3') | ~r1_tarski(A_162, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_1922])).
% 4.86/1.92  tff(c_45, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.92  tff(c_60, plain, (![A_21, B_20]: (r1_tarski(A_21, k2_xboole_0(B_20, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_14])).
% 4.86/1.92  tff(c_118, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_29])).
% 4.86/1.92  tff(c_122, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_118, c_4])).
% 4.86/1.92  tff(c_109, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_4])).
% 4.86/1.92  tff(c_161, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k3_xboole_0(A_34, C_36))=k3_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.92  tff(c_296, plain, (![A_45, C_46, B_47]: (k2_xboole_0(k3_xboole_0(A_45, C_46), k3_xboole_0(A_45, B_47))=k3_xboole_0(A_45, k2_xboole_0(B_47, C_46)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_161])).
% 4.86/1.92  tff(c_336, plain, (![B_47]: (k3_xboole_0('#skF_4', k2_xboole_0(B_47, '#skF_5'))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', B_47)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_296])).
% 4.86/1.92  tff(c_128, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_30])).
% 4.86/1.92  tff(c_132, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.86/1.92  tff(c_406, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_336, c_132])).
% 4.86/1.92  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_122, c_406])).
% 4.86/1.92  tff(c_411, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 4.86/1.92  tff(c_634, plain, (![A_65, C_66, B_67, D_68]: (r1_xboole_0(A_65, C_66) | ~r1_xboole_0(B_67, D_68) | ~r1_tarski(C_66, D_68) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.92  tff(c_705, plain, (![A_75, C_76]: (r1_xboole_0(A_75, C_76) | ~r1_tarski(C_76, k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(A_75, '#skF_1'))), inference(resolution, [status(thm)], [c_411, c_634])).
% 4.86/1.92  tff(c_718, plain, (![A_77]: (r1_xboole_0(A_77, '#skF_2') | ~r1_tarski(A_77, '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_705])).
% 4.86/1.92  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.86/1.92  tff(c_105, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 4.86/1.92  tff(c_723, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_718, c_105])).
% 4.86/1.92  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_723])).
% 4.86/1.92  tff(c_732, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_29])).
% 4.86/1.92  tff(c_799, plain, (![A_81, C_82, B_83, D_84]: (r1_xboole_0(A_81, C_82) | ~r1_xboole_0(B_83, D_84) | ~r1_tarski(C_82, D_84) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.92  tff(c_882, plain, (![A_92, C_93]: (r1_xboole_0(A_92, C_93) | ~r1_tarski(C_93, k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(A_92, '#skF_1'))), inference(resolution, [status(thm)], [c_732, c_799])).
% 4.86/1.92  tff(c_895, plain, (![A_94]: (r1_xboole_0(A_94, '#skF_2') | ~r1_tarski(A_94, '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_882])).
% 4.86/1.92  tff(c_900, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_895, c_105])).
% 4.86/1.92  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_900])).
% 4.86/1.92  tff(c_910, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 4.86/1.92  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.86/1.92  tff(c_920, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_910, c_18])).
% 4.86/1.92  tff(c_921, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_920])).
% 4.86/1.92  tff(c_1948, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1943, c_921])).
% 4.86/1.92  tff(c_1956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_1948])).
% 4.86/1.92  tff(c_1957, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_29])).
% 4.86/1.92  tff(c_1978, plain, (![A_163, C_164, B_165, D_166]: (r1_xboole_0(A_163, C_164) | ~r1_xboole_0(B_165, D_166) | ~r1_tarski(C_164, D_166) | ~r1_tarski(A_163, B_165))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.92  tff(c_2187, plain, (![A_181, C_182]: (r1_xboole_0(A_181, C_182) | ~r1_tarski(C_182, k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(A_181, '#skF_1'))), inference(resolution, [status(thm)], [c_1957, c_1978])).
% 4.86/1.92  tff(c_2208, plain, (![A_184]: (r1_xboole_0(A_184, '#skF_3') | ~r1_tarski(A_184, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_2187])).
% 4.86/1.92  tff(c_2213, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2208, c_921])).
% 4.86/1.92  tff(c_2221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_2213])).
% 4.86/1.92  tff(c_2222, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_920])).
% 4.86/1.92  tff(c_2227, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2222, c_4])).
% 4.86/1.92  tff(c_2300, plain, (![A_193, B_194, C_195]: (k2_xboole_0(k3_xboole_0(A_193, B_194), k3_xboole_0(A_193, C_195))=k3_xboole_0(A_193, k2_xboole_0(B_194, C_195)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.92  tff(c_2337, plain, (![C_195]: (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_195))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', C_195)))), inference(superposition, [status(thm), theory('equality')], [c_2227, c_2300])).
% 4.86/1.92  tff(c_2250, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_30])).
% 4.86/1.92  tff(c_2254, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2250])).
% 4.86/1.92  tff(c_3275, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_2254])).
% 4.86/1.92  tff(c_3279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_914, c_3275])).
% 4.86/1.92  tff(c_3281, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_30])).
% 4.86/1.92  tff(c_2223, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_920])).
% 4.86/1.92  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.86/1.92  tff(c_27, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 4.86/1.92  tff(c_3291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3281, c_910, c_2223, c_27])).
% 4.86/1.92  tff(c_3292, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 4.86/1.92  tff(c_3492, plain, (![A_252, C_253, B_254, D_255]: (r1_xboole_0(A_252, C_253) | ~r1_xboole_0(B_254, D_255) | ~r1_tarski(C_253, D_255) | ~r1_tarski(A_252, B_254))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.92  tff(c_3609, plain, (![A_265, C_266]: (r1_xboole_0(A_265, C_266) | ~r1_tarski(C_266, k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(A_265, '#skF_1'))), inference(resolution, [status(thm)], [c_3292, c_3492])).
% 4.86/1.92  tff(c_3630, plain, (![A_268]: (r1_xboole_0(A_268, '#skF_3') | ~r1_tarski(A_268, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_3609])).
% 4.86/1.92  tff(c_3416, plain, (![A_244, C_245, B_246, D_247]: (r1_xboole_0(A_244, C_245) | ~r1_xboole_0(B_246, D_247) | ~r1_tarski(C_245, D_247) | ~r1_tarski(A_244, B_246))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.92  tff(c_3441, plain, (![A_249, C_250]: (r1_xboole_0(A_249, C_250) | ~r1_tarski(C_250, k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(A_249, '#skF_1'))), inference(resolution, [status(thm)], [c_3292, c_3416])).
% 4.86/1.92  tff(c_3454, plain, (![A_251]: (r1_xboole_0(A_251, '#skF_2') | ~r1_tarski(A_251, '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_3441])).
% 4.86/1.92  tff(c_3293, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 4.86/1.92  tff(c_3302, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_xboole_0('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3293, c_22])).
% 4.86/1.92  tff(c_3303, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_3302])).
% 4.86/1.92  tff(c_3459, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3454, c_3303])).
% 4.86/1.92  tff(c_3467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_3459])).
% 4.86/1.92  tff(c_3468, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_3302])).
% 4.86/1.92  tff(c_3635, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3630, c_3468])).
% 4.86/1.92  tff(c_3643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_3635])).
% 4.86/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.92  
% 4.86/1.92  Inference rules
% 4.86/1.92  ----------------------
% 4.86/1.92  #Ref     : 0
% 4.86/1.92  #Sup     : 885
% 4.86/1.92  #Fact    : 0
% 4.86/1.92  #Define  : 0
% 4.86/1.92  #Split   : 20
% 4.86/1.92  #Chain   : 0
% 4.86/1.92  #Close   : 0
% 4.86/1.92  
% 4.86/1.92  Ordering : KBO
% 4.86/1.92  
% 4.86/1.92  Simplification rules
% 4.86/1.92  ----------------------
% 4.86/1.92  #Subsume      : 23
% 4.86/1.92  #Demod        : 482
% 4.86/1.92  #Tautology    : 408
% 4.86/1.92  #SimpNegUnit  : 2
% 4.86/1.92  #BackRed      : 12
% 4.86/1.92  
% 4.86/1.92  #Partial instantiations: 0
% 4.86/1.92  #Strategies tried      : 1
% 4.86/1.92  
% 4.86/1.92  Timing (in seconds)
% 4.86/1.92  ----------------------
% 4.86/1.92  Preprocessing        : 0.29
% 4.86/1.92  Parsing              : 0.16
% 4.86/1.92  CNF conversion       : 0.02
% 4.86/1.92  Main loop            : 0.85
% 4.86/1.92  Inferencing          : 0.28
% 4.86/1.92  Reduction            : 0.34
% 4.86/1.92  Demodulation         : 0.27
% 4.86/1.92  BG Simplification    : 0.03
% 4.86/1.92  Subsumption          : 0.14
% 4.86/1.92  Abstraction          : 0.03
% 4.86/1.92  MUC search           : 0.00
% 4.86/1.92  Cooper               : 0.00
% 4.86/1.92  Total                : 1.18
% 4.86/1.92  Index Insertion      : 0.00
% 4.86/1.92  Index Deletion       : 0.00
% 4.86/1.92  Index Matching       : 0.00
% 4.86/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
