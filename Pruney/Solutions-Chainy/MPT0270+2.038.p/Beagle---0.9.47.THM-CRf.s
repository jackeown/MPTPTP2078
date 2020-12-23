%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.91s
% Verified   : 
% Statistics : Number of formulae       :  160 (1035 expanded)
%              Number of leaves         :   29 ( 344 expanded)
%              Depth                    :   18
%              Number of atoms          :  219 (1391 expanded)
%              Number of equality atoms :   94 ( 915 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_38,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,k1_tarski(B_30)) = A_29
      | r2_hidden(B_30,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,A_44)
      | ~ r2_hidden(D_43,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3951,plain,(
    ! [A_208,B_209] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_208,B_209)),A_208)
      | k3_xboole_0(A_208,B_209) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_144])).

tff(c_4028,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_3'(k3_xboole_0(B_2,A_1)),A_1)
      | k3_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3951])).

tff(c_171,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_192,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k3_xboole_0(A_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_171])).

tff(c_206,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_38])).

tff(c_189,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_171])).

tff(c_186,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,A_29) = k3_xboole_0(A_29,k1_tarski(B_30))
      | r2_hidden(B_30,A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_171])).

tff(c_2482,plain,(
    ! [A_163,B_164] :
      ( k3_xboole_0(A_163,k1_tarski(B_164)) = k3_xboole_0(A_163,k1_xboole_0)
      | r2_hidden(B_164,A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_186])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_132,plain,(
    ! [D_40,B_41,A_42] :
      ( r2_hidden(D_40,B_41)
      | ~ r2_hidden(D_40,k3_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_462,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_66,B_67)),B_67)
      | k3_xboole_0(A_66,B_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_482,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_1,B_2)),A_1)
      | k3_xboole_0(B_2,A_1) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_462])).

tff(c_36,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_225,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_36])).

tff(c_234,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_225])).

tff(c_725,plain,(
    ! [A_88,C_89,B_90] :
      ( ~ r2_hidden(A_88,C_89)
      | ~ r2_hidden(A_88,B_90)
      | ~ r2_hidden(A_88,k5_xboole_0(B_90,C_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_764,plain,(
    ! [A_91] :
      ( ~ r2_hidden(A_91,k1_xboole_0)
      | ~ r2_hidden(A_91,k1_xboole_0)
      | ~ r2_hidden(A_91,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_725])).

tff(c_1016,plain,(
    ! [B_98] :
      ( ~ r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0,B_98)),k1_xboole_0)
      | k3_xboole_0(B_98,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_482,c_764])).

tff(c_1064,plain,(
    ! [B_99] : k3_xboole_0(B_99,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_482,c_1016])).

tff(c_1101,plain,(
    ! [B_99] : k5_xboole_0(B_99,k1_xboole_0) = k4_xboole_0(B_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_36])).

tff(c_1132,plain,(
    ! [B_99] : k5_xboole_0(B_99,k1_xboole_0) = B_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1101])).

tff(c_1050,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_482,c_1016])).

tff(c_412,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,k1_tarski(B_30)) = k3_xboole_0(A_29,k1_xboole_0)
      | r2_hidden(B_30,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_186])).

tff(c_1703,plain,(
    ! [A_130,B_131] :
      ( k3_xboole_0(A_130,k1_tarski(B_131)) = k1_xboole_0
      | r2_hidden(B_131,A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_412])).

tff(c_156,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_168,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_1738,plain,(
    ! [B_131,A_130] :
      ( k5_xboole_0(k1_tarski(B_131),k1_xboole_0) = k4_xboole_0(k1_tarski(B_131),A_130)
      | r2_hidden(B_131,A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1703,c_168])).

tff(c_1991,plain,(
    ! [B_140,A_141] :
      ( k4_xboole_0(k1_tarski(B_140),A_141) = k1_tarski(B_140)
      | r2_hidden(B_140,A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1738])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_251,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2009,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_251])).

tff(c_2060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_2009])).

tff(c_2062,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2104,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_58])).

tff(c_40,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2108,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_40])).

tff(c_2111,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2108])).

tff(c_2255,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_189])).

tff(c_2296,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2255])).

tff(c_2503,plain,
    ( k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2482,c_2296])).

tff(c_2550,plain,
    ( k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0
    | r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_2503])).

tff(c_3092,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2550])).

tff(c_2179,plain,(
    ! [A_149,C_150,B_151] :
      ( ~ r2_hidden(A_149,C_150)
      | ~ r2_hidden(A_149,B_151)
      | ~ r2_hidden(A_149,k5_xboole_0(B_151,C_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2185,plain,(
    ! [A_149] :
      ( ~ r2_hidden(A_149,k1_xboole_0)
      | ~ r2_hidden(A_149,k1_xboole_0)
      | ~ r2_hidden(A_149,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_2179])).

tff(c_3103,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3092,c_2185])).

tff(c_3108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3103])).

tff(c_3109,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2550])).

tff(c_3113,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_2255])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3204,plain,(
    ! [D_8] :
      ( r2_hidden(D_8,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3113,c_8])).

tff(c_4697,plain,(
    ! [A_227,A_228,B_229] :
      ( ~ r2_hidden(A_227,k3_xboole_0(A_228,B_229))
      | ~ r2_hidden(A_227,A_228)
      | ~ r2_hidden(A_227,k4_xboole_0(A_228,B_229)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2179])).

tff(c_4776,plain,(
    ! [A_227] :
      ( ~ r2_hidden(A_227,k3_xboole_0(k1_tarski('#skF_6'),'#skF_7'))
      | ~ r2_hidden(A_227,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_227,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_4697])).

tff(c_4987,plain,(
    ! [A_232] :
      ( ~ r2_hidden(A_232,k1_xboole_0)
      | ~ r2_hidden(A_232,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_232,k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_2,c_4776])).

tff(c_5055,plain,(
    ! [D_233] :
      ( ~ r2_hidden(D_233,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_233,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3204,c_4987])).

tff(c_5132,plain,(
    ! [D_234] : ~ r2_hidden(D_234,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3204,c_5055])).

tff(c_5191,plain,(
    ! [B_235] : k3_xboole_0(k1_xboole_0,B_235) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4028,c_5132])).

tff(c_5233,plain,(
    ! [B_235] : k5_xboole_0(B_235,k1_xboole_0) = k4_xboole_0(B_235,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5191,c_168])).

tff(c_5276,plain,(
    ! [B_235] : k5_xboole_0(B_235,k1_xboole_0) = B_235 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5233])).

tff(c_2061,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3130,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_6')) = k5_xboole_0('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3109,c_36])).

tff(c_50,plain,(
    ! [B_30,A_29] :
      ( ~ r2_hidden(B_30,A_29)
      | k4_xboole_0(A_29,k1_tarski(B_30)) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3414,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | k5_xboole_0('#skF_7',k1_xboole_0) != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_3130,c_50])).

tff(c_3427,plain,(
    k5_xboole_0('#skF_7',k1_xboole_0) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_3414])).

tff(c_5655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5276,c_3427])).

tff(c_5657,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5800,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5657,c_60])).

tff(c_5804,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5800,c_40])).

tff(c_5807,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5804])).

tff(c_5958,plain,
    ( k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6')
    | r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_5807])).

tff(c_6039,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5958])).

tff(c_5743,plain,(
    ! [A_258,B_259] : k4_xboole_0(A_258,k4_xboole_0(A_258,B_259)) = k3_xboole_0(A_258,B_259) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5764,plain,(
    ! [A_260] : k4_xboole_0(A_260,A_260) = k3_xboole_0(A_260,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5743])).

tff(c_5782,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5764,c_38])).

tff(c_5761,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5743])).

tff(c_5758,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,A_29) = k3_xboole_0(A_29,k1_tarski(B_30))
      | r2_hidden(B_30,A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_5743])).

tff(c_6069,plain,(
    ! [A_278,B_279] :
      ( k3_xboole_0(A_278,k1_tarski(B_279)) = k3_xboole_0(A_278,k1_xboole_0)
      | r2_hidden(B_279,A_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5761,c_5758])).

tff(c_5942,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5807,c_5761])).

tff(c_5986,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) = k3_xboole_0('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5942])).

tff(c_6078,plain,
    ( k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6069,c_5986])).

tff(c_6120,plain,
    ( k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0
    | r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_6078])).

tff(c_6125,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_6120])).

tff(c_5812,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5782,c_36])).

tff(c_5818,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5812])).

tff(c_6447,plain,(
    ! [A_296,C_297,B_298] :
      ( ~ r2_hidden(A_296,C_297)
      | ~ r2_hidden(A_296,B_298)
      | ~ r2_hidden(A_296,k5_xboole_0(B_298,C_297)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6486,plain,(
    ! [A_299] :
      ( ~ r2_hidden(A_299,k1_xboole_0)
      | ~ r2_hidden(A_299,k1_xboole_0)
      | ~ r2_hidden(A_299,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5818,c_6447])).

tff(c_6500,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6125,c_6486])).

tff(c_6511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6125,c_6500])).

tff(c_6512,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6120])).

tff(c_6517,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6512,c_5807])).

tff(c_6555,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6517,c_50])).

tff(c_6569,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6039,c_6555])).

tff(c_6513,plain,(
    ~ r2_hidden('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6120])).

tff(c_6515,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6512,c_5986])).

tff(c_5656,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5778,plain,(
    ! [B_30] :
      ( k3_xboole_0(k1_tarski(B_30),k1_xboole_0) = k1_tarski(B_30)
      | r2_hidden(B_30,k1_tarski(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5764,c_52])).

tff(c_5796,plain,(
    ! [B_30] :
      ( k3_xboole_0(k1_xboole_0,k1_tarski(B_30)) = k1_tarski(B_30)
      | r2_hidden(B_30,k1_tarski(B_30)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5778])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k3_xboole_0(A_3,B_4))
      | ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6042,plain,(
    ! [D_274] :
      ( r2_hidden(D_274,k1_xboole_0)
      | ~ r2_hidden(D_274,k3_xboole_0('#skF_7',k1_tarski('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5942,c_6])).

tff(c_7901,plain,(
    ! [D_352] :
      ( r2_hidden(D_352,k1_xboole_0)
      | ~ r2_hidden(D_352,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_352,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4,c_6042])).

tff(c_7917,plain,
    ( r2_hidden('#skF_6',k1_xboole_0)
    | ~ r2_hidden('#skF_6','#skF_7')
    | k3_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_5796,c_7901])).

tff(c_7964,plain,
    ( r2_hidden('#skF_6',k1_xboole_0)
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6515,c_5656,c_7917])).

tff(c_7966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6569,c_6513,c_7964])).

tff(c_7967,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5958])).

tff(c_5948,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5807,c_50])).

tff(c_7969,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5948])).

tff(c_8030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7967,c_7969])).

tff(c_8032,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5948])).

tff(c_8182,plain,(
    ! [D_359] :
      ( r2_hidden(D_359,'#skF_7')
      | ~ r2_hidden(D_359,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8032,c_8])).

tff(c_8187,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_7')
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_8182])).

tff(c_8278,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8187])).

tff(c_8301,plain,(
    ! [A_29] :
      ( ~ r2_hidden('#skF_6',A_29)
      | k4_xboole_0(A_29,k1_xboole_0) != A_29 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8278,c_50])).

tff(c_8308,plain,(
    ! [A_29] : ~ r2_hidden('#skF_6',A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8301])).

tff(c_8330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8308,c_5656])).

tff(c_8332,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8187])).

tff(c_8044,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8032,c_5942])).

tff(c_8188,plain,(
    ! [D_360] :
      ( r2_hidden(D_360,k1_xboole_0)
      | ~ r2_hidden(D_360,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8044,c_6])).

tff(c_8193,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_6')),k1_xboole_0)
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_8188])).

tff(c_8335,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_6')),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_8332,c_8193])).

tff(c_8205,plain,(
    ! [A_361,C_362,B_363] :
      ( ~ r2_hidden(A_361,C_362)
      | ~ r2_hidden(A_361,B_363)
      | ~ r2_hidden(A_361,k5_xboole_0(B_363,C_362)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8365,plain,(
    ! [A_370] :
      ( ~ r2_hidden(A_370,k1_xboole_0)
      | ~ r2_hidden(A_370,k1_xboole_0)
      | ~ r2_hidden(A_370,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5818,c_8205])).

tff(c_8367,plain,(
    ~ r2_hidden('#skF_3'(k1_tarski('#skF_6')),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8335,c_8365])).

tff(c_8374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8335,c_8367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.63/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.50  
% 6.63/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.50  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.63/2.50  
% 6.63/2.50  %Foreground sorts:
% 6.63/2.50  
% 6.63/2.50  
% 6.63/2.50  %Background operators:
% 6.63/2.50  
% 6.63/2.50  
% 6.63/2.50  %Foreground operators:
% 6.63/2.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.63/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.63/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.63/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.63/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.63/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.63/2.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.63/2.50  tff('#skF_7', type, '#skF_7': $i).
% 6.63/2.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.63/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.63/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.63/2.50  tff('#skF_5', type, '#skF_5': $i).
% 6.63/2.50  tff('#skF_6', type, '#skF_6': $i).
% 6.63/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.63/2.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.63/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.63/2.50  tff('#skF_4', type, '#skF_4': $i).
% 6.63/2.50  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.63/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.63/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.63/2.50  
% 6.91/2.53  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.91/2.53  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.91/2.53  tff(f_70, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.91/2.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.91/2.53  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.91/2.53  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.91/2.53  tff(f_76, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 6.91/2.53  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.91/2.53  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.91/2.53  tff(c_38, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.91/2.53  tff(c_34, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.91/2.53  tff(c_52, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k1_tarski(B_30))=A_29 | r2_hidden(B_30, A_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.91/2.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.91/2.53  tff(c_144, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, A_44) | ~r2_hidden(D_43, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.91/2.53  tff(c_3951, plain, (![A_208, B_209]: (r2_hidden('#skF_3'(k3_xboole_0(A_208, B_209)), A_208) | k3_xboole_0(A_208, B_209)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_144])).
% 6.91/2.53  tff(c_4028, plain, (![B_2, A_1]: (r2_hidden('#skF_3'(k3_xboole_0(B_2, A_1)), A_1) | k3_xboole_0(A_1, B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3951])).
% 6.91/2.53  tff(c_171, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.91/2.53  tff(c_192, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k3_xboole_0(A_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_171])).
% 6.91/2.53  tff(c_206, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_192, c_38])).
% 6.91/2.53  tff(c_189, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_171])).
% 6.91/2.53  tff(c_186, plain, (![A_29, B_30]: (k4_xboole_0(A_29, A_29)=k3_xboole_0(A_29, k1_tarski(B_30)) | r2_hidden(B_30, A_29))), inference(superposition, [status(thm), theory('equality')], [c_52, c_171])).
% 6.91/2.53  tff(c_2482, plain, (![A_163, B_164]: (k3_xboole_0(A_163, k1_tarski(B_164))=k3_xboole_0(A_163, k1_xboole_0) | r2_hidden(B_164, A_163))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_186])).
% 6.91/2.53  tff(c_56, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.91/2.53  tff(c_79, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 6.91/2.53  tff(c_132, plain, (![D_40, B_41, A_42]: (r2_hidden(D_40, B_41) | ~r2_hidden(D_40, k3_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.91/2.53  tff(c_462, plain, (![A_66, B_67]: (r2_hidden('#skF_3'(k3_xboole_0(A_66, B_67)), B_67) | k3_xboole_0(A_66, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_132])).
% 6.91/2.53  tff(c_482, plain, (![A_1, B_2]: (r2_hidden('#skF_3'(k3_xboole_0(A_1, B_2)), A_1) | k3_xboole_0(B_2, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_462])).
% 6.91/2.53  tff(c_36, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.91/2.53  tff(c_225, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_36])).
% 6.91/2.53  tff(c_234, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_225])).
% 6.91/2.53  tff(c_725, plain, (![A_88, C_89, B_90]: (~r2_hidden(A_88, C_89) | ~r2_hidden(A_88, B_90) | ~r2_hidden(A_88, k5_xboole_0(B_90, C_89)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.91/2.53  tff(c_764, plain, (![A_91]: (~r2_hidden(A_91, k1_xboole_0) | ~r2_hidden(A_91, k1_xboole_0) | ~r2_hidden(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_725])).
% 6.91/2.53  tff(c_1016, plain, (![B_98]: (~r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0, B_98)), k1_xboole_0) | k3_xboole_0(B_98, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_482, c_764])).
% 6.91/2.53  tff(c_1064, plain, (![B_99]: (k3_xboole_0(B_99, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_482, c_1016])).
% 6.91/2.53  tff(c_1101, plain, (![B_99]: (k5_xboole_0(B_99, k1_xboole_0)=k4_xboole_0(B_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1064, c_36])).
% 6.91/2.53  tff(c_1132, plain, (![B_99]: (k5_xboole_0(B_99, k1_xboole_0)=B_99)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1101])).
% 6.91/2.53  tff(c_1050, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_482, c_1016])).
% 6.91/2.53  tff(c_412, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k1_tarski(B_30))=k3_xboole_0(A_29, k1_xboole_0) | r2_hidden(B_30, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_186])).
% 6.91/2.53  tff(c_1703, plain, (![A_130, B_131]: (k3_xboole_0(A_130, k1_tarski(B_131))=k1_xboole_0 | r2_hidden(B_131, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_412])).
% 6.91/2.53  tff(c_156, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.91/2.53  tff(c_168, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_156])).
% 6.91/2.53  tff(c_1738, plain, (![B_131, A_130]: (k5_xboole_0(k1_tarski(B_131), k1_xboole_0)=k4_xboole_0(k1_tarski(B_131), A_130) | r2_hidden(B_131, A_130))), inference(superposition, [status(thm), theory('equality')], [c_1703, c_168])).
% 6.91/2.53  tff(c_1991, plain, (![B_140, A_141]: (k4_xboole_0(k1_tarski(B_140), A_141)=k1_tarski(B_140) | r2_hidden(B_140, A_141))), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1738])).
% 6.91/2.53  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.91/2.53  tff(c_251, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 6.91/2.53  tff(c_2009, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1991, c_251])).
% 6.91/2.53  tff(c_2060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_2009])).
% 6.91/2.53  tff(c_2062, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 6.91/2.53  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.91/2.53  tff(c_2104, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_58])).
% 6.91/2.53  tff(c_40, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.91/2.53  tff(c_2108, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2104, c_40])).
% 6.91/2.53  tff(c_2111, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2108])).
% 6.91/2.53  tff(c_2255, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2111, c_189])).
% 6.91/2.53  tff(c_2296, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2255])).
% 6.91/2.53  tff(c_2503, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k3_xboole_0(k1_xboole_0, k1_xboole_0) | r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2482, c_2296])).
% 6.91/2.53  tff(c_2550, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0 | r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_206, c_2503])).
% 6.91/2.53  tff(c_3092, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2550])).
% 6.91/2.53  tff(c_2179, plain, (![A_149, C_150, B_151]: (~r2_hidden(A_149, C_150) | ~r2_hidden(A_149, B_151) | ~r2_hidden(A_149, k5_xboole_0(B_151, C_150)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.91/2.53  tff(c_2185, plain, (![A_149]: (~r2_hidden(A_149, k1_xboole_0) | ~r2_hidden(A_149, k1_xboole_0) | ~r2_hidden(A_149, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_2179])).
% 6.91/2.53  tff(c_3103, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_3092, c_2185])).
% 6.91/2.53  tff(c_3108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3103])).
% 6.91/2.53  tff(c_3109, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2550])).
% 6.91/2.53  tff(c_3113, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_2255])).
% 6.91/2.53  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.91/2.53  tff(c_3204, plain, (![D_8]: (r2_hidden(D_8, k1_tarski('#skF_6')) | ~r2_hidden(D_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3113, c_8])).
% 6.91/2.53  tff(c_4697, plain, (![A_227, A_228, B_229]: (~r2_hidden(A_227, k3_xboole_0(A_228, B_229)) | ~r2_hidden(A_227, A_228) | ~r2_hidden(A_227, k4_xboole_0(A_228, B_229)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2179])).
% 6.91/2.53  tff(c_4776, plain, (![A_227]: (~r2_hidden(A_227, k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')) | ~r2_hidden(A_227, k1_tarski('#skF_6')) | ~r2_hidden(A_227, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_4697])).
% 6.91/2.53  tff(c_4987, plain, (![A_232]: (~r2_hidden(A_232, k1_xboole_0) | ~r2_hidden(A_232, k1_tarski('#skF_6')) | ~r2_hidden(A_232, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_2, c_4776])).
% 6.91/2.53  tff(c_5055, plain, (![D_233]: (~r2_hidden(D_233, k1_tarski('#skF_6')) | ~r2_hidden(D_233, k1_xboole_0))), inference(resolution, [status(thm)], [c_3204, c_4987])).
% 6.91/2.53  tff(c_5132, plain, (![D_234]: (~r2_hidden(D_234, k1_xboole_0))), inference(resolution, [status(thm)], [c_3204, c_5055])).
% 6.91/2.53  tff(c_5191, plain, (![B_235]: (k3_xboole_0(k1_xboole_0, B_235)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4028, c_5132])).
% 6.91/2.53  tff(c_5233, plain, (![B_235]: (k5_xboole_0(B_235, k1_xboole_0)=k4_xboole_0(B_235, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5191, c_168])).
% 6.91/2.53  tff(c_5276, plain, (![B_235]: (k5_xboole_0(B_235, k1_xboole_0)=B_235)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5233])).
% 6.91/2.53  tff(c_2061, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 6.91/2.53  tff(c_3130, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_6'))=k5_xboole_0('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3109, c_36])).
% 6.91/2.53  tff(c_50, plain, (![B_30, A_29]: (~r2_hidden(B_30, A_29) | k4_xboole_0(A_29, k1_tarski(B_30))!=A_29)), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.91/2.53  tff(c_3414, plain, (~r2_hidden('#skF_6', '#skF_7') | k5_xboole_0('#skF_7', k1_xboole_0)!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_3130, c_50])).
% 6.91/2.53  tff(c_3427, plain, (k5_xboole_0('#skF_7', k1_xboole_0)!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_3414])).
% 6.91/2.53  tff(c_5655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5276, c_3427])).
% 6.91/2.53  tff(c_5657, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 6.91/2.53  tff(c_60, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.91/2.53  tff(c_5800, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5657, c_60])).
% 6.91/2.53  tff(c_5804, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5800, c_40])).
% 6.91/2.53  tff(c_5807, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5804])).
% 6.91/2.53  tff(c_5958, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6') | r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_5807])).
% 6.91/2.53  tff(c_6039, plain, (r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_5958])).
% 6.91/2.53  tff(c_5743, plain, (![A_258, B_259]: (k4_xboole_0(A_258, k4_xboole_0(A_258, B_259))=k3_xboole_0(A_258, B_259))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.91/2.53  tff(c_5764, plain, (![A_260]: (k4_xboole_0(A_260, A_260)=k3_xboole_0(A_260, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5743])).
% 6.91/2.53  tff(c_5782, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5764, c_38])).
% 6.91/2.53  tff(c_5761, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5743])).
% 6.91/2.53  tff(c_5758, plain, (![A_29, B_30]: (k4_xboole_0(A_29, A_29)=k3_xboole_0(A_29, k1_tarski(B_30)) | r2_hidden(B_30, A_29))), inference(superposition, [status(thm), theory('equality')], [c_52, c_5743])).
% 6.91/2.53  tff(c_6069, plain, (![A_278, B_279]: (k3_xboole_0(A_278, k1_tarski(B_279))=k3_xboole_0(A_278, k1_xboole_0) | r2_hidden(B_279, A_278))), inference(demodulation, [status(thm), theory('equality')], [c_5761, c_5758])).
% 6.91/2.53  tff(c_5942, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5807, c_5761])).
% 6.91/2.53  tff(c_5986, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))=k3_xboole_0('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5942])).
% 6.91/2.53  tff(c_6078, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k3_xboole_0(k1_xboole_0, k1_xboole_0) | r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6069, c_5986])).
% 6.91/2.53  tff(c_6120, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0 | r2_hidden('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5782, c_6078])).
% 6.91/2.53  tff(c_6125, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_6120])).
% 6.91/2.53  tff(c_5812, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5782, c_36])).
% 6.91/2.53  tff(c_5818, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5812])).
% 6.91/2.53  tff(c_6447, plain, (![A_296, C_297, B_298]: (~r2_hidden(A_296, C_297) | ~r2_hidden(A_296, B_298) | ~r2_hidden(A_296, k5_xboole_0(B_298, C_297)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.91/2.53  tff(c_6486, plain, (![A_299]: (~r2_hidden(A_299, k1_xboole_0) | ~r2_hidden(A_299, k1_xboole_0) | ~r2_hidden(A_299, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5818, c_6447])).
% 6.91/2.53  tff(c_6500, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_6125, c_6486])).
% 6.91/2.53  tff(c_6511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6125, c_6500])).
% 6.91/2.53  tff(c_6512, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_6120])).
% 6.91/2.53  tff(c_6517, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6512, c_5807])).
% 6.91/2.53  tff(c_6555, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | k1_tarski('#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6517, c_50])).
% 6.91/2.53  tff(c_6569, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6039, c_6555])).
% 6.91/2.53  tff(c_6513, plain, (~r2_hidden('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_6120])).
% 6.91/2.53  tff(c_6515, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6512, c_5986])).
% 6.91/2.53  tff(c_5656, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 6.91/2.53  tff(c_5778, plain, (![B_30]: (k3_xboole_0(k1_tarski(B_30), k1_xboole_0)=k1_tarski(B_30) | r2_hidden(B_30, k1_tarski(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_5764, c_52])).
% 6.91/2.53  tff(c_5796, plain, (![B_30]: (k3_xboole_0(k1_xboole_0, k1_tarski(B_30))=k1_tarski(B_30) | r2_hidden(B_30, k1_tarski(B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5778])).
% 6.91/2.53  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k3_xboole_0(A_3, B_4)) | ~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.91/2.53  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.91/2.53  tff(c_6042, plain, (![D_274]: (r2_hidden(D_274, k1_xboole_0) | ~r2_hidden(D_274, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_5942, c_6])).
% 6.91/2.53  tff(c_7901, plain, (![D_352]: (r2_hidden(D_352, k1_xboole_0) | ~r2_hidden(D_352, k1_tarski('#skF_6')) | ~r2_hidden(D_352, '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_6042])).
% 6.91/2.53  tff(c_7917, plain, (r2_hidden('#skF_6', k1_xboole_0) | ~r2_hidden('#skF_6', '#skF_7') | k3_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_5796, c_7901])).
% 6.91/2.53  tff(c_7964, plain, (r2_hidden('#skF_6', k1_xboole_0) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6515, c_5656, c_7917])).
% 6.91/2.53  tff(c_7966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6569, c_6513, c_7964])).
% 6.91/2.53  tff(c_7967, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_5958])).
% 6.91/2.53  tff(c_5948, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5807, c_50])).
% 6.91/2.53  tff(c_7969, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_5948])).
% 6.91/2.53  tff(c_8030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7967, c_7969])).
% 6.91/2.53  tff(c_8032, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_5948])).
% 6.91/2.53  tff(c_8182, plain, (![D_359]: (r2_hidden(D_359, '#skF_7') | ~r2_hidden(D_359, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8032, c_8])).
% 6.91/2.53  tff(c_8187, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_7') | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_8182])).
% 6.91/2.53  tff(c_8278, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8187])).
% 6.91/2.53  tff(c_8301, plain, (![A_29]: (~r2_hidden('#skF_6', A_29) | k4_xboole_0(A_29, k1_xboole_0)!=A_29)), inference(superposition, [status(thm), theory('equality')], [c_8278, c_50])).
% 6.91/2.53  tff(c_8308, plain, (![A_29]: (~r2_hidden('#skF_6', A_29))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8301])).
% 6.91/2.53  tff(c_8330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8308, c_5656])).
% 6.91/2.53  tff(c_8332, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8187])).
% 6.91/2.53  tff(c_8044, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8032, c_5942])).
% 6.91/2.53  tff(c_8188, plain, (![D_360]: (r2_hidden(D_360, k1_xboole_0) | ~r2_hidden(D_360, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8044, c_6])).
% 6.91/2.53  tff(c_8193, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), k1_xboole_0) | k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_8188])).
% 6.91/2.53  tff(c_8335, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_8332, c_8193])).
% 6.91/2.53  tff(c_8205, plain, (![A_361, C_362, B_363]: (~r2_hidden(A_361, C_362) | ~r2_hidden(A_361, B_363) | ~r2_hidden(A_361, k5_xboole_0(B_363, C_362)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.91/2.53  tff(c_8365, plain, (![A_370]: (~r2_hidden(A_370, k1_xboole_0) | ~r2_hidden(A_370, k1_xboole_0) | ~r2_hidden(A_370, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5818, c_8205])).
% 6.91/2.53  tff(c_8367, plain, (~r2_hidden('#skF_3'(k1_tarski('#skF_6')), k1_xboole_0)), inference(resolution, [status(thm)], [c_8335, c_8365])).
% 6.91/2.53  tff(c_8374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8335, c_8367])).
% 6.91/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.53  
% 6.91/2.53  Inference rules
% 6.91/2.53  ----------------------
% 6.91/2.53  #Ref     : 0
% 6.91/2.53  #Sup     : 1990
% 6.91/2.53  #Fact    : 0
% 6.91/2.53  #Define  : 0
% 6.91/2.53  #Split   : 14
% 6.91/2.53  #Chain   : 0
% 6.91/2.53  #Close   : 0
% 6.91/2.53  
% 6.91/2.53  Ordering : KBO
% 6.91/2.53  
% 6.91/2.53  Simplification rules
% 6.91/2.53  ----------------------
% 6.91/2.53  #Subsume      : 272
% 6.91/2.53  #Demod        : 1326
% 6.91/2.53  #Tautology    : 973
% 6.91/2.53  #SimpNegUnit  : 108
% 6.91/2.53  #BackRed      : 121
% 6.91/2.53  
% 6.91/2.53  #Partial instantiations: 0
% 6.91/2.53  #Strategies tried      : 1
% 6.91/2.53  
% 6.91/2.53  Timing (in seconds)
% 6.91/2.53  ----------------------
% 6.91/2.53  Preprocessing        : 0.31
% 6.91/2.53  Parsing              : 0.16
% 6.91/2.53  CNF conversion       : 0.02
% 6.91/2.53  Main loop            : 1.42
% 6.91/2.53  Inferencing          : 0.46
% 6.91/2.53  Reduction            : 0.53
% 6.91/2.53  Demodulation         : 0.41
% 6.91/2.53  BG Simplification    : 0.06
% 6.91/2.53  Subsumption          : 0.26
% 6.91/2.53  Abstraction          : 0.07
% 6.91/2.53  MUC search           : 0.00
% 6.91/2.53  Cooper               : 0.00
% 6.91/2.53  Total                : 1.79
% 6.91/2.53  Index Insertion      : 0.00
% 6.91/2.53  Index Deletion       : 0.00
% 6.91/2.53  Index Matching       : 0.00
% 6.91/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
