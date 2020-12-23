%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:16 EST 2020

% Result     : Theorem 12.63s
% Output     : CNFRefutation 12.63s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 229 expanded)
%              Number of leaves         :   30 (  85 expanded)
%              Depth                    :    7
%              Number of atoms          :  146 ( 376 expanded)
%              Number of equality atoms :   51 ( 155 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_62,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_228,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_304,plain,(
    ! [A_60,B_61] : k2_xboole_0(k1_tarski(A_60),k1_tarski(B_61)) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_132,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,(
    ! [A_52,B_51] : k4_xboole_0(A_52,k2_xboole_0(B_51,A_52)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_40])).

tff(c_310,plain,(
    ! [B_61,A_60] : k4_xboole_0(k1_tarski(B_61),k2_tarski(A_60,B_61)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_147])).

tff(c_435,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | k4_xboole_0(k1_tarski(A_75),B_76) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_454,plain,(
    ! [B_61,A_60] : r2_hidden(B_61,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_435])).

tff(c_30,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_99])).

tff(c_459,plain,(
    ! [A_77] : r2_hidden(A_77,k1_tarski(A_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_435])).

tff(c_42,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_377,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_395,plain,(
    ! [D_66,A_29] :
      ( ~ r2_hidden(D_66,A_29)
      | ~ r2_hidden(D_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_377])).

tff(c_462,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_459,c_395])).

tff(c_48,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_71,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_70])).

tff(c_615,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_2669,plain,(
    ! [D_140,A_141,B_142] :
      ( r2_hidden(D_140,k4_xboole_0(A_141,B_142))
      | r2_hidden(D_140,B_142)
      | ~ r2_hidden(D_140,A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2705,plain,(
    ! [D_140] :
      ( r2_hidden(D_140,k1_xboole_0)
      | r2_hidden(D_140,'#skF_9')
      | ~ r2_hidden(D_140,k2_tarski('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_2669])).

tff(c_2801,plain,(
    ! [D_146] :
      ( r2_hidden(D_146,'#skF_9')
      | ~ r2_hidden(D_146,k2_tarski('#skF_8','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_2705])).

tff(c_2805,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_454,c_2801])).

tff(c_2817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_2805])).

tff(c_2818,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_2819,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_68,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_72,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_68])).

tff(c_2820,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2819,c_2820])).

tff(c_2822,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_5815,plain,(
    ! [A_222,C_223,B_224] :
      ( k2_xboole_0(k2_tarski(A_222,C_223),B_224) = B_224
      | ~ r2_hidden(C_223,B_224)
      | ~ r2_hidden(A_222,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_17329,plain,(
    ! [A_446,C_447,B_448] :
      ( k4_xboole_0(k2_tarski(A_446,C_447),B_448) = k1_xboole_0
      | ~ r2_hidden(C_447,B_448)
      | ~ r2_hidden(A_446,B_448) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5815,c_40])).

tff(c_66,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_66])).

tff(c_2897,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2819,c_73])).

tff(c_17435,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17329,c_2897])).

tff(c_17538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_2822,c_17435])).

tff(c_17540,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_17576,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17540,c_64])).

tff(c_17577,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_17576])).

tff(c_17619,plain,(
    ! [A_455,B_456] : k2_xboole_0(k1_tarski(A_455),k1_tarski(B_456)) = k2_tarski(A_455,B_456) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_17634,plain,(
    ! [A_455,B_456] : k4_xboole_0(k1_tarski(A_455),k2_tarski(A_455,B_456)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17619,c_40])).

tff(c_17695,plain,(
    ! [A_463,B_464] :
      ( r2_hidden(A_463,B_464)
      | k4_xboole_0(k1_tarski(A_463),B_464) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_17715,plain,(
    ! [A_455,B_456] : r2_hidden(A_455,k2_tarski(A_455,B_456)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17634,c_17695])).

tff(c_17718,plain,(
    ! [A_463,B_28] : r2_hidden(A_463,k2_xboole_0(k1_tarski(A_463),B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_17695])).

tff(c_17928,plain,(
    ! [D_480,B_481,A_482] :
      ( ~ r2_hidden(D_480,B_481)
      | ~ r2_hidden(D_480,k4_xboole_0(A_482,B_481)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17959,plain,(
    ! [D_483,A_484] :
      ( ~ r2_hidden(D_483,A_484)
      | ~ r2_hidden(D_483,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_17928])).

tff(c_17976,plain,(
    ! [A_463] : ~ r2_hidden(A_463,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17718,c_17959])).

tff(c_17815,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_19727,plain,(
    ! [D_532,A_533,B_534] :
      ( r2_hidden(D_532,k4_xboole_0(A_533,B_534))
      | r2_hidden(D_532,B_534)
      | ~ r2_hidden(D_532,A_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19760,plain,(
    ! [D_532] :
      ( r2_hidden(D_532,k1_xboole_0)
      | r2_hidden(D_532,'#skF_9')
      | ~ r2_hidden(D_532,k2_tarski('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17815,c_19727])).

tff(c_19854,plain,(
    ! [D_538] :
      ( r2_hidden(D_538,'#skF_9')
      | ~ r2_hidden(D_538,k2_tarski('#skF_8','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_17976,c_19760])).

tff(c_19870,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_17715,c_19854])).

tff(c_19879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17577,c_19870])).

tff(c_19881,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_19882,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_7'),'#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_19883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19881,c_19882])).

tff(c_19884,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_19880,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_23038,plain,(
    ! [A_630,C_631,B_632] :
      ( k2_xboole_0(k2_tarski(A_630,C_631),B_632) = B_632
      | ~ r2_hidden(C_631,B_632)
      | ~ r2_hidden(A_630,B_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23103,plain,(
    ! [A_630,C_631,B_632] :
      ( k4_xboole_0(k2_tarski(A_630,C_631),B_632) = k4_xboole_0(B_632,B_632)
      | ~ r2_hidden(C_631,B_632)
      | ~ r2_hidden(A_630,B_632) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23038,c_34])).

tff(c_37589,plain,(
    ! [A_887,C_888,B_889] :
      ( k4_xboole_0(k2_tarski(A_887,C_888),B_889) = k1_xboole_0
      | ~ r2_hidden(C_888,B_889)
      | ~ r2_hidden(A_887,B_889) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_23103])).

tff(c_20043,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_19881,c_73])).

tff(c_37720,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_37589,c_20043])).

tff(c_37827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19884,c_19880,c_37720])).

tff(c_37828,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_17576])).

tff(c_37829,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_17576])).

tff(c_17539,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_37831,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37829,c_17539])).

tff(c_39123,plain,(
    ! [A_965,C_966,B_967] :
      ( k2_xboole_0(k2_tarski(A_965,C_966),B_967) = B_967
      | ~ r2_hidden(C_966,B_967)
      | ~ r2_hidden(A_965,B_967) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_51676,plain,(
    ! [A_1224,C_1225,B_1226] :
      ( k4_xboole_0(k2_tarski(A_1224,C_1225),B_1226) = k1_xboole_0
      | ~ r2_hidden(C_1225,B_1226)
      | ~ r2_hidden(A_1224,B_1226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39123,c_40])).

tff(c_60,plain,
    ( k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37833,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17540,c_37829,c_60])).

tff(c_51793,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_51676,c_37833])).

tff(c_51879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37828,c_37831,c_51793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.63/6.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.63/6.12  
% 12.63/6.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.63/6.12  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 12.63/6.12  
% 12.63/6.12  %Foreground sorts:
% 12.63/6.12  
% 12.63/6.12  
% 12.63/6.12  %Background operators:
% 12.63/6.12  
% 12.63/6.12  
% 12.63/6.12  %Foreground operators:
% 12.63/6.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.63/6.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.63/6.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.63/6.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.63/6.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.63/6.12  tff('#skF_7', type, '#skF_7': $i).
% 12.63/6.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.63/6.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.63/6.12  tff('#skF_5', type, '#skF_5': $i).
% 12.63/6.12  tff('#skF_6', type, '#skF_6': $i).
% 12.63/6.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.63/6.12  tff('#skF_9', type, '#skF_9': $i).
% 12.63/6.12  tff('#skF_8', type, '#skF_8': $i).
% 12.63/6.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.63/6.12  tff('#skF_4', type, '#skF_4': $i).
% 12.63/6.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.63/6.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.63/6.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.63/6.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.63/6.12  
% 12.63/6.14  tff(f_89, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 12.63/6.14  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 12.63/6.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.63/6.14  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.63/6.14  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 12.63/6.14  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 12.63/6.14  tff(f_62, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 12.63/6.14  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.63/6.14  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.63/6.14  tff(f_78, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 12.63/6.14  tff(f_54, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.63/6.14  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.63/6.14  tff(c_228, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 12.63/6.14  tff(c_304, plain, (![A_60, B_61]: (k2_xboole_0(k1_tarski(A_60), k1_tarski(B_61))=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.63/6.14  tff(c_132, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.63/6.14  tff(c_40, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.63/6.14  tff(c_147, plain, (![A_52, B_51]: (k4_xboole_0(A_52, k2_xboole_0(B_51, A_52))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_40])).
% 12.63/6.14  tff(c_310, plain, (![B_61, A_60]: (k4_xboole_0(k1_tarski(B_61), k2_tarski(A_60, B_61))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_304, c_147])).
% 12.63/6.14  tff(c_435, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | k4_xboole_0(k1_tarski(A_75), B_76)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.63/6.14  tff(c_454, plain, (![B_61, A_60]: (r2_hidden(B_61, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_435])).
% 12.63/6.14  tff(c_30, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.63/6.14  tff(c_99, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.63/6.14  tff(c_109, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_99])).
% 12.63/6.14  tff(c_459, plain, (![A_77]: (r2_hidden(A_77, k1_tarski(A_77)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_435])).
% 12.63/6.14  tff(c_42, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.63/6.14  tff(c_377, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.63/6.14  tff(c_395, plain, (![D_66, A_29]: (~r2_hidden(D_66, A_29) | ~r2_hidden(D_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_377])).
% 12.63/6.14  tff(c_462, plain, (![A_77]: (~r2_hidden(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_459, c_395])).
% 12.63/6.14  tff(c_48, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.63/6.14  tff(c_70, plain, (r2_hidden('#skF_4', '#skF_6') | k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.63/6.14  tff(c_71, plain, (r2_hidden('#skF_4', '#skF_6') | k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_70])).
% 12.63/6.14  tff(c_615, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71])).
% 12.63/6.14  tff(c_2669, plain, (![D_140, A_141, B_142]: (r2_hidden(D_140, k4_xboole_0(A_141, B_142)) | r2_hidden(D_140, B_142) | ~r2_hidden(D_140, A_141))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.63/6.14  tff(c_2705, plain, (![D_140]: (r2_hidden(D_140, k1_xboole_0) | r2_hidden(D_140, '#skF_9') | ~r2_hidden(D_140, k2_tarski('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_615, c_2669])).
% 12.63/6.14  tff(c_2801, plain, (![D_146]: (r2_hidden(D_146, '#skF_9') | ~r2_hidden(D_146, k2_tarski('#skF_8', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_462, c_2705])).
% 12.63/6.14  tff(c_2805, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_454, c_2801])).
% 12.63/6.14  tff(c_2817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_2805])).
% 12.63/6.14  tff(c_2818, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_71])).
% 12.63/6.14  tff(c_2819, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_71])).
% 12.63/6.14  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.63/6.14  tff(c_72, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68])).
% 12.63/6.14  tff(c_2820, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 12.63/6.14  tff(c_2821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2819, c_2820])).
% 12.63/6.14  tff(c_2822, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 12.63/6.14  tff(c_5815, plain, (![A_222, C_223, B_224]: (k2_xboole_0(k2_tarski(A_222, C_223), B_224)=B_224 | ~r2_hidden(C_223, B_224) | ~r2_hidden(A_222, B_224))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.63/6.14  tff(c_17329, plain, (![A_446, C_447, B_448]: (k4_xboole_0(k2_tarski(A_446, C_447), B_448)=k1_xboole_0 | ~r2_hidden(C_447, B_448) | ~r2_hidden(A_446, B_448))), inference(superposition, [status(thm), theory('equality')], [c_5815, c_40])).
% 12.63/6.14  tff(c_66, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.63/6.14  tff(c_73, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_66])).
% 12.63/6.14  tff(c_2897, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2819, c_73])).
% 12.63/6.14  tff(c_17435, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17329, c_2897])).
% 12.63/6.14  tff(c_17538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2818, c_2822, c_17435])).
% 12.63/6.14  tff(c_17540, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 12.63/6.14  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.63/6.14  tff(c_17576, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17540, c_64])).
% 12.63/6.14  tff(c_17577, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_17576])).
% 12.63/6.14  tff(c_17619, plain, (![A_455, B_456]: (k2_xboole_0(k1_tarski(A_455), k1_tarski(B_456))=k2_tarski(A_455, B_456))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.63/6.14  tff(c_17634, plain, (![A_455, B_456]: (k4_xboole_0(k1_tarski(A_455), k2_tarski(A_455, B_456))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17619, c_40])).
% 12.63/6.14  tff(c_17695, plain, (![A_463, B_464]: (r2_hidden(A_463, B_464) | k4_xboole_0(k1_tarski(A_463), B_464)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.63/6.14  tff(c_17715, plain, (![A_455, B_456]: (r2_hidden(A_455, k2_tarski(A_455, B_456)))), inference(superposition, [status(thm), theory('equality')], [c_17634, c_17695])).
% 12.63/6.14  tff(c_17718, plain, (![A_463, B_28]: (r2_hidden(A_463, k2_xboole_0(k1_tarski(A_463), B_28)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_17695])).
% 12.63/6.14  tff(c_17928, plain, (![D_480, B_481, A_482]: (~r2_hidden(D_480, B_481) | ~r2_hidden(D_480, k4_xboole_0(A_482, B_481)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.63/6.14  tff(c_17959, plain, (![D_483, A_484]: (~r2_hidden(D_483, A_484) | ~r2_hidden(D_483, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_17928])).
% 12.63/6.14  tff(c_17976, plain, (![A_463]: (~r2_hidden(A_463, k1_xboole_0))), inference(resolution, [status(thm)], [c_17718, c_17959])).
% 12.63/6.14  tff(c_17815, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 12.63/6.14  tff(c_19727, plain, (![D_532, A_533, B_534]: (r2_hidden(D_532, k4_xboole_0(A_533, B_534)) | r2_hidden(D_532, B_534) | ~r2_hidden(D_532, A_533))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.63/6.14  tff(c_19760, plain, (![D_532]: (r2_hidden(D_532, k1_xboole_0) | r2_hidden(D_532, '#skF_9') | ~r2_hidden(D_532, k2_tarski('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_17815, c_19727])).
% 12.63/6.14  tff(c_19854, plain, (![D_538]: (r2_hidden(D_538, '#skF_9') | ~r2_hidden(D_538, k2_tarski('#skF_8', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_17976, c_19760])).
% 12.63/6.14  tff(c_19870, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_17715, c_19854])).
% 12.63/6.14  tff(c_19879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17577, c_19870])).
% 12.63/6.14  tff(c_19881, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 12.63/6.14  tff(c_19882, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_7'), '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71])).
% 12.63/6.14  tff(c_19883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19881, c_19882])).
% 12.63/6.14  tff(c_19884, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_71])).
% 12.63/6.14  tff(c_19880, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 12.63/6.14  tff(c_23038, plain, (![A_630, C_631, B_632]: (k2_xboole_0(k2_tarski(A_630, C_631), B_632)=B_632 | ~r2_hidden(C_631, B_632) | ~r2_hidden(A_630, B_632))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.63/6.14  tff(c_34, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.63/6.14  tff(c_23103, plain, (![A_630, C_631, B_632]: (k4_xboole_0(k2_tarski(A_630, C_631), B_632)=k4_xboole_0(B_632, B_632) | ~r2_hidden(C_631, B_632) | ~r2_hidden(A_630, B_632))), inference(superposition, [status(thm), theory('equality')], [c_23038, c_34])).
% 12.63/6.14  tff(c_37589, plain, (![A_887, C_888, B_889]: (k4_xboole_0(k2_tarski(A_887, C_888), B_889)=k1_xboole_0 | ~r2_hidden(C_888, B_889) | ~r2_hidden(A_887, B_889))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_23103])).
% 12.63/6.14  tff(c_20043, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_19881, c_73])).
% 12.63/6.14  tff(c_37720, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_37589, c_20043])).
% 12.63/6.14  tff(c_37827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19884, c_19880, c_37720])).
% 12.63/6.14  tff(c_37828, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_17576])).
% 12.63/6.14  tff(c_37829, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_17576])).
% 12.63/6.14  tff(c_17539, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 12.63/6.14  tff(c_37831, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_37829, c_17539])).
% 12.63/6.14  tff(c_39123, plain, (![A_965, C_966, B_967]: (k2_xboole_0(k2_tarski(A_965, C_966), B_967)=B_967 | ~r2_hidden(C_966, B_967) | ~r2_hidden(A_965, B_967))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.63/6.14  tff(c_51676, plain, (![A_1224, C_1225, B_1226]: (k4_xboole_0(k2_tarski(A_1224, C_1225), B_1226)=k1_xboole_0 | ~r2_hidden(C_1225, B_1226) | ~r2_hidden(A_1224, B_1226))), inference(superposition, [status(thm), theory('equality')], [c_39123, c_40])).
% 12.63/6.14  tff(c_60, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.63/6.14  tff(c_37833, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17540, c_37829, c_60])).
% 12.63/6.14  tff(c_51793, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_51676, c_37833])).
% 12.63/6.14  tff(c_51879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37828, c_37831, c_51793])).
% 12.63/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.63/6.14  
% 12.63/6.14  Inference rules
% 12.63/6.14  ----------------------
% 12.63/6.14  #Ref     : 0
% 12.63/6.14  #Sup     : 13168
% 12.63/6.14  #Fact    : 0
% 12.63/6.14  #Define  : 0
% 12.63/6.14  #Split   : 13
% 12.63/6.14  #Chain   : 0
% 12.63/6.14  #Close   : 0
% 12.63/6.14  
% 12.63/6.14  Ordering : KBO
% 12.63/6.14  
% 12.63/6.14  Simplification rules
% 12.63/6.14  ----------------------
% 12.63/6.14  #Subsume      : 2874
% 12.63/6.14  #Demod        : 9585
% 12.63/6.14  #Tautology    : 5819
% 12.63/6.14  #SimpNegUnit  : 176
% 12.63/6.14  #BackRed      : 5
% 12.63/6.14  
% 12.63/6.14  #Partial instantiations: 0
% 12.63/6.14  #Strategies tried      : 1
% 12.63/6.14  
% 12.63/6.14  Timing (in seconds)
% 12.63/6.14  ----------------------
% 12.63/6.14  Preprocessing        : 0.33
% 12.63/6.14  Parsing              : 0.17
% 12.63/6.14  CNF conversion       : 0.02
% 12.63/6.14  Main loop            : 5.03
% 12.63/6.14  Inferencing          : 1.03
% 12.63/6.14  Reduction            : 2.74
% 12.63/6.14  Demodulation         : 2.38
% 12.63/6.14  BG Simplification    : 0.12
% 12.63/6.15  Subsumption          : 0.90
% 12.63/6.15  Abstraction          : 0.19
% 12.63/6.15  MUC search           : 0.00
% 12.63/6.15  Cooper               : 0.00
% 12.63/6.15  Total                : 5.39
% 12.63/6.15  Index Insertion      : 0.00
% 12.63/6.15  Index Deletion       : 0.00
% 12.63/6.15  Index Matching       : 0.00
% 12.63/6.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
