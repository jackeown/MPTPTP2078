%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:35 EST 2020

% Result     : Theorem 14.52s
% Output     : CNFRefutation 14.52s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 307 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  185 ( 574 expanded)
%              Number of equality atoms :   39 (  79 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_60,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_29990,plain,(
    ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_689,plain,(
    ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_36,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,
    ( r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | r1_xboole_0('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_180,plain,(
    r1_xboole_0('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_316,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_334,plain,(
    ! [A_68,B_69] :
      ( ~ r1_xboole_0(A_68,B_69)
      | k3_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_316])).

tff(c_350,plain,(
    k3_xboole_0('#skF_8','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_334])).

tff(c_462,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_493,plain,(
    k4_xboole_0('#skF_8',k1_xboole_0) = k4_xboole_0('#skF_8','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_462])).

tff(c_511,plain,(
    k4_xboole_0('#skF_8','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_493])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_251,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_348,plain,(
    k3_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_334])).

tff(c_496,plain,(
    k4_xboole_0('#skF_8',k1_xboole_0) = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_462])).

tff(c_512,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_496])).

tff(c_988,plain,(
    ! [A_87,B_88,C_89] : k4_xboole_0(k4_xboole_0(A_87,B_88),C_89) = k4_xboole_0(A_87,k2_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1056,plain,(
    ! [C_89] : k4_xboole_0('#skF_8',k2_xboole_0('#skF_9',C_89)) = k4_xboole_0('#skF_8',C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_988])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_254,plain,(
    r1_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_251,c_24])).

tff(c_347,plain,(
    k3_xboole_0('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_254,c_334])).

tff(c_28,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_354,plain,(
    ! [C_17] :
      ( ~ r1_xboole_0('#skF_9','#skF_8')
      | ~ r2_hidden(C_17,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_28])).

tff(c_370,plain,(
    ! [C_17] : ~ r2_hidden(C_17,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_354])).

tff(c_34,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] : k4_xboole_0(k4_xboole_0(A_24,B_25),C_26) = k4_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_558,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3619,plain,(
    ! [D_188,A_189,B_190] :
      ( r2_hidden(D_188,A_189)
      | ~ r2_hidden(D_188,k3_xboole_0(A_189,B_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_10])).

tff(c_4211,plain,(
    ! [A_201,B_202] :
      ( r2_hidden('#skF_3'(A_201,B_202),A_201)
      | r1_xboole_0(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_26,c_3619])).

tff(c_4265,plain,(
    ! [B_203] : r1_xboole_0(k1_xboole_0,B_203) ),
    inference(resolution,[status(thm)],[c_4211,c_370])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2829,plain,(
    ! [A_164,B_165,C_166] :
      ( ~ r1_xboole_0(A_164,B_165)
      | ~ r2_hidden(C_166,k3_xboole_0(B_165,A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_316])).

tff(c_2928,plain,(
    ! [A_164,B_165] :
      ( ~ r1_xboole_0(A_164,B_165)
      | k3_xboole_0(B_165,A_164) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_2829])).

tff(c_4280,plain,(
    ! [B_203] : k3_xboole_0(B_203,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4265,c_2928])).

tff(c_601,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k3_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_558])).

tff(c_4676,plain,(
    ! [A_212] : k4_xboole_0(A_212,A_212) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4280,c_601])).

tff(c_4744,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(B_25,k4_xboole_0(A_24,B_25))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4676])).

tff(c_4767,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(B_25,A_24)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4744])).

tff(c_1021,plain,(
    ! [C_89,A_87,B_88] : k2_xboole_0(C_89,k4_xboole_0(A_87,k2_xboole_0(B_88,C_89))) = k2_xboole_0(C_89,k4_xboole_0(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_34])).

tff(c_44,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1063,plain,(
    ! [A_87,B_88,B_33] : k4_xboole_0(A_87,k2_xboole_0(B_88,k4_xboole_0(k4_xboole_0(A_87,B_88),B_33))) = k3_xboole_0(k4_xboole_0(A_87,B_88),B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_988])).

tff(c_15389,plain,(
    ! [A_394,B_395,B_396] : k4_xboole_0(A_394,k2_xboole_0(B_395,k4_xboole_0(A_394,k2_xboole_0(B_395,B_396)))) = k3_xboole_0(k4_xboole_0(A_394,B_395),B_396) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1063])).

tff(c_15583,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k2_xboole_0(B_88,k4_xboole_0(A_87,B_88))) = k3_xboole_0(k4_xboole_0(A_87,B_88),B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_15389])).

tff(c_15764,plain,(
    ! [B_397,A_398] : k3_xboole_0(B_397,k4_xboole_0(A_398,B_397)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4767,c_34,c_4,c_15583])).

tff(c_1239,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_3'(A_96,B_97),k3_xboole_0(A_96,B_97))
      | r1_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1281,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_3'(A_3,B_4),k3_xboole_0(B_4,A_3))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1239])).

tff(c_15856,plain,(
    ! [A_398,B_397] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_398,B_397),B_397),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_398,B_397),B_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15764,c_1281])).

tff(c_16052,plain,(
    ! [A_399,B_400] : r1_xboole_0(k4_xboole_0(A_399,B_400),B_400) ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_15856])).

tff(c_29751,plain,(
    ! [C_531] : r1_xboole_0(k4_xboole_0('#skF_8',C_531),k2_xboole_0('#skF_9',C_531)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_16052])).

tff(c_29855,plain,(
    r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_29751])).

tff(c_29896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_689,c_29855])).

tff(c_29898,plain,(
    r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_30053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29990,c_29898])).

tff(c_30054,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_30142,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_30054])).

tff(c_86,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_101,plain,(
    ! [A_48,B_47] : r1_tarski(A_48,k2_xboole_0(B_47,A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_48])).

tff(c_29897,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_29932,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_29897,c_24])).

tff(c_30260,plain,(
    ! [A_533,C_534,B_535] :
      ( r1_xboole_0(A_533,C_534)
      | ~ r1_xboole_0(B_535,C_534)
      | ~ r1_tarski(A_533,B_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_31416,plain,(
    ! [A_566] :
      ( r1_xboole_0(A_566,'#skF_5')
      | ~ r1_tarski(A_566,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_29932,c_30260])).

tff(c_31448,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_31416])).

tff(c_31460,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_31448,c_24])).

tff(c_31466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30142,c_31460])).

tff(c_31467,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30054])).

tff(c_31497,plain,(
    ! [A_567,C_568,B_569] :
      ( r1_xboole_0(A_567,C_568)
      | ~ r1_xboole_0(B_569,C_568)
      | ~ r1_tarski(A_567,B_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34289,plain,(
    ! [A_631] :
      ( r1_xboole_0(A_631,'#skF_5')
      | ~ r1_tarski(A_631,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_29932,c_31497])).

tff(c_34327,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_34289])).

tff(c_34334,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34327,c_24])).

tff(c_34340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31467,c_34334])).

tff(c_34342,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6')
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34437,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_34342,c_56])).

tff(c_34438,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34437])).

tff(c_34341,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_34345,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_34341,c_24])).

tff(c_34936,plain,(
    ! [A_657,C_658,B_659] :
      ( r1_xboole_0(A_657,C_658)
      | ~ r1_xboole_0(B_659,C_658)
      | ~ r1_tarski(A_657,B_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_35648,plain,(
    ! [A_675] :
      ( r1_xboole_0(A_675,'#skF_5')
      | ~ r1_tarski(A_675,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_34345,c_34936])).

tff(c_35685,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_35648])).

tff(c_35702,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_35685,c_24])).

tff(c_35708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34438,c_35702])).

tff(c_35709,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_34437])).

tff(c_36498,plain,(
    ! [A_705,C_706,B_707] :
      ( r1_xboole_0(A_705,C_706)
      | ~ r1_xboole_0(B_707,C_706)
      | ~ r1_tarski(A_705,B_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38250,plain,(
    ! [A_744] :
      ( r1_xboole_0(A_744,'#skF_5')
      | ~ r1_tarski(A_744,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_34345,c_36498])).

tff(c_38282,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_38250])).

tff(c_38295,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_38282,c_24])).

tff(c_38301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35709,c_38295])).

tff(c_38303,plain,(
    ~ r1_xboole_0('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6')
    | r1_xboole_0('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38460,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38303,c_52])).

tff(c_38461,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38460])).

tff(c_38302,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_38309,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_38302,c_24])).

tff(c_38799,plain,(
    ! [A_778,C_779,B_780] :
      ( r1_xboole_0(A_778,C_779)
      | ~ r1_xboole_0(B_780,C_779)
      | ~ r1_tarski(A_778,B_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_39154,plain,(
    ! [A_798] :
      ( r1_xboole_0(A_798,'#skF_5')
      | ~ r1_tarski(A_798,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_38309,c_38799])).

tff(c_39190,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_39154])).

tff(c_39229,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_39190,c_24])).

tff(c_39236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38461,c_39229])).

tff(c_39237,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38460])).

tff(c_104,plain,(
    ! [B_47,A_48] : r1_tarski(B_47,k2_xboole_0(A_48,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_48])).

tff(c_39911,plain,(
    ! [A_819,C_820,B_821] :
      ( r1_xboole_0(A_819,C_820)
      | ~ r1_xboole_0(B_821,C_820)
      | ~ r1_tarski(A_819,B_821) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40282,plain,(
    ! [A_834] :
      ( r1_xboole_0(A_834,'#skF_5')
      | ~ r1_tarski(A_834,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_38309,c_39911])).

tff(c_40299,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_40282])).

tff(c_40312,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_40299,c_24])).

tff(c_40318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39237,c_40312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.52/6.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.52/6.63  
% 14.52/6.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.52/6.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8
% 14.52/6.63  
% 14.52/6.63  %Foreground sorts:
% 14.52/6.63  
% 14.52/6.63  
% 14.52/6.63  %Background operators:
% 14.52/6.63  
% 14.52/6.63  
% 14.52/6.63  %Foreground operators:
% 14.52/6.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.52/6.63  tff('#skF_4', type, '#skF_4': $i > $i).
% 14.52/6.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.52/6.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.52/6.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.52/6.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.52/6.63  tff('#skF_7', type, '#skF_7': $i).
% 14.52/6.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.52/6.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.52/6.63  tff('#skF_10', type, '#skF_10': $i).
% 14.52/6.63  tff('#skF_5', type, '#skF_5': $i).
% 14.52/6.63  tff('#skF_6', type, '#skF_6': $i).
% 14.52/6.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.52/6.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.52/6.63  tff('#skF_9', type, '#skF_9': $i).
% 14.52/6.63  tff('#skF_8', type, '#skF_8': $i).
% 14.52/6.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.52/6.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.52/6.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.52/6.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.52/6.63  
% 14.52/6.66  tff(f_104, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 14.52/6.66  tff(f_71, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.52/6.66  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.52/6.66  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.52/6.66  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 14.52/6.66  tff(f_73, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.52/6.66  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.52/6.66  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.52/6.66  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.52/6.66  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.52/6.66  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.52/6.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.52/6.66  tff(f_87, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.52/6.66  tff(f_85, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 14.52/6.66  tff(c_60, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.52/6.66  tff(c_29990, plain, (~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_60])).
% 14.52/6.66  tff(c_58, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.52/6.66  tff(c_689, plain, (~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_58])).
% 14.52/6.66  tff(c_36, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.52/6.66  tff(c_50, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | r1_xboole_0('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.52/6.66  tff(c_180, plain, (r1_xboole_0('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_50])).
% 14.52/6.66  tff(c_30, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.52/6.66  tff(c_316, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.52/6.66  tff(c_334, plain, (![A_68, B_69]: (~r1_xboole_0(A_68, B_69) | k3_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_316])).
% 14.52/6.66  tff(c_350, plain, (k3_xboole_0('#skF_8', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_180, c_334])).
% 14.52/6.66  tff(c_462, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.52/6.66  tff(c_493, plain, (k4_xboole_0('#skF_8', k1_xboole_0)=k4_xboole_0('#skF_8', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_350, c_462])).
% 14.52/6.66  tff(c_511, plain, (k4_xboole_0('#skF_8', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_493])).
% 14.52/6.66  tff(c_54, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.52/6.66  tff(c_251, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_54])).
% 14.52/6.66  tff(c_348, plain, (k3_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_334])).
% 14.52/6.66  tff(c_496, plain, (k4_xboole_0('#skF_8', k1_xboole_0)=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_348, c_462])).
% 14.52/6.66  tff(c_512, plain, (k4_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_496])).
% 14.52/6.66  tff(c_988, plain, (![A_87, B_88, C_89]: (k4_xboole_0(k4_xboole_0(A_87, B_88), C_89)=k4_xboole_0(A_87, k2_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.52/6.66  tff(c_1056, plain, (![C_89]: (k4_xboole_0('#skF_8', k2_xboole_0('#skF_9', C_89))=k4_xboole_0('#skF_8', C_89))), inference(superposition, [status(thm), theory('equality')], [c_512, c_988])).
% 14.52/6.66  tff(c_24, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.52/6.66  tff(c_254, plain, (r1_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_251, c_24])).
% 14.52/6.66  tff(c_347, plain, (k3_xboole_0('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_254, c_334])).
% 14.52/6.66  tff(c_28, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.52/6.66  tff(c_354, plain, (![C_17]: (~r1_xboole_0('#skF_9', '#skF_8') | ~r2_hidden(C_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_347, c_28])).
% 14.52/6.66  tff(c_370, plain, (![C_17]: (~r2_hidden(C_17, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_354])).
% 14.52/6.66  tff(c_34, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.52/6.66  tff(c_38, plain, (![A_24, B_25, C_26]: (k4_xboole_0(k4_xboole_0(A_24, B_25), C_26)=k4_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.52/6.66  tff(c_26, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.52/6.66  tff(c_558, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.52/6.66  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.52/6.66  tff(c_3619, plain, (![D_188, A_189, B_190]: (r2_hidden(D_188, A_189) | ~r2_hidden(D_188, k3_xboole_0(A_189, B_190)))), inference(superposition, [status(thm), theory('equality')], [c_558, c_10])).
% 14.52/6.66  tff(c_4211, plain, (![A_201, B_202]: (r2_hidden('#skF_3'(A_201, B_202), A_201) | r1_xboole_0(A_201, B_202))), inference(resolution, [status(thm)], [c_26, c_3619])).
% 14.52/6.66  tff(c_4265, plain, (![B_203]: (r1_xboole_0(k1_xboole_0, B_203))), inference(resolution, [status(thm)], [c_4211, c_370])).
% 14.52/6.66  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.52/6.66  tff(c_2829, plain, (![A_164, B_165, C_166]: (~r1_xboole_0(A_164, B_165) | ~r2_hidden(C_166, k3_xboole_0(B_165, A_164)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_316])).
% 14.52/6.66  tff(c_2928, plain, (![A_164, B_165]: (~r1_xboole_0(A_164, B_165) | k3_xboole_0(B_165, A_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_2829])).
% 14.52/6.66  tff(c_4280, plain, (![B_203]: (k3_xboole_0(B_203, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4265, c_2928])).
% 14.52/6.66  tff(c_601, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k3_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_558])).
% 14.52/6.66  tff(c_4676, plain, (![A_212]: (k4_xboole_0(A_212, A_212)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4280, c_601])).
% 14.52/6.66  tff(c_4744, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(B_25, k4_xboole_0(A_24, B_25)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_4676])).
% 14.52/6.66  tff(c_4767, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(B_25, A_24))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4744])).
% 14.52/6.66  tff(c_1021, plain, (![C_89, A_87, B_88]: (k2_xboole_0(C_89, k4_xboole_0(A_87, k2_xboole_0(B_88, C_89)))=k2_xboole_0(C_89, k4_xboole_0(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_988, c_34])).
% 14.52/6.66  tff(c_44, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.52/6.66  tff(c_1063, plain, (![A_87, B_88, B_33]: (k4_xboole_0(A_87, k2_xboole_0(B_88, k4_xboole_0(k4_xboole_0(A_87, B_88), B_33)))=k3_xboole_0(k4_xboole_0(A_87, B_88), B_33))), inference(superposition, [status(thm), theory('equality')], [c_44, c_988])).
% 14.52/6.66  tff(c_15389, plain, (![A_394, B_395, B_396]: (k4_xboole_0(A_394, k2_xboole_0(B_395, k4_xboole_0(A_394, k2_xboole_0(B_395, B_396))))=k3_xboole_0(k4_xboole_0(A_394, B_395), B_396))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1063])).
% 14.52/6.66  tff(c_15583, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k2_xboole_0(B_88, k4_xboole_0(A_87, B_88)))=k3_xboole_0(k4_xboole_0(A_87, B_88), B_88))), inference(superposition, [status(thm), theory('equality')], [c_1021, c_15389])).
% 14.52/6.66  tff(c_15764, plain, (![B_397, A_398]: (k3_xboole_0(B_397, k4_xboole_0(A_398, B_397))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4767, c_34, c_4, c_15583])).
% 14.52/6.66  tff(c_1239, plain, (![A_96, B_97]: (r2_hidden('#skF_3'(A_96, B_97), k3_xboole_0(A_96, B_97)) | r1_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.52/6.66  tff(c_1281, plain, (![A_3, B_4]: (r2_hidden('#skF_3'(A_3, B_4), k3_xboole_0(B_4, A_3)) | r1_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1239])).
% 14.52/6.66  tff(c_15856, plain, (![A_398, B_397]: (r2_hidden('#skF_3'(k4_xboole_0(A_398, B_397), B_397), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_398, B_397), B_397))), inference(superposition, [status(thm), theory('equality')], [c_15764, c_1281])).
% 14.52/6.66  tff(c_16052, plain, (![A_399, B_400]: (r1_xboole_0(k4_xboole_0(A_399, B_400), B_400))), inference(negUnitSimplification, [status(thm)], [c_370, c_15856])).
% 14.52/6.66  tff(c_29751, plain, (![C_531]: (r1_xboole_0(k4_xboole_0('#skF_8', C_531), k2_xboole_0('#skF_9', C_531)))), inference(superposition, [status(thm), theory('equality')], [c_1056, c_16052])).
% 14.52/6.66  tff(c_29855, plain, (r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_511, c_29751])).
% 14.52/6.66  tff(c_29896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_689, c_29855])).
% 14.52/6.66  tff(c_29898, plain, (r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_58])).
% 14.52/6.66  tff(c_30053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29990, c_29898])).
% 14.52/6.66  tff(c_30054, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 14.52/6.66  tff(c_30142, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_30054])).
% 14.52/6.66  tff(c_86, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.52/6.66  tff(c_48, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.52/6.66  tff(c_101, plain, (![A_48, B_47]: (r1_tarski(A_48, k2_xboole_0(B_47, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_48])).
% 14.52/6.66  tff(c_29897, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 14.52/6.66  tff(c_29932, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_29897, c_24])).
% 14.52/6.66  tff(c_30260, plain, (![A_533, C_534, B_535]: (r1_xboole_0(A_533, C_534) | ~r1_xboole_0(B_535, C_534) | ~r1_tarski(A_533, B_535))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.52/6.66  tff(c_31416, plain, (![A_566]: (r1_xboole_0(A_566, '#skF_5') | ~r1_tarski(A_566, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_29932, c_30260])).
% 14.52/6.66  tff(c_31448, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_101, c_31416])).
% 14.52/6.66  tff(c_31460, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_31448, c_24])).
% 14.52/6.66  tff(c_31466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30142, c_31460])).
% 14.52/6.66  tff(c_31467, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_30054])).
% 14.52/6.66  tff(c_31497, plain, (![A_567, C_568, B_569]: (r1_xboole_0(A_567, C_568) | ~r1_xboole_0(B_569, C_568) | ~r1_tarski(A_567, B_569))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.52/6.66  tff(c_34289, plain, (![A_631]: (r1_xboole_0(A_631, '#skF_5') | ~r1_tarski(A_631, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_29932, c_31497])).
% 14.52/6.66  tff(c_34327, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_34289])).
% 14.52/6.66  tff(c_34334, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34327, c_24])).
% 14.52/6.66  tff(c_34340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31467, c_34334])).
% 14.52/6.66  tff(c_34342, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_54])).
% 14.52/6.66  tff(c_56, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6') | r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.52/6.66  tff(c_34437, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_34342, c_56])).
% 14.52/6.66  tff(c_34438, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_34437])).
% 14.52/6.66  tff(c_34341, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 14.52/6.66  tff(c_34345, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_34341, c_24])).
% 14.52/6.66  tff(c_34936, plain, (![A_657, C_658, B_659]: (r1_xboole_0(A_657, C_658) | ~r1_xboole_0(B_659, C_658) | ~r1_tarski(A_657, B_659))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.52/6.66  tff(c_35648, plain, (![A_675]: (r1_xboole_0(A_675, '#skF_5') | ~r1_tarski(A_675, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_34345, c_34936])).
% 14.52/6.66  tff(c_35685, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_35648])).
% 14.52/6.66  tff(c_35702, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_35685, c_24])).
% 14.52/6.66  tff(c_35708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34438, c_35702])).
% 14.52/6.66  tff(c_35709, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_34437])).
% 14.52/6.66  tff(c_36498, plain, (![A_705, C_706, B_707]: (r1_xboole_0(A_705, C_706) | ~r1_xboole_0(B_707, C_706) | ~r1_tarski(A_705, B_707))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.52/6.66  tff(c_38250, plain, (![A_744]: (r1_xboole_0(A_744, '#skF_5') | ~r1_tarski(A_744, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_34345, c_36498])).
% 14.52/6.66  tff(c_38282, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_101, c_38250])).
% 14.52/6.66  tff(c_38295, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_38282, c_24])).
% 14.52/6.66  tff(c_38301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35709, c_38295])).
% 14.52/6.66  tff(c_38303, plain, (~r1_xboole_0('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_50])).
% 14.52/6.66  tff(c_52, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6') | r1_xboole_0('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.52/6.66  tff(c_38460, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38303, c_52])).
% 14.52/6.66  tff(c_38461, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_38460])).
% 14.52/6.66  tff(c_38302, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 14.52/6.66  tff(c_38309, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_38302, c_24])).
% 14.52/6.66  tff(c_38799, plain, (![A_778, C_779, B_780]: (r1_xboole_0(A_778, C_779) | ~r1_xboole_0(B_780, C_779) | ~r1_tarski(A_778, B_780))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.52/6.66  tff(c_39154, plain, (![A_798]: (r1_xboole_0(A_798, '#skF_5') | ~r1_tarski(A_798, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_38309, c_38799])).
% 14.52/6.66  tff(c_39190, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_39154])).
% 14.52/6.66  tff(c_39229, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_39190, c_24])).
% 14.52/6.66  tff(c_39236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38461, c_39229])).
% 14.52/6.66  tff(c_39237, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_38460])).
% 14.52/6.66  tff(c_104, plain, (![B_47, A_48]: (r1_tarski(B_47, k2_xboole_0(A_48, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_48])).
% 14.52/6.66  tff(c_39911, plain, (![A_819, C_820, B_821]: (r1_xboole_0(A_819, C_820) | ~r1_xboole_0(B_821, C_820) | ~r1_tarski(A_819, B_821))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.52/6.66  tff(c_40282, plain, (![A_834]: (r1_xboole_0(A_834, '#skF_5') | ~r1_tarski(A_834, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_38309, c_39911])).
% 14.52/6.66  tff(c_40299, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_104, c_40282])).
% 14.52/6.66  tff(c_40312, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_40299, c_24])).
% 14.52/6.66  tff(c_40318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39237, c_40312])).
% 14.52/6.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.52/6.66  
% 14.52/6.66  Inference rules
% 14.52/6.66  ----------------------
% 14.52/6.66  #Ref     : 0
% 14.52/6.66  #Sup     : 10141
% 14.52/6.66  #Fact    : 0
% 14.52/6.66  #Define  : 0
% 14.52/6.66  #Split   : 27
% 14.52/6.66  #Chain   : 0
% 14.52/6.66  #Close   : 0
% 14.52/6.66  
% 14.52/6.66  Ordering : KBO
% 14.52/6.66  
% 14.52/6.66  Simplification rules
% 14.52/6.66  ----------------------
% 14.52/6.66  #Subsume      : 1259
% 14.52/6.66  #Demod        : 9623
% 14.52/6.66  #Tautology    : 5013
% 14.52/6.66  #SimpNegUnit  : 323
% 14.52/6.66  #BackRed      : 14
% 14.52/6.66  
% 14.52/6.66  #Partial instantiations: 0
% 14.52/6.66  #Strategies tried      : 1
% 14.52/6.66  
% 14.52/6.66  Timing (in seconds)
% 14.52/6.66  ----------------------
% 14.52/6.66  Preprocessing        : 0.30
% 14.52/6.66  Parsing              : 0.16
% 14.52/6.66  CNF conversion       : 0.02
% 14.52/6.66  Main loop            : 5.52
% 14.52/6.66  Inferencing          : 1.08
% 14.52/6.66  Reduction            : 2.87
% 14.52/6.66  Demodulation         : 2.39
% 14.52/6.66  BG Simplification    : 0.12
% 14.52/6.66  Subsumption          : 1.10
% 14.52/6.66  Abstraction          : 0.17
% 14.52/6.66  MUC search           : 0.00
% 14.52/6.66  Cooper               : 0.00
% 14.52/6.66  Total                : 5.87
% 14.52/6.66  Index Insertion      : 0.00
% 14.52/6.66  Index Deletion       : 0.00
% 14.52/6.66  Index Matching       : 0.00
% 14.52/6.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
