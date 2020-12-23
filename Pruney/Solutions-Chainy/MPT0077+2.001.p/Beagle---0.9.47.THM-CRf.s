%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:35 EST 2020

% Result     : Theorem 18.19s
% Output     : CNFRefutation 18.40s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 349 expanded)
%              Number of leaves         :   35 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 603 expanded)
%              Number of equality atoms :   54 ( 113 expanded)
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

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_58,plain,
    ( r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2009,plain,(
    ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_277,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_30,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_343,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1791,plain,(
    ! [A_115,B_116] :
      ( ~ r1_xboole_0(A_115,B_116)
      | k3_xboole_0(A_115,B_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_1810,plain,(
    k3_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_277,c_1791])).

tff(c_2120,plain,(
    ! [A_127,B_128] : k2_xboole_0(k3_xboole_0(A_127,B_128),k4_xboole_0(A_127,B_128)) = A_127 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2141,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_8','#skF_9')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1810,c_2120])).

tff(c_34,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_176,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(resolution,[status(thm)],[c_34,c_164])).

tff(c_2475,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2141,c_176])).

tff(c_40,plain,(
    ! [A_26,B_27,C_28] : k4_xboole_0(k4_xboole_0(A_26,B_27),C_28) = k4_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_107,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_122,plain,(
    ! [A_48,B_47] : r1_tarski(A_48,k2_xboole_0(B_47,A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_48])).

tff(c_2126,plain,(
    ! [A_127,B_128] : r1_tarski(k4_xboole_0(A_127,B_128),A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_2120,c_122])).

tff(c_50,plain,
    ( r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | r1_xboole_0('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156,plain,(
    r1_xboole_0('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2623,plain,(
    ! [A_146,C_147,B_148] :
      ( r1_xboole_0(A_146,C_147)
      | ~ r1_xboole_0(B_148,C_147)
      | ~ r1_tarski(A_146,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2713,plain,(
    ! [A_151] :
      ( r1_xboole_0(A_151,'#skF_10')
      | ~ r1_tarski(A_151,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_156,c_2623])).

tff(c_354,plain,(
    ! [A_60,B_61] :
      ( ~ r1_xboole_0(A_60,B_61)
      | k3_xboole_0(A_60,B_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_3321,plain,(
    ! [A_172] :
      ( k3_xboole_0(A_172,'#skF_10') = k1_xboole_0
      | ~ r1_tarski(A_172,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2713,c_354])).

tff(c_4126,plain,(
    ! [B_201] : k3_xboole_0(k4_xboole_0('#skF_8',B_201),'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2126,c_3321])).

tff(c_44,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4149,plain,(
    ! [B_201] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_8',B_201),'#skF_10')) = k4_xboole_0('#skF_8',B_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_4126,c_44])).

tff(c_61958,plain,(
    ! [B_969] : k4_xboole_0('#skF_8',k2_xboole_0(B_969,'#skF_10')) = k4_xboole_0('#skF_8',B_969) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_40,c_4149])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_280,plain,(
    r1_xboole_0('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_277,c_24])).

tff(c_365,plain,(
    ! [A_63,B_64] :
      ( ~ r1_xboole_0(A_63,B_64)
      | k3_xboole_0(A_63,B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_378,plain,(
    k3_xboole_0('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_365])).

tff(c_28,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_385,plain,(
    ! [C_17] :
      ( ~ r1_xboole_0('#skF_9','#skF_8')
      | ~ r2_hidden(C_17,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_28])).

tff(c_401,plain,(
    ! [C_17] : ~ r2_hidden(C_17,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_385])).

tff(c_908,plain,(
    ! [A_84,B_85] : k2_xboole_0(k3_xboole_0(A_84,B_85),k4_xboole_0(A_84,B_85)) = A_84 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_959,plain,(
    ! [A_86,B_87] : r1_tarski(k3_xboole_0(A_86,B_87),A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_48])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1215,plain,(
    ! [A_97,B_98] : k2_xboole_0(k3_xboole_0(A_97,B_98),A_97) = A_97 ),
    inference(resolution,[status(thm)],[c_959,c_32])).

tff(c_177,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_34,c_164])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_186,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_2])).

tff(c_1229,plain,(
    ! [B_98] : k3_xboole_0(k1_xboole_0,B_98) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_186])).

tff(c_1732,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_3'(A_112,B_113),k3_xboole_0(A_112,B_113))
      | r1_xboole_0(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1744,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_98),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_1732])).

tff(c_1765,plain,(
    ! [B_98] : r1_xboole_0(k1_xboole_0,B_98) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_1744])).

tff(c_38,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_212,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_323,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k3_xboole_0(A_59,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_212])).

tff(c_333,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_38])).

tff(c_358,plain,(
    ! [C_17] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_17,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_28])).

tff(c_363,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_1776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_363])).

tff(c_1777,plain,(
    ! [C_17] : ~ r2_hidden(C_17,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_36,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2168,plain,(
    ! [A_129,B_130] : r1_tarski(k3_xboole_0(A_129,B_130),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_2120,c_48])).

tff(c_2252,plain,(
    ! [A_135,B_136] : k2_xboole_0(k3_xboole_0(A_135,B_136),A_135) = A_135 ),
    inference(resolution,[status(thm)],[c_2168,c_32])).

tff(c_2320,plain,(
    ! [B_137] : k3_xboole_0(k1_xboole_0,B_137) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2252,c_186])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2344,plain,(
    ! [B_137] : k3_xboole_0(B_137,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2320,c_4])).

tff(c_227,plain,(
    ! [A_25] : k4_xboole_0(A_25,A_25) = k3_xboole_0(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_212])).

tff(c_2366,plain,(
    ! [A_25] : k4_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_227])).

tff(c_2855,plain,(
    ! [A_158,B_159,C_160] : k4_xboole_0(k4_xboole_0(A_158,B_159),C_160) = k4_xboole_0(A_158,k2_xboole_0(B_159,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2913,plain,(
    ! [A_158,B_159] : k4_xboole_0(A_158,k2_xboole_0(B_159,k4_xboole_0(A_158,B_159))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2366,c_2855])).

tff(c_2937,plain,(
    ! [A_158,B_159] : k4_xboole_0(A_158,k2_xboole_0(B_159,A_158)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2913])).

tff(c_2880,plain,(
    ! [C_160,A_158,B_159] : k2_xboole_0(C_160,k4_xboole_0(A_158,k2_xboole_0(B_159,C_160))) = k2_xboole_0(C_160,k4_xboole_0(A_158,B_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2855,c_36])).

tff(c_42,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2920,plain,(
    ! [A_158,B_159,B_30] : k4_xboole_0(A_158,k2_xboole_0(B_159,k4_xboole_0(k4_xboole_0(A_158,B_159),B_30))) = k3_xboole_0(k4_xboole_0(A_158,B_159),B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2855])).

tff(c_15842,plain,(
    ! [A_393,B_394,B_395] : k4_xboole_0(A_393,k2_xboole_0(B_394,k4_xboole_0(A_393,k2_xboole_0(B_394,B_395)))) = k3_xboole_0(k4_xboole_0(A_393,B_394),B_395) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2920])).

tff(c_16076,plain,(
    ! [A_158,B_159] : k4_xboole_0(A_158,k2_xboole_0(B_159,k4_xboole_0(A_158,B_159))) = k3_xboole_0(k4_xboole_0(A_158,B_159),B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2880,c_15842])).

tff(c_16219,plain,(
    ! [B_396,A_397] : k3_xboole_0(B_396,k4_xboole_0(A_397,B_396)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2937,c_36,c_4,c_16076])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16378,plain,(
    ! [B_396,A_397] :
      ( r2_hidden('#skF_3'(B_396,k4_xboole_0(A_397,B_396)),k1_xboole_0)
      | r1_xboole_0(B_396,k4_xboole_0(A_397,B_396)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16219,c_26])).

tff(c_16522,plain,(
    ! [B_396,A_397] : r1_xboole_0(B_396,k4_xboole_0(A_397,B_396)) ),
    inference(negUnitSimplification,[status(thm)],[c_1777,c_16378])).

tff(c_63847,plain,(
    ! [B_976] : r1_xboole_0(k2_xboole_0(B_976,'#skF_10'),k4_xboole_0('#skF_8',B_976)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61958,c_16522])).

tff(c_63931,plain,(
    r1_xboole_0(k2_xboole_0('#skF_9','#skF_10'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2475,c_63847])).

tff(c_64376,plain,(
    r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_63931,c_24])).

tff(c_64383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2009,c_64376])).

tff(c_64385,plain,(
    r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_60,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_8',k2_xboole_0('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64401,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64385,c_60])).

tff(c_64402,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_64401])).

tff(c_64384,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_64392,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_64384,c_24])).

tff(c_64794,plain,(
    ! [A_991,C_992,B_993] :
      ( r1_xboole_0(A_991,C_992)
      | ~ r1_xboole_0(B_993,C_992)
      | ~ r1_tarski(A_991,B_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_67003,plain,(
    ! [A_1062] :
      ( r1_xboole_0(A_1062,'#skF_5')
      | ~ r1_tarski(A_1062,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_64392,c_64794])).

tff(c_67038,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_67003])).

tff(c_67057,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_67038,c_24])).

tff(c_67063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64402,c_67057])).

tff(c_67064,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64401])).

tff(c_67500,plain,(
    ! [A_1078,C_1079,B_1080] :
      ( r1_xboole_0(A_1078,C_1079)
      | ~ r1_xboole_0(B_1080,C_1079)
      | ~ r1_tarski(A_1078,B_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_69936,plain,(
    ! [A_1155] :
      ( r1_xboole_0(A_1155,'#skF_5')
      | ~ r1_tarski(A_1155,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_64392,c_67500])).

tff(c_69970,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_69936])).

tff(c_69981,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_69970,c_24])).

tff(c_69987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67064,c_69981])).

tff(c_69989,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6')
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70901,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_69989,c_56])).

tff(c_70902,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70901])).

tff(c_69988,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_70030,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_69988,c_24])).

tff(c_71564,plain,(
    ! [A_1224,C_1225,B_1226] :
      ( r1_xboole_0(A_1224,C_1225)
      | ~ r1_xboole_0(B_1226,C_1225)
      | ~ r1_tarski(A_1224,B_1226) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_72390,plain,(
    ! [A_1257] :
      ( r1_xboole_0(A_1257,'#skF_5')
      | ~ r1_tarski(A_1257,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_70030,c_71564])).

tff(c_72425,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_72390])).

tff(c_72444,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72425,c_24])).

tff(c_72450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70902,c_72444])).

tff(c_72451,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70901])).

tff(c_73058,plain,(
    ! [A_1282,C_1283,B_1284] :
      ( r1_xboole_0(A_1282,C_1283)
      | ~ r1_xboole_0(B_1284,C_1283)
      | ~ r1_tarski(A_1282,B_1284) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_73486,plain,(
    ! [A_1305] :
      ( r1_xboole_0(A_1305,'#skF_5')
      | ~ r1_tarski(A_1305,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_70030,c_73058])).

tff(c_73520,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_73486])).

tff(c_73528,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_73520,c_24])).

tff(c_73533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72451,c_73528])).

tff(c_73535,plain,(
    ~ r1_xboole_0('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6')
    | r1_xboole_0('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_73750,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_73535,c_52])).

tff(c_73751,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_73750])).

tff(c_73534,plain,(
    r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_73538,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_73534,c_24])).

tff(c_74182,plain,(
    ! [A_1343,C_1344,B_1345] :
      ( r1_xboole_0(A_1343,C_1344)
      | ~ r1_xboole_0(B_1345,C_1344)
      | ~ r1_tarski(A_1343,B_1345) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74652,plain,(
    ! [A_1363] :
      ( r1_xboole_0(A_1363,'#skF_5')
      | ~ r1_tarski(A_1363,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_73538,c_74182])).

tff(c_74687,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_74652])).

tff(c_74698,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74687,c_24])).

tff(c_74703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73751,c_74698])).

tff(c_74704,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_73750])).

tff(c_75263,plain,(
    ! [A_1390,C_1391,B_1392] :
      ( r1_xboole_0(A_1390,C_1391)
      | ~ r1_xboole_0(B_1392,C_1391)
      | ~ r1_tarski(A_1390,B_1392) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_75666,plain,(
    ! [A_1412] :
      ( r1_xboole_0(A_1412,'#skF_5')
      | ~ r1_tarski(A_1412,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_73538,c_75263])).

tff(c_75700,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_75666])).

tff(c_75707,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_75700,c_24])).

tff(c_75712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74704,c_75707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.19/10.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.19/10.35  
% 18.19/10.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.19/10.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8
% 18.19/10.35  
% 18.19/10.35  %Foreground sorts:
% 18.19/10.35  
% 18.19/10.35  
% 18.19/10.35  %Background operators:
% 18.19/10.35  
% 18.19/10.35  
% 18.19/10.35  %Foreground operators:
% 18.19/10.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.19/10.35  tff('#skF_4', type, '#skF_4': $i > $i).
% 18.19/10.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.19/10.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.19/10.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.19/10.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.19/10.35  tff('#skF_7', type, '#skF_7': $i).
% 18.19/10.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.19/10.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.19/10.35  tff('#skF_10', type, '#skF_10': $i).
% 18.19/10.35  tff('#skF_5', type, '#skF_5': $i).
% 18.19/10.35  tff('#skF_6', type, '#skF_6': $i).
% 18.19/10.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.19/10.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.19/10.35  tff('#skF_9', type, '#skF_9': $i).
% 18.19/10.35  tff('#skF_8', type, '#skF_8': $i).
% 18.19/10.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.19/10.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.19/10.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.19/10.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.19/10.35  
% 18.40/10.38  tff(f_106, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 18.40/10.38  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 18.40/10.38  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 18.40/10.38  tff(f_81, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 18.40/10.38  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.40/10.38  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.40/10.38  tff(f_77, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 18.40/10.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.40/10.38  tff(f_89, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.40/10.38  tff(f_87, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 18.40/10.38  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 18.40/10.38  tff(f_75, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 18.40/10.38  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.40/10.38  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 18.40/10.38  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.40/10.38  tff(c_58, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.40/10.38  tff(c_2009, plain, (~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_58])).
% 18.40/10.38  tff(c_54, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.40/10.38  tff(c_277, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_54])).
% 18.40/10.38  tff(c_30, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.40/10.38  tff(c_343, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.40/10.38  tff(c_1791, plain, (![A_115, B_116]: (~r1_xboole_0(A_115, B_116) | k3_xboole_0(A_115, B_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_343])).
% 18.40/10.38  tff(c_1810, plain, (k3_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_277, c_1791])).
% 18.40/10.38  tff(c_2120, plain, (![A_127, B_128]: (k2_xboole_0(k3_xboole_0(A_127, B_128), k4_xboole_0(A_127, B_128))=A_127)), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.40/10.38  tff(c_2141, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_8', '#skF_9'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1810, c_2120])).
% 18.40/10.38  tff(c_34, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.40/10.38  tff(c_164, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.40/10.38  tff(c_176, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(resolution, [status(thm)], [c_34, c_164])).
% 18.40/10.38  tff(c_2475, plain, (k4_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2141, c_176])).
% 18.40/10.38  tff(c_40, plain, (![A_26, B_27, C_28]: (k4_xboole_0(k4_xboole_0(A_26, B_27), C_28)=k4_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.40/10.38  tff(c_107, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.40/10.38  tff(c_48, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.40/10.38  tff(c_122, plain, (![A_48, B_47]: (r1_tarski(A_48, k2_xboole_0(B_47, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_48])).
% 18.40/10.38  tff(c_2126, plain, (![A_127, B_128]: (r1_tarski(k4_xboole_0(A_127, B_128), A_127))), inference(superposition, [status(thm), theory('equality')], [c_2120, c_122])).
% 18.40/10.38  tff(c_50, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | r1_xboole_0('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.40/10.38  tff(c_156, plain, (r1_xboole_0('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_50])).
% 18.40/10.38  tff(c_2623, plain, (![A_146, C_147, B_148]: (r1_xboole_0(A_146, C_147) | ~r1_xboole_0(B_148, C_147) | ~r1_tarski(A_146, B_148))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_2713, plain, (![A_151]: (r1_xboole_0(A_151, '#skF_10') | ~r1_tarski(A_151, '#skF_8'))), inference(resolution, [status(thm)], [c_156, c_2623])).
% 18.40/10.38  tff(c_354, plain, (![A_60, B_61]: (~r1_xboole_0(A_60, B_61) | k3_xboole_0(A_60, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_343])).
% 18.40/10.38  tff(c_3321, plain, (![A_172]: (k3_xboole_0(A_172, '#skF_10')=k1_xboole_0 | ~r1_tarski(A_172, '#skF_8'))), inference(resolution, [status(thm)], [c_2713, c_354])).
% 18.40/10.38  tff(c_4126, plain, (![B_201]: (k3_xboole_0(k4_xboole_0('#skF_8', B_201), '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2126, c_3321])).
% 18.40/10.38  tff(c_44, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.40/10.38  tff(c_4149, plain, (![B_201]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_8', B_201), '#skF_10'))=k4_xboole_0('#skF_8', B_201))), inference(superposition, [status(thm), theory('equality')], [c_4126, c_44])).
% 18.40/10.38  tff(c_61958, plain, (![B_969]: (k4_xboole_0('#skF_8', k2_xboole_0(B_969, '#skF_10'))=k4_xboole_0('#skF_8', B_969))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_40, c_4149])).
% 18.40/10.38  tff(c_24, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.40/10.38  tff(c_280, plain, (r1_xboole_0('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_277, c_24])).
% 18.40/10.38  tff(c_365, plain, (![A_63, B_64]: (~r1_xboole_0(A_63, B_64) | k3_xboole_0(A_63, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_343])).
% 18.40/10.38  tff(c_378, plain, (k3_xboole_0('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_365])).
% 18.40/10.38  tff(c_28, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.40/10.38  tff(c_385, plain, (![C_17]: (~r1_xboole_0('#skF_9', '#skF_8') | ~r2_hidden(C_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_378, c_28])).
% 18.40/10.38  tff(c_401, plain, (![C_17]: (~r2_hidden(C_17, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_385])).
% 18.40/10.38  tff(c_908, plain, (![A_84, B_85]: (k2_xboole_0(k3_xboole_0(A_84, B_85), k4_xboole_0(A_84, B_85))=A_84)), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.40/10.38  tff(c_959, plain, (![A_86, B_87]: (r1_tarski(k3_xboole_0(A_86, B_87), A_86))), inference(superposition, [status(thm), theory('equality')], [c_908, c_48])).
% 18.40/10.38  tff(c_32, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.40/10.38  tff(c_1215, plain, (![A_97, B_98]: (k2_xboole_0(k3_xboole_0(A_97, B_98), A_97)=A_97)), inference(resolution, [status(thm)], [c_959, c_32])).
% 18.40/10.38  tff(c_177, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(resolution, [status(thm)], [c_34, c_164])).
% 18.40/10.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.40/10.38  tff(c_186, plain, (![A_53]: (k2_xboole_0(A_53, k1_xboole_0)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_177, c_2])).
% 18.40/10.38  tff(c_1229, plain, (![B_98]: (k3_xboole_0(k1_xboole_0, B_98)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1215, c_186])).
% 18.40/10.38  tff(c_1732, plain, (![A_112, B_113]: (r2_hidden('#skF_3'(A_112, B_113), k3_xboole_0(A_112, B_113)) | r1_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.40/10.38  tff(c_1744, plain, (![B_98]: (r2_hidden('#skF_3'(k1_xboole_0, B_98), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_98))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_1732])).
% 18.40/10.38  tff(c_1765, plain, (![B_98]: (r1_xboole_0(k1_xboole_0, B_98))), inference(negUnitSimplification, [status(thm)], [c_401, c_1744])).
% 18.40/10.38  tff(c_38, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.40/10.38  tff(c_212, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 18.40/10.38  tff(c_323, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k3_xboole_0(A_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_212])).
% 18.40/10.38  tff(c_333, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_323, c_38])).
% 18.40/10.38  tff(c_358, plain, (![C_17]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_333, c_28])).
% 18.40/10.38  tff(c_363, plain, (~r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_358])).
% 18.40/10.38  tff(c_1776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1765, c_363])).
% 18.40/10.38  tff(c_1777, plain, (![C_17]: (~r2_hidden(C_17, k1_xboole_0))), inference(splitRight, [status(thm)], [c_358])).
% 18.40/10.38  tff(c_36, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.40/10.38  tff(c_2168, plain, (![A_129, B_130]: (r1_tarski(k3_xboole_0(A_129, B_130), A_129))), inference(superposition, [status(thm), theory('equality')], [c_2120, c_48])).
% 18.40/10.38  tff(c_2252, plain, (![A_135, B_136]: (k2_xboole_0(k3_xboole_0(A_135, B_136), A_135)=A_135)), inference(resolution, [status(thm)], [c_2168, c_32])).
% 18.40/10.38  tff(c_2320, plain, (![B_137]: (k3_xboole_0(k1_xboole_0, B_137)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2252, c_186])).
% 18.40/10.38  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.40/10.38  tff(c_2344, plain, (![B_137]: (k3_xboole_0(B_137, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2320, c_4])).
% 18.40/10.38  tff(c_227, plain, (![A_25]: (k4_xboole_0(A_25, A_25)=k3_xboole_0(A_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_212])).
% 18.40/10.38  tff(c_2366, plain, (![A_25]: (k4_xboole_0(A_25, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2344, c_227])).
% 18.40/10.38  tff(c_2855, plain, (![A_158, B_159, C_160]: (k4_xboole_0(k4_xboole_0(A_158, B_159), C_160)=k4_xboole_0(A_158, k2_xboole_0(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.40/10.38  tff(c_2913, plain, (![A_158, B_159]: (k4_xboole_0(A_158, k2_xboole_0(B_159, k4_xboole_0(A_158, B_159)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2366, c_2855])).
% 18.40/10.38  tff(c_2937, plain, (![A_158, B_159]: (k4_xboole_0(A_158, k2_xboole_0(B_159, A_158))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2913])).
% 18.40/10.38  tff(c_2880, plain, (![C_160, A_158, B_159]: (k2_xboole_0(C_160, k4_xboole_0(A_158, k2_xboole_0(B_159, C_160)))=k2_xboole_0(C_160, k4_xboole_0(A_158, B_159)))), inference(superposition, [status(thm), theory('equality')], [c_2855, c_36])).
% 18.40/10.38  tff(c_42, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 18.40/10.38  tff(c_2920, plain, (![A_158, B_159, B_30]: (k4_xboole_0(A_158, k2_xboole_0(B_159, k4_xboole_0(k4_xboole_0(A_158, B_159), B_30)))=k3_xboole_0(k4_xboole_0(A_158, B_159), B_30))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2855])).
% 18.40/10.38  tff(c_15842, plain, (![A_393, B_394, B_395]: (k4_xboole_0(A_393, k2_xboole_0(B_394, k4_xboole_0(A_393, k2_xboole_0(B_394, B_395))))=k3_xboole_0(k4_xboole_0(A_393, B_394), B_395))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2920])).
% 18.40/10.38  tff(c_16076, plain, (![A_158, B_159]: (k4_xboole_0(A_158, k2_xboole_0(B_159, k4_xboole_0(A_158, B_159)))=k3_xboole_0(k4_xboole_0(A_158, B_159), B_159))), inference(superposition, [status(thm), theory('equality')], [c_2880, c_15842])).
% 18.40/10.38  tff(c_16219, plain, (![B_396, A_397]: (k3_xboole_0(B_396, k4_xboole_0(A_397, B_396))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2937, c_36, c_4, c_16076])).
% 18.40/10.38  tff(c_26, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.40/10.38  tff(c_16378, plain, (![B_396, A_397]: (r2_hidden('#skF_3'(B_396, k4_xboole_0(A_397, B_396)), k1_xboole_0) | r1_xboole_0(B_396, k4_xboole_0(A_397, B_396)))), inference(superposition, [status(thm), theory('equality')], [c_16219, c_26])).
% 18.40/10.38  tff(c_16522, plain, (![B_396, A_397]: (r1_xboole_0(B_396, k4_xboole_0(A_397, B_396)))), inference(negUnitSimplification, [status(thm)], [c_1777, c_16378])).
% 18.40/10.38  tff(c_63847, plain, (![B_976]: (r1_xboole_0(k2_xboole_0(B_976, '#skF_10'), k4_xboole_0('#skF_8', B_976)))), inference(superposition, [status(thm), theory('equality')], [c_61958, c_16522])).
% 18.40/10.38  tff(c_63931, plain, (r1_xboole_0(k2_xboole_0('#skF_9', '#skF_10'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2475, c_63847])).
% 18.40/10.38  tff(c_64376, plain, (r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_63931, c_24])).
% 18.40/10.38  tff(c_64383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2009, c_64376])).
% 18.40/10.38  tff(c_64385, plain, (r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_58])).
% 18.40/10.38  tff(c_60, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_8', k2_xboole_0('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.40/10.38  tff(c_64401, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64385, c_60])).
% 18.40/10.38  tff(c_64402, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_64401])).
% 18.40/10.38  tff(c_64384, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 18.40/10.38  tff(c_64392, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_64384, c_24])).
% 18.40/10.38  tff(c_64794, plain, (![A_991, C_992, B_993]: (r1_xboole_0(A_991, C_992) | ~r1_xboole_0(B_993, C_992) | ~r1_tarski(A_991, B_993))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_67003, plain, (![A_1062]: (r1_xboole_0(A_1062, '#skF_5') | ~r1_tarski(A_1062, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_64392, c_64794])).
% 18.40/10.38  tff(c_67038, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_67003])).
% 18.40/10.38  tff(c_67057, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_67038, c_24])).
% 18.40/10.38  tff(c_67063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64402, c_67057])).
% 18.40/10.38  tff(c_67064, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_64401])).
% 18.40/10.38  tff(c_67500, plain, (![A_1078, C_1079, B_1080]: (r1_xboole_0(A_1078, C_1079) | ~r1_xboole_0(B_1080, C_1079) | ~r1_tarski(A_1078, B_1080))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_69936, plain, (![A_1155]: (r1_xboole_0(A_1155, '#skF_5') | ~r1_tarski(A_1155, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_64392, c_67500])).
% 18.40/10.38  tff(c_69970, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_122, c_69936])).
% 18.40/10.38  tff(c_69981, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_69970, c_24])).
% 18.40/10.38  tff(c_69987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67064, c_69981])).
% 18.40/10.38  tff(c_69989, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_54])).
% 18.40/10.38  tff(c_56, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6') | r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.40/10.38  tff(c_70901, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_69989, c_56])).
% 18.40/10.38  tff(c_70902, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_70901])).
% 18.40/10.38  tff(c_69988, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 18.40/10.38  tff(c_70030, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_69988, c_24])).
% 18.40/10.38  tff(c_71564, plain, (![A_1224, C_1225, B_1226]: (r1_xboole_0(A_1224, C_1225) | ~r1_xboole_0(B_1226, C_1225) | ~r1_tarski(A_1224, B_1226))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_72390, plain, (![A_1257]: (r1_xboole_0(A_1257, '#skF_5') | ~r1_tarski(A_1257, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_70030, c_71564])).
% 18.40/10.38  tff(c_72425, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_72390])).
% 18.40/10.38  tff(c_72444, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_72425, c_24])).
% 18.40/10.38  tff(c_72450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70902, c_72444])).
% 18.40/10.38  tff(c_72451, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_70901])).
% 18.40/10.38  tff(c_73058, plain, (![A_1282, C_1283, B_1284]: (r1_xboole_0(A_1282, C_1283) | ~r1_xboole_0(B_1284, C_1283) | ~r1_tarski(A_1282, B_1284))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_73486, plain, (![A_1305]: (r1_xboole_0(A_1305, '#skF_5') | ~r1_tarski(A_1305, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_70030, c_73058])).
% 18.40/10.38  tff(c_73520, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_122, c_73486])).
% 18.40/10.38  tff(c_73528, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_73520, c_24])).
% 18.40/10.38  tff(c_73533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72451, c_73528])).
% 18.40/10.38  tff(c_73535, plain, (~r1_xboole_0('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_50])).
% 18.40/10.38  tff(c_52, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6') | r1_xboole_0('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.40/10.38  tff(c_73750, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_73535, c_52])).
% 18.40/10.38  tff(c_73751, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_73750])).
% 18.40/10.38  tff(c_73534, plain, (r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 18.40/10.38  tff(c_73538, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_73534, c_24])).
% 18.40/10.38  tff(c_74182, plain, (![A_1343, C_1344, B_1345]: (r1_xboole_0(A_1343, C_1344) | ~r1_xboole_0(B_1345, C_1344) | ~r1_tarski(A_1343, B_1345))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_74652, plain, (![A_1363]: (r1_xboole_0(A_1363, '#skF_5') | ~r1_tarski(A_1363, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_73538, c_74182])).
% 18.40/10.38  tff(c_74687, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_74652])).
% 18.40/10.38  tff(c_74698, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74687, c_24])).
% 18.40/10.38  tff(c_74703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73751, c_74698])).
% 18.40/10.38  tff(c_74704, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_73750])).
% 18.40/10.38  tff(c_75263, plain, (![A_1390, C_1391, B_1392]: (r1_xboole_0(A_1390, C_1391) | ~r1_xboole_0(B_1392, C_1391) | ~r1_tarski(A_1390, B_1392))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.40/10.38  tff(c_75666, plain, (![A_1412]: (r1_xboole_0(A_1412, '#skF_5') | ~r1_tarski(A_1412, k2_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_73538, c_75263])).
% 18.40/10.38  tff(c_75700, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_122, c_75666])).
% 18.40/10.38  tff(c_75707, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_75700, c_24])).
% 18.40/10.38  tff(c_75712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74704, c_75707])).
% 18.40/10.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.40/10.38  
% 18.40/10.38  Inference rules
% 18.40/10.38  ----------------------
% 18.40/10.38  #Ref     : 0
% 18.40/10.38  #Sup     : 19156
% 18.40/10.38  #Fact    : 0
% 18.40/10.38  #Define  : 0
% 18.40/10.38  #Split   : 21
% 18.40/10.38  #Chain   : 0
% 18.40/10.38  #Close   : 0
% 18.40/10.38  
% 18.40/10.38  Ordering : KBO
% 18.40/10.38  
% 18.40/10.38  Simplification rules
% 18.40/10.38  ----------------------
% 18.40/10.38  #Subsume      : 2087
% 18.40/10.38  #Demod        : 19319
% 18.40/10.38  #Tautology    : 12028
% 18.40/10.38  #SimpNegUnit  : 272
% 18.40/10.38  #BackRed      : 43
% 18.40/10.38  
% 18.40/10.38  #Partial instantiations: 0
% 18.40/10.38  #Strategies tried      : 1
% 18.40/10.38  
% 18.40/10.38  Timing (in seconds)
% 18.40/10.38  ----------------------
% 18.40/10.38  Preprocessing        : 0.32
% 18.40/10.38  Parsing              : 0.18
% 18.40/10.38  CNF conversion       : 0.02
% 18.40/10.38  Main loop            : 9.24
% 18.40/10.38  Inferencing          : 1.33
% 18.40/10.38  Reduction            : 5.24
% 18.40/10.38  Demodulation         : 4.56
% 18.40/10.38  BG Simplification    : 0.13
% 18.40/10.38  Subsumption          : 2.02
% 18.40/10.38  Abstraction          : 0.20
% 18.40/10.38  MUC search           : 0.00
% 18.40/10.38  Cooper               : 0.00
% 18.40/10.38  Total                : 9.61
% 18.40/10.38  Index Insertion      : 0.00
% 18.40/10.38  Index Deletion       : 0.00
% 18.40/10.38  Index Matching       : 0.00
% 18.40/10.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
