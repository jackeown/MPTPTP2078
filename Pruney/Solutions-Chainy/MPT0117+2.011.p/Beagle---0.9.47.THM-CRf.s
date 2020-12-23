%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:30 EST 2020

% Result     : Theorem 10.03s
% Output     : CNFRefutation 10.27s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 289 expanded)
%              Number of leaves         :   31 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  104 ( 323 expanded)
%              Number of equality atoms :   56 ( 227 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

tff(c_20,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    ! [B_43,A_44] : k5_xboole_0(B_43,A_44) = k5_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    ! [A_44] : k5_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_24])).

tff(c_28,plain,(
    ! [A_31] : k5_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_676,plain,(
    ! [A_77,B_78,C_79] : k5_xboole_0(k5_xboole_0(A_77,B_78),C_79) = k5_xboole_0(A_77,k5_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_750,plain,(
    ! [A_31,C_79] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_79)) = k5_xboole_0(k1_xboole_0,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_676])).

tff(c_771,plain,(
    ! [A_80,C_81] : k5_xboole_0(A_80,k5_xboole_0(A_80,C_81)) = C_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_750])).

tff(c_810,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_771])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_166,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_177,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_1367,plain,(
    ! [A_96,B_97] : k2_xboole_0(k5_xboole_0(A_96,B_97),k3_xboole_0(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1421,plain,(
    k2_xboole_0(k5_xboole_0('#skF_5','#skF_4'),'#skF_5') = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_1367])).

tff(c_1443,plain,(
    k2_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_5') = k2_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1421])).

tff(c_768,plain,(
    ! [A_31,C_79] : k5_xboole_0(A_31,k5_xboole_0(A_31,C_79)) = C_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_750])).

tff(c_937,plain,(
    ! [B_85,A_86] : k5_xboole_0(B_85,k5_xboole_0(A_86,B_85)) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_771])).

tff(c_976,plain,(
    ! [A_31,C_79] : k5_xboole_0(k5_xboole_0(A_31,C_79),C_79) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_937])).

tff(c_187,plain,(
    ! [A_49,B_50] : r1_xboole_0(k3_xboole_0(A_49,B_50),k5_xboole_0(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    r1_xboole_0('#skF_5',k5_xboole_0('#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_187])).

tff(c_210,plain,(
    r1_xboole_0('#skF_5',k5_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_193])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_393,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11759,plain,(
    ! [A_262,B_263] :
      ( ~ r1_xboole_0(A_262,B_263)
      | k3_xboole_0(A_262,B_263) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_11806,plain,(
    k3_xboole_0('#skF_5',k5_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_210,c_11759])).

tff(c_13135,plain,(
    k4_xboole_0('#skF_5',k5_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11806,c_12])).

tff(c_13155,plain,(
    k4_xboole_0('#skF_5',k5_xboole_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_13135])).

tff(c_34,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_13527,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_5') = k2_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13155,c_34])).

tff(c_13537,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_976,c_13527])).

tff(c_16101,plain,(
    ! [A_353,B_354] : k5_xboole_0(A_353,k2_xboole_0(A_353,B_354)) = k4_xboole_0(B_354,A_353) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_771])).

tff(c_16190,plain,(
    k5_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13537,c_16101])).

tff(c_16285,plain,(
    k5_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_16190,c_976])).

tff(c_14001,plain,(
    ! [A_317,A_315,B_316] : k5_xboole_0(A_317,k5_xboole_0(A_315,B_316)) = k5_xboole_0(A_315,k5_xboole_0(B_316,A_317)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_676])).

tff(c_14258,plain,(
    ! [A_44,A_317] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_44,A_317)) = k5_xboole_0(A_317,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_14001])).

tff(c_16896,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16285,c_14258])).

tff(c_16962,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_84,c_16896])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_tarski(A_17,k3_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22259,plain,(
    ! [A_420] :
      ( r1_tarski(A_420,'#skF_4')
      | ~ r1_tarski(A_420,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16962,c_16])).

tff(c_22294,plain,(
    ! [B_23] : r1_tarski(k4_xboole_0('#skF_5',B_23),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_22259])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_178,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_166])).

tff(c_1418,plain,(
    k2_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_3') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1367])).

tff(c_1442,plain,(
    k2_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1418])).

tff(c_190,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_187])).

tff(c_209,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_190])).

tff(c_1797,plain,(
    ! [A_106,B_107] :
      ( ~ r1_xboole_0(A_106,B_107)
      | k3_xboole_0(A_106,B_107) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_1845,plain,(
    k3_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_209,c_1797])).

tff(c_2552,plain,(
    k4_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1845,c_12])).

tff(c_2571,plain,(
    k4_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2552])).

tff(c_3608,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') = k2_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2571,c_34])).

tff(c_3618,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_976,c_3608])).

tff(c_6017,plain,(
    ! [A_199,B_200] : k5_xboole_0(A_199,k2_xboole_0(A_199,B_200)) = k4_xboole_0(B_200,A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_771])).

tff(c_6111,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3618,c_6017])).

tff(c_826,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_771])).

tff(c_6204,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6111,c_826])).

tff(c_8929,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6204,c_810])).

tff(c_11609,plain,(
    ! [A_260] :
      ( r1_tarski(A_260,'#skF_4')
      | ~ r1_tarski(A_260,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8929,c_16])).

tff(c_11644,plain,(
    ! [B_23] : r1_tarski(k4_xboole_0('#skF_3',B_23),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_11609])).

tff(c_1547,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(k5_xboole_0(A_99,B_100),C_101)
      | ~ r1_tarski(k4_xboole_0(B_100,A_99),C_101)
      | ~ r1_tarski(k4_xboole_0(A_99,B_100),C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1596,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_5','#skF_3'),'#skF_4')
    | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1547,c_36])).

tff(c_1638,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1596])).

tff(c_11672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11644,c_1638])).

tff(c_11673,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_5','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1596])).

tff(c_22404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22294,c_11673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.03/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.99  
% 10.18/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 10.20/3.99  
% 10.20/3.99  %Foreground sorts:
% 10.20/3.99  
% 10.20/3.99  
% 10.20/3.99  %Background operators:
% 10.20/3.99  
% 10.20/3.99  
% 10.20/3.99  %Foreground operators:
% 10.20/3.99  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.20/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/3.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.20/3.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.20/3.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/3.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.20/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.20/3.99  tff('#skF_5', type, '#skF_5': $i).
% 10.20/3.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.20/3.99  tff('#skF_3', type, '#skF_3': $i).
% 10.20/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/3.99  tff('#skF_4', type, '#skF_4': $i).
% 10.20/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/3.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.20/3.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.20/3.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.20/3.99  
% 10.27/4.01  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.27/4.01  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.27/4.01  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.27/4.01  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 10.27/4.01  tff(f_73, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.27/4.01  tff(f_71, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.27/4.01  tff(f_90, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 10.27/4.01  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.27/4.01  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 10.27/4.01  tff(f_51, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 10.27/4.01  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.27/4.01  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.27/4.01  tff(f_83, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.27/4.01  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 10.27/4.01  tff(f_81, axiom, (![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 10.27/4.01  tff(c_20, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.27/4.01  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.27/4.01  tff(c_68, plain, (![B_43, A_44]: (k5_xboole_0(B_43, A_44)=k5_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.27/4.01  tff(c_24, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.27/4.01  tff(c_84, plain, (![A_44]: (k5_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_68, c_24])).
% 10.27/4.01  tff(c_28, plain, (![A_31]: (k5_xboole_0(A_31, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.27/4.01  tff(c_676, plain, (![A_77, B_78, C_79]: (k5_xboole_0(k5_xboole_0(A_77, B_78), C_79)=k5_xboole_0(A_77, k5_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.27/4.01  tff(c_750, plain, (![A_31, C_79]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_79))=k5_xboole_0(k1_xboole_0, C_79))), inference(superposition, [status(thm), theory('equality')], [c_28, c_676])).
% 10.27/4.01  tff(c_771, plain, (![A_80, C_81]: (k5_xboole_0(A_80, k5_xboole_0(A_80, C_81))=C_81)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_750])).
% 10.27/4.01  tff(c_810, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_771])).
% 10.27/4.01  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.27/4.01  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.27/4.01  tff(c_166, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.27/4.01  tff(c_177, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_38, c_166])).
% 10.27/4.01  tff(c_1367, plain, (![A_96, B_97]: (k2_xboole_0(k5_xboole_0(A_96, B_97), k3_xboole_0(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.27/4.01  tff(c_1421, plain, (k2_xboole_0(k5_xboole_0('#skF_5', '#skF_4'), '#skF_5')=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_177, c_1367])).
% 10.27/4.01  tff(c_1443, plain, (k2_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_5')=k2_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1421])).
% 10.27/4.01  tff(c_768, plain, (![A_31, C_79]: (k5_xboole_0(A_31, k5_xboole_0(A_31, C_79))=C_79)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_750])).
% 10.27/4.01  tff(c_937, plain, (![B_85, A_86]: (k5_xboole_0(B_85, k5_xboole_0(A_86, B_85))=A_86)), inference(superposition, [status(thm), theory('equality')], [c_2, c_771])).
% 10.27/4.01  tff(c_976, plain, (![A_31, C_79]: (k5_xboole_0(k5_xboole_0(A_31, C_79), C_79)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_768, c_937])).
% 10.27/4.01  tff(c_187, plain, (![A_49, B_50]: (r1_xboole_0(k3_xboole_0(A_49, B_50), k5_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.27/4.01  tff(c_193, plain, (r1_xboole_0('#skF_5', k5_xboole_0('#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_187])).
% 10.27/4.01  tff(c_210, plain, (r1_xboole_0('#skF_5', k5_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_193])).
% 10.27/4.01  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.27/4.01  tff(c_393, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.27/4.01  tff(c_11759, plain, (![A_262, B_263]: (~r1_xboole_0(A_262, B_263) | k3_xboole_0(A_262, B_263)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_393])).
% 10.27/4.01  tff(c_11806, plain, (k3_xboole_0('#skF_5', k5_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_210, c_11759])).
% 10.27/4.01  tff(c_13135, plain, (k4_xboole_0('#skF_5', k5_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11806, c_12])).
% 10.27/4.01  tff(c_13155, plain, (k4_xboole_0('#skF_5', k5_xboole_0('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_13135])).
% 10.27/4.01  tff(c_34, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.27/4.01  tff(c_13527, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_5')=k2_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13155, c_34])).
% 10.27/4.01  tff(c_13537, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1443, c_976, c_13527])).
% 10.27/4.01  tff(c_16101, plain, (![A_353, B_354]: (k5_xboole_0(A_353, k2_xboole_0(A_353, B_354))=k4_xboole_0(B_354, A_353))), inference(superposition, [status(thm), theory('equality')], [c_34, c_771])).
% 10.27/4.01  tff(c_16190, plain, (k5_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13537, c_16101])).
% 10.27/4.01  tff(c_16285, plain, (k5_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_16190, c_976])).
% 10.27/4.01  tff(c_14001, plain, (![A_317, A_315, B_316]: (k5_xboole_0(A_317, k5_xboole_0(A_315, B_316))=k5_xboole_0(A_315, k5_xboole_0(B_316, A_317)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_676])).
% 10.27/4.01  tff(c_14258, plain, (![A_44, A_317]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_44, A_317))=k5_xboole_0(A_317, A_44))), inference(superposition, [status(thm), theory('equality')], [c_84, c_14001])).
% 10.27/4.01  tff(c_16896, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16285, c_14258])).
% 10.27/4.01  tff(c_16962, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_810, c_84, c_16896])).
% 10.27/4.01  tff(c_16, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, B_18) | ~r1_tarski(A_17, k3_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.27/4.01  tff(c_22259, plain, (![A_420]: (r1_tarski(A_420, '#skF_4') | ~r1_tarski(A_420, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16962, c_16])).
% 10.27/4.01  tff(c_22294, plain, (![B_23]: (r1_tarski(k4_xboole_0('#skF_5', B_23), '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_22259])).
% 10.27/4.01  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.27/4.01  tff(c_178, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_40, c_166])).
% 10.27/4.01  tff(c_1418, plain, (k2_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_178, c_1367])).
% 10.27/4.01  tff(c_1442, plain, (k2_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k2_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1418])).
% 10.27/4.01  tff(c_190, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_187])).
% 10.27/4.01  tff(c_209, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_190])).
% 10.27/4.01  tff(c_1797, plain, (![A_106, B_107]: (~r1_xboole_0(A_106, B_107) | k3_xboole_0(A_106, B_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_393])).
% 10.27/4.01  tff(c_1845, plain, (k3_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_209, c_1797])).
% 10.27/4.01  tff(c_2552, plain, (k4_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1845, c_12])).
% 10.27/4.01  tff(c_2571, plain, (k4_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2552])).
% 10.27/4.01  tff(c_3608, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k2_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2571, c_34])).
% 10.27/4.01  tff(c_3618, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_976, c_3608])).
% 10.27/4.01  tff(c_6017, plain, (![A_199, B_200]: (k5_xboole_0(A_199, k2_xboole_0(A_199, B_200))=k4_xboole_0(B_200, A_199))), inference(superposition, [status(thm), theory('equality')], [c_34, c_771])).
% 10.27/4.01  tff(c_6111, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3618, c_6017])).
% 10.27/4.01  tff(c_826, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_771])).
% 10.27/4.01  tff(c_6204, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6111, c_826])).
% 10.27/4.01  tff(c_8929, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6204, c_810])).
% 10.27/4.01  tff(c_11609, plain, (![A_260]: (r1_tarski(A_260, '#skF_4') | ~r1_tarski(A_260, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8929, c_16])).
% 10.27/4.01  tff(c_11644, plain, (![B_23]: (r1_tarski(k4_xboole_0('#skF_3', B_23), '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_11609])).
% 10.27/4.01  tff(c_1547, plain, (![A_99, B_100, C_101]: (r1_tarski(k5_xboole_0(A_99, B_100), C_101) | ~r1_tarski(k4_xboole_0(B_100, A_99), C_101) | ~r1_tarski(k4_xboole_0(A_99, B_100), C_101))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.27/4.01  tff(c_36, plain, (~r1_tarski(k5_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.27/4.01  tff(c_1596, plain, (~r1_tarski(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4') | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1547, c_36])).
% 10.27/4.01  tff(c_1638, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1596])).
% 10.27/4.01  tff(c_11672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11644, c_1638])).
% 10.27/4.01  tff(c_11673, plain, (~r1_tarski(k4_xboole_0('#skF_5', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1596])).
% 10.27/4.01  tff(c_22404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22294, c_11673])).
% 10.27/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.27/4.01  
% 10.27/4.01  Inference rules
% 10.27/4.01  ----------------------
% 10.27/4.01  #Ref     : 0
% 10.27/4.01  #Sup     : 5722
% 10.27/4.01  #Fact    : 0
% 10.27/4.01  #Define  : 0
% 10.27/4.01  #Split   : 9
% 10.27/4.01  #Chain   : 0
% 10.27/4.01  #Close   : 0
% 10.27/4.01  
% 10.27/4.01  Ordering : KBO
% 10.27/4.01  
% 10.27/4.01  Simplification rules
% 10.27/4.01  ----------------------
% 10.27/4.01  #Subsume      : 252
% 10.27/4.01  #Demod        : 6285
% 10.27/4.01  #Tautology    : 3099
% 10.27/4.01  #SimpNegUnit  : 39
% 10.27/4.01  #BackRed      : 61
% 10.27/4.01  
% 10.27/4.01  #Partial instantiations: 0
% 10.27/4.01  #Strategies tried      : 1
% 10.27/4.01  
% 10.27/4.01  Timing (in seconds)
% 10.27/4.01  ----------------------
% 10.27/4.01  Preprocessing        : 0.31
% 10.27/4.01  Parsing              : 0.17
% 10.27/4.01  CNF conversion       : 0.02
% 10.27/4.01  Main loop            : 2.97
% 10.27/4.01  Inferencing          : 0.67
% 10.27/4.01  Reduction            : 1.56
% 10.27/4.01  Demodulation         : 1.32
% 10.27/4.01  BG Simplification    : 0.08
% 10.27/4.01  Subsumption          : 0.47
% 10.27/4.01  Abstraction          : 0.11
% 10.27/4.01  MUC search           : 0.00
% 10.27/4.01  Cooper               : 0.00
% 10.27/4.01  Total                : 3.32
% 10.27/4.01  Index Insertion      : 0.00
% 10.27/4.01  Index Deletion       : 0.00
% 10.27/4.01  Index Matching       : 0.00
% 10.27/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
