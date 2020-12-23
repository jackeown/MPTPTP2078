%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 12.73s
% Output     : CNFRefutation 12.73s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 184 expanded)
%              Number of leaves         :   33 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 248 expanded)
%              Number of equality atoms :   47 ( 123 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,A_49) = k2_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_49] : k2_xboole_0(k1_xboole_0,A_49) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_30])).

tff(c_661,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_685,plain,(
    ! [B_96] : k4_xboole_0(B_96,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_122])).

tff(c_723,plain,(
    ! [B_100] : k4_xboole_0(B_100,k1_xboole_0) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_685])).

tff(c_40,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_732,plain,(
    ! [B_100] : k5_xboole_0(k1_xboole_0,B_100) = k2_xboole_0(k1_xboole_0,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_40])).

tff(c_738,plain,(
    ! [B_100] : k5_xboole_0(k1_xboole_0,B_100) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_732])).

tff(c_32,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_30])).

tff(c_188,plain,(
    ! [B_17] : k3_xboole_0(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_153])).

tff(c_760,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_783,plain,(
    ! [B_17] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_760])).

tff(c_792,plain,(
    ! [B_104] : k4_xboole_0(k1_xboole_0,B_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_783])).

tff(c_804,plain,(
    ! [B_104] : k5_xboole_0(B_104,k1_xboole_0) = k2_xboole_0(B_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_40])).

tff(c_814,plain,(
    ! [B_104] : k5_xboole_0(B_104,k1_xboole_0) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_804])).

tff(c_26,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_201,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_209,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_26,c_201])).

tff(c_786,plain,(
    ! [B_12] : k5_xboole_0(B_12,B_12) = k4_xboole_0(B_12,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_760])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2486,plain,(
    ! [A_210,B_211,C_212] :
      ( r2_hidden(A_210,B_211)
      | r2_hidden(A_210,C_212)
      | ~ r2_hidden(A_210,k5_xboole_0(B_211,C_212)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2519,plain,(
    ! [B_211,C_212,B_4] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_211,C_212),B_4),B_211)
      | r2_hidden('#skF_1'(k5_xboole_0(B_211,C_212),B_4),C_212)
      | r1_tarski(k5_xboole_0(B_211,C_212),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_2486])).

tff(c_6337,plain,(
    ! [B_211,B_4] :
      ( r1_tarski(k5_xboole_0(B_211,B_211),B_4)
      | r2_hidden('#skF_1'(k5_xboole_0(B_211,B_211),B_4),B_211) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2519])).

tff(c_6339,plain,(
    ! [B_211,B_4] :
      ( r1_tarski(k4_xboole_0(B_211,B_211),B_4)
      | r2_hidden('#skF_1'(k4_xboole_0(B_211,B_211),B_4),B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_786,c_6337])).

tff(c_218,plain,(
    ! [B_54] : k3_xboole_0(B_54,B_54) = B_54 ),
    inference(resolution,[status(thm)],[c_26,c_201])).

tff(c_224,plain,(
    ! [B_54] : k2_xboole_0(B_54,B_54) = B_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_32])).

tff(c_38,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    ! [A_49,B_48] : r1_tarski(A_49,k2_xboole_0(B_48,A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_38])).

tff(c_977,plain,(
    ! [B_121,A_122] : r1_tarski(k4_xboole_0(B_121,A_122),k2_xboole_0(A_122,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_115])).

tff(c_994,plain,(
    ! [B_54] : r1_tarski(k4_xboole_0(B_54,B_54),B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_977])).

tff(c_937,plain,(
    ! [C_117,B_118,A_119] :
      ( r2_hidden(C_117,B_118)
      | ~ r2_hidden(C_117,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_962,plain,(
    ! [A_3,B_4,B_118] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_118)
      | ~ r1_tarski(A_3,B_118)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_937])).

tff(c_2218,plain,(
    ! [A_198,C_199,B_200] :
      ( ~ r2_hidden(A_198,C_199)
      | ~ r2_hidden(A_198,B_200)
      | ~ r2_hidden(A_198,k5_xboole_0(B_200,C_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5959,plain,(
    ! [B_412,C_413,B_414] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_412,C_413),B_414),C_413)
      | ~ r2_hidden('#skF_1'(k5_xboole_0(B_412,C_413),B_414),B_412)
      | r1_tarski(k5_xboole_0(B_412,C_413),B_414) ) ),
    inference(resolution,[status(thm)],[c_8,c_2218])).

tff(c_22254,plain,(
    ! [B_824,B_825,B_826] :
      ( ~ r2_hidden('#skF_1'(k5_xboole_0(B_824,B_825),B_826),B_824)
      | ~ r1_tarski(k5_xboole_0(B_824,B_825),B_825)
      | r1_tarski(k5_xboole_0(B_824,B_825),B_826) ) ),
    inference(resolution,[status(thm)],[c_962,c_5959])).

tff(c_22336,plain,(
    ! [B_12,B_826] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_12,B_12),B_826),B_12)
      | ~ r1_tarski(k5_xboole_0(B_12,B_12),B_12)
      | r1_tarski(k5_xboole_0(B_12,B_12),B_826) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_22254])).

tff(c_22394,plain,(
    ! [B_830,B_831] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_830,B_830),B_831),B_830)
      | r1_tarski(k4_xboole_0(B_830,B_830),B_831) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_994,c_786,c_22336])).

tff(c_22576,plain,(
    ! [B_835,B_836] : r1_tarski(k4_xboole_0(B_835,B_835),B_836) ),
    inference(resolution,[status(thm)],[c_6339,c_22394])).

tff(c_169,plain,(
    ! [A_50] : r1_tarski(k1_xboole_0,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_38])).

tff(c_546,plain,(
    ! [B_83,A_84] :
      ( B_83 = A_84
      | ~ r1_tarski(B_83,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_559,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_169,c_546])).

tff(c_22643,plain,(
    ! [B_835] : k4_xboole_0(B_835,B_835) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22576,c_559])).

tff(c_42,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1471,plain,(
    ! [A_150,B_151,C_152] :
      ( r1_tarski(k2_tarski(A_150,B_151),C_152)
      | ~ r2_hidden(B_151,C_152)
      | ~ r2_hidden(A_150,C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2522,plain,(
    ! [A_213,C_214] :
      ( r1_tarski(k1_tarski(A_213),C_214)
      | ~ r2_hidden(A_213,C_214)
      | ~ r2_hidden(A_213,C_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1471])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2565,plain,(
    ! [A_217,C_218] :
      ( k3_xboole_0(k1_tarski(A_217),C_218) = k1_tarski(A_217)
      | ~ r2_hidden(A_217,C_218) ) ),
    inference(resolution,[status(thm)],[c_2522,c_34])).

tff(c_28,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2589,plain,(
    ! [A_217,C_218] :
      ( k5_xboole_0(k1_tarski(A_217),k1_tarski(A_217)) = k4_xboole_0(k1_tarski(A_217),C_218)
      | ~ r2_hidden(A_217,C_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2565,c_28])).

tff(c_2629,plain,(
    ! [A_217,C_218] :
      ( k4_xboole_0(k1_tarski(A_217),k1_tarski(A_217)) = k4_xboole_0(k1_tarski(A_217),C_218)
      | ~ r2_hidden(A_217,C_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_2589])).

tff(c_27878,plain,(
    ! [A_868,C_869] :
      ( k4_xboole_0(k1_tarski(A_868),C_869) = k1_xboole_0
      | ~ r2_hidden(A_868,C_869) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22643,c_2629])).

tff(c_28058,plain,(
    ! [C_869,A_868] :
      ( k2_xboole_0(C_869,k1_tarski(A_868)) = k5_xboole_0(C_869,k1_xboole_0)
      | ~ r2_hidden(A_868,C_869) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27878,c_40])).

tff(c_29178,plain,(
    ! [C_876,A_877] :
      ( k2_xboole_0(C_876,k1_tarski(A_877)) = C_876
      | ~ r2_hidden(A_877,C_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_28058])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_62,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_29689,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29178,c_62])).

tff(c_29792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_29689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:43:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.73/5.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/5.59  
% 12.73/5.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/5.59  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.73/5.59  
% 12.73/5.59  %Foreground sorts:
% 12.73/5.59  
% 12.73/5.59  
% 12.73/5.59  %Background operators:
% 12.73/5.59  
% 12.73/5.59  
% 12.73/5.59  %Foreground operators:
% 12.73/5.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.73/5.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.73/5.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.73/5.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.73/5.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.73/5.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.73/5.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.73/5.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.73/5.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.73/5.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.73/5.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.73/5.59  tff('#skF_2', type, '#skF_2': $i).
% 12.73/5.59  tff('#skF_3', type, '#skF_3': $i).
% 12.73/5.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.73/5.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.73/5.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.73/5.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.73/5.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.73/5.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.73/5.59  
% 12.73/5.61  tff(f_84, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 12.73/5.61  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 12.73/5.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.73/5.61  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.73/5.61  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.73/5.61  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 12.73/5.61  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.73/5.61  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.73/5.61  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.73/5.61  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.73/5.61  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 12.73/5.61  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.73/5.61  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.73/5.61  tff(f_79, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 12.73/5.61  tff(c_60, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.73/5.61  tff(c_30, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.73/5.61  tff(c_100, plain, (![B_48, A_49]: (k2_xboole_0(B_48, A_49)=k2_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.73/5.61  tff(c_122, plain, (![A_49]: (k2_xboole_0(k1_xboole_0, A_49)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_100, c_30])).
% 12.73/5.61  tff(c_661, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.73/5.61  tff(c_685, plain, (![B_96]: (k4_xboole_0(B_96, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_96))), inference(superposition, [status(thm), theory('equality')], [c_661, c_122])).
% 12.73/5.61  tff(c_723, plain, (![B_100]: (k4_xboole_0(B_100, k1_xboole_0)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_685])).
% 12.73/5.61  tff(c_40, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.73/5.61  tff(c_732, plain, (![B_100]: (k5_xboole_0(k1_xboole_0, B_100)=k2_xboole_0(k1_xboole_0, B_100))), inference(superposition, [status(thm), theory('equality')], [c_723, c_40])).
% 12.73/5.61  tff(c_738, plain, (![B_100]: (k5_xboole_0(k1_xboole_0, B_100)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_732])).
% 12.73/5.61  tff(c_32, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k3_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.73/5.61  tff(c_153, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_100, c_30])).
% 12.73/5.61  tff(c_188, plain, (![B_17]: (k3_xboole_0(k1_xboole_0, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_153])).
% 12.73/5.61  tff(c_760, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.73/5.61  tff(c_783, plain, (![B_17]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_17))), inference(superposition, [status(thm), theory('equality')], [c_188, c_760])).
% 12.73/5.61  tff(c_792, plain, (![B_104]: (k4_xboole_0(k1_xboole_0, B_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_738, c_783])).
% 12.73/5.61  tff(c_804, plain, (![B_104]: (k5_xboole_0(B_104, k1_xboole_0)=k2_xboole_0(B_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_792, c_40])).
% 12.73/5.61  tff(c_814, plain, (![B_104]: (k5_xboole_0(B_104, k1_xboole_0)=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_804])).
% 12.73/5.61  tff(c_26, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/5.61  tff(c_201, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.73/5.61  tff(c_209, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_26, c_201])).
% 12.73/5.61  tff(c_786, plain, (![B_12]: (k5_xboole_0(B_12, B_12)=k4_xboole_0(B_12, B_12))), inference(superposition, [status(thm), theory('equality')], [c_209, c_760])).
% 12.73/5.61  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.73/5.61  tff(c_2486, plain, (![A_210, B_211, C_212]: (r2_hidden(A_210, B_211) | r2_hidden(A_210, C_212) | ~r2_hidden(A_210, k5_xboole_0(B_211, C_212)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.73/5.61  tff(c_2519, plain, (![B_211, C_212, B_4]: (r2_hidden('#skF_1'(k5_xboole_0(B_211, C_212), B_4), B_211) | r2_hidden('#skF_1'(k5_xboole_0(B_211, C_212), B_4), C_212) | r1_tarski(k5_xboole_0(B_211, C_212), B_4))), inference(resolution, [status(thm)], [c_8, c_2486])).
% 12.73/5.61  tff(c_6337, plain, (![B_211, B_4]: (r1_tarski(k5_xboole_0(B_211, B_211), B_4) | r2_hidden('#skF_1'(k5_xboole_0(B_211, B_211), B_4), B_211))), inference(factorization, [status(thm), theory('equality')], [c_2519])).
% 12.73/5.61  tff(c_6339, plain, (![B_211, B_4]: (r1_tarski(k4_xboole_0(B_211, B_211), B_4) | r2_hidden('#skF_1'(k4_xboole_0(B_211, B_211), B_4), B_211))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_786, c_6337])).
% 12.73/5.61  tff(c_218, plain, (![B_54]: (k3_xboole_0(B_54, B_54)=B_54)), inference(resolution, [status(thm)], [c_26, c_201])).
% 12.73/5.61  tff(c_224, plain, (![B_54]: (k2_xboole_0(B_54, B_54)=B_54)), inference(superposition, [status(thm), theory('equality')], [c_218, c_32])).
% 12.73/5.61  tff(c_38, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.73/5.61  tff(c_115, plain, (![A_49, B_48]: (r1_tarski(A_49, k2_xboole_0(B_48, A_49)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_38])).
% 12.73/5.61  tff(c_977, plain, (![B_121, A_122]: (r1_tarski(k4_xboole_0(B_121, A_122), k2_xboole_0(A_122, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_661, c_115])).
% 12.73/5.61  tff(c_994, plain, (![B_54]: (r1_tarski(k4_xboole_0(B_54, B_54), B_54))), inference(superposition, [status(thm), theory('equality')], [c_224, c_977])).
% 12.73/5.61  tff(c_937, plain, (![C_117, B_118, A_119]: (r2_hidden(C_117, B_118) | ~r2_hidden(C_117, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.73/5.61  tff(c_962, plain, (![A_3, B_4, B_118]: (r2_hidden('#skF_1'(A_3, B_4), B_118) | ~r1_tarski(A_3, B_118) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_937])).
% 12.73/5.61  tff(c_2218, plain, (![A_198, C_199, B_200]: (~r2_hidden(A_198, C_199) | ~r2_hidden(A_198, B_200) | ~r2_hidden(A_198, k5_xboole_0(B_200, C_199)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.73/5.61  tff(c_5959, plain, (![B_412, C_413, B_414]: (~r2_hidden('#skF_1'(k5_xboole_0(B_412, C_413), B_414), C_413) | ~r2_hidden('#skF_1'(k5_xboole_0(B_412, C_413), B_414), B_412) | r1_tarski(k5_xboole_0(B_412, C_413), B_414))), inference(resolution, [status(thm)], [c_8, c_2218])).
% 12.73/5.61  tff(c_22254, plain, (![B_824, B_825, B_826]: (~r2_hidden('#skF_1'(k5_xboole_0(B_824, B_825), B_826), B_824) | ~r1_tarski(k5_xboole_0(B_824, B_825), B_825) | r1_tarski(k5_xboole_0(B_824, B_825), B_826))), inference(resolution, [status(thm)], [c_962, c_5959])).
% 12.73/5.61  tff(c_22336, plain, (![B_12, B_826]: (~r2_hidden('#skF_1'(k4_xboole_0(B_12, B_12), B_826), B_12) | ~r1_tarski(k5_xboole_0(B_12, B_12), B_12) | r1_tarski(k5_xboole_0(B_12, B_12), B_826))), inference(superposition, [status(thm), theory('equality')], [c_786, c_22254])).
% 12.73/5.61  tff(c_22394, plain, (![B_830, B_831]: (~r2_hidden('#skF_1'(k4_xboole_0(B_830, B_830), B_831), B_830) | r1_tarski(k4_xboole_0(B_830, B_830), B_831))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_994, c_786, c_22336])).
% 12.73/5.61  tff(c_22576, plain, (![B_835, B_836]: (r1_tarski(k4_xboole_0(B_835, B_835), B_836))), inference(resolution, [status(thm)], [c_6339, c_22394])).
% 12.73/5.61  tff(c_169, plain, (![A_50]: (r1_tarski(k1_xboole_0, A_50))), inference(superposition, [status(thm), theory('equality')], [c_153, c_38])).
% 12.73/5.61  tff(c_546, plain, (![B_83, A_84]: (B_83=A_84 | ~r1_tarski(B_83, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/5.61  tff(c_559, plain, (![A_50]: (k1_xboole_0=A_50 | ~r1_tarski(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_169, c_546])).
% 12.73/5.61  tff(c_22643, plain, (![B_835]: (k4_xboole_0(B_835, B_835)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22576, c_559])).
% 12.73/5.61  tff(c_42, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.73/5.61  tff(c_1471, plain, (![A_150, B_151, C_152]: (r1_tarski(k2_tarski(A_150, B_151), C_152) | ~r2_hidden(B_151, C_152) | ~r2_hidden(A_150, C_152))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.73/5.61  tff(c_2522, plain, (![A_213, C_214]: (r1_tarski(k1_tarski(A_213), C_214) | ~r2_hidden(A_213, C_214) | ~r2_hidden(A_213, C_214))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1471])).
% 12.73/5.61  tff(c_34, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.73/5.61  tff(c_2565, plain, (![A_217, C_218]: (k3_xboole_0(k1_tarski(A_217), C_218)=k1_tarski(A_217) | ~r2_hidden(A_217, C_218))), inference(resolution, [status(thm)], [c_2522, c_34])).
% 12.73/5.61  tff(c_28, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.73/5.61  tff(c_2589, plain, (![A_217, C_218]: (k5_xboole_0(k1_tarski(A_217), k1_tarski(A_217))=k4_xboole_0(k1_tarski(A_217), C_218) | ~r2_hidden(A_217, C_218))), inference(superposition, [status(thm), theory('equality')], [c_2565, c_28])).
% 12.73/5.61  tff(c_2629, plain, (![A_217, C_218]: (k4_xboole_0(k1_tarski(A_217), k1_tarski(A_217))=k4_xboole_0(k1_tarski(A_217), C_218) | ~r2_hidden(A_217, C_218))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_2589])).
% 12.73/5.61  tff(c_27878, plain, (![A_868, C_869]: (k4_xboole_0(k1_tarski(A_868), C_869)=k1_xboole_0 | ~r2_hidden(A_868, C_869))), inference(demodulation, [status(thm), theory('equality')], [c_22643, c_2629])).
% 12.73/5.61  tff(c_28058, plain, (![C_869, A_868]: (k2_xboole_0(C_869, k1_tarski(A_868))=k5_xboole_0(C_869, k1_xboole_0) | ~r2_hidden(A_868, C_869))), inference(superposition, [status(thm), theory('equality')], [c_27878, c_40])).
% 12.73/5.61  tff(c_29178, plain, (![C_876, A_877]: (k2_xboole_0(C_876, k1_tarski(A_877))=C_876 | ~r2_hidden(A_877, C_876))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_28058])).
% 12.73/5.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.73/5.61  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.73/5.61  tff(c_62, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 12.73/5.61  tff(c_29689, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29178, c_62])).
% 12.73/5.61  tff(c_29792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_29689])).
% 12.73/5.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/5.61  
% 12.73/5.61  Inference rules
% 12.73/5.61  ----------------------
% 12.73/5.61  #Ref     : 0
% 12.73/5.61  #Sup     : 7072
% 12.73/5.61  #Fact    : 2
% 12.73/5.61  #Define  : 0
% 12.73/5.61  #Split   : 1
% 12.73/5.61  #Chain   : 0
% 12.73/5.61  #Close   : 0
% 12.73/5.61  
% 12.73/5.61  Ordering : KBO
% 12.73/5.61  
% 12.73/5.61  Simplification rules
% 12.73/5.61  ----------------------
% 12.73/5.61  #Subsume      : 1787
% 12.73/5.61  #Demod        : 5627
% 12.73/5.61  #Tautology    : 3378
% 12.73/5.61  #SimpNegUnit  : 117
% 12.73/5.61  #BackRed      : 58
% 12.73/5.61  
% 12.73/5.61  #Partial instantiations: 0
% 12.73/5.61  #Strategies tried      : 1
% 12.73/5.61  
% 12.73/5.61  Timing (in seconds)
% 12.73/5.61  ----------------------
% 12.73/5.61  Preprocessing        : 0.34
% 12.73/5.61  Parsing              : 0.17
% 12.73/5.61  CNF conversion       : 0.02
% 12.73/5.61  Main loop            : 4.51
% 12.73/5.61  Inferencing          : 0.91
% 12.73/5.61  Reduction            : 2.30
% 12.73/5.61  Demodulation         : 1.98
% 12.73/5.61  BG Simplification    : 0.08
% 12.73/5.61  Subsumption          : 1.01
% 12.73/5.61  Abstraction          : 0.13
% 12.73/5.61  MUC search           : 0.00
% 12.73/5.61  Cooper               : 0.00
% 12.73/5.61  Total                : 4.89
% 12.73/5.61  Index Insertion      : 0.00
% 12.73/5.61  Index Deletion       : 0.00
% 12.73/5.61  Index Matching       : 0.00
% 12.73/5.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
