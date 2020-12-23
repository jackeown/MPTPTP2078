%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 11.42s
% Output     : CNFRefutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 290 expanded)
%              Number of leaves         :   33 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :   77 ( 282 expanded)
%              Number of equality atoms :   61 ( 262 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [C_51,A_49,B_50] :
      ( k4_xboole_0(C_51,k2_tarski(A_49,B_50)) = C_51
      | r2_hidden(B_50,C_51)
      | r2_hidden(A_49,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [B_54,A_55] : k5_xboole_0(B_54,A_55) = k5_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_55] : k5_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_738,plain,(
    ! [A_91,B_92] : k5_xboole_0(k5_xboole_0(A_91,B_92),k2_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3106,plain,(
    ! [A_158,B_159] : k5_xboole_0(A_158,k5_xboole_0(B_159,k2_xboole_0(A_158,B_159))) = k3_xboole_0(A_158,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_14])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_489,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_549,plain,(
    ! [A_15,C_86] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_86)) = k5_xboole_0(k1_xboole_0,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_489])).

tff(c_567,plain,(
    ! [A_15,C_86] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_86)) = C_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_549])).

tff(c_3151,plain,(
    ! [B_159,A_158] : k5_xboole_0(B_159,k2_xboole_0(A_158,B_159)) = k5_xboole_0(A_158,k3_xboole_0(A_158,B_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3106,c_567])).

tff(c_4604,plain,(
    ! [B_180,A_181] : k5_xboole_0(B_180,k2_xboole_0(A_181,B_180)) = k4_xboole_0(A_181,B_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3151])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2087,plain,(
    ! [C_145,A_146,B_147] : k5_xboole_0(C_145,k5_xboole_0(A_146,B_147)) = k5_xboole_0(A_146,k5_xboole_0(B_147,C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_4])).

tff(c_2380,plain,(
    ! [A_55,C_145] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_55,C_145)) = k5_xboole_0(C_145,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2087])).

tff(c_4619,plain,(
    ! [A_181,B_180] : k5_xboole_0(k2_xboole_0(A_181,B_180),B_180) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_181,B_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4604,c_2380])).

tff(c_6180,plain,(
    ! [A_200,B_201] : k5_xboole_0(k2_xboole_0(A_200,B_201),B_201) = k4_xboole_0(A_200,B_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4619])).

tff(c_6320,plain,(
    ! [B_2,A_1] : k5_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6180])).

tff(c_3840,plain,(
    ! [A_170,B_171] : k5_xboole_0(k5_xboole_0(A_170,B_171),k2_xboole_0(B_171,A_170)) = k3_xboole_0(A_170,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_738])).

tff(c_826,plain,(
    ! [A_3,B_4] : k5_xboole_0(k5_xboole_0(A_3,B_4),k2_xboole_0(B_4,A_3)) = k3_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_738])).

tff(c_3855,plain,(
    ! [B_171,A_170] : k3_xboole_0(B_171,A_170) = k3_xboole_0(A_170,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_3840,c_826])).

tff(c_4710,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4604])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5451,plain,(
    ! [A_190,B_191] : k5_xboole_0(A_190,k2_xboole_0(A_190,B_191)) = k4_xboole_0(B_191,A_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4604])).

tff(c_5567,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k4_xboole_0(k4_xboole_0(B_10,A_9),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5451])).

tff(c_10008,plain,(
    ! [B_239,A_240] : k4_xboole_0(k4_xboole_0(B_239,A_240),A_240) = k4_xboole_0(B_239,A_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4710,c_5567])).

tff(c_570,plain,(
    ! [A_87,C_88] : k5_xboole_0(A_87,k5_xboole_0(A_87,C_88)) = C_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_549])).

tff(c_606,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_570])).

tff(c_4108,plain,(
    ! [A_174,C_175] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_174,C_175)) = k5_xboole_0(C_175,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2087])).

tff(c_4225,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_4108])).

tff(c_4303,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4225])).

tff(c_10054,plain,(
    ! [B_239,A_240] : k5_xboole_0(k4_xboole_0(B_239,A_240),k4_xboole_0(B_239,A_240)) = k3_xboole_0(k4_xboole_0(B_239,A_240),A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_10008,c_4303])).

tff(c_10154,plain,(
    ! [A_241,B_242] : k3_xboole_0(A_241,k4_xboole_0(B_242,A_241)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_16,c_10054])).

tff(c_4254,plain,(
    ! [A_5,B_6] : k5_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4108])).

tff(c_4311,plain,(
    ! [A_5,B_6] : k5_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k4_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4254])).

tff(c_10168,plain,(
    ! [A_241,B_242] : k4_xboole_0(A_241,k4_xboole_0(B_242,A_241)) = k5_xboole_0(k1_xboole_0,A_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_10154,c_4311])).

tff(c_10223,plain,(
    ! [A_241,B_242] : k4_xboole_0(A_241,k4_xboole_0(B_242,A_241)) = A_241 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_10168])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),k5_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1328,plain,(
    ! [A_127,C_128] : r1_tarski(k4_xboole_0(A_127,k5_xboole_0(A_127,C_128)),C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_20])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4317,plain,(
    ! [A_176,C_177] : k2_xboole_0(k4_xboole_0(A_176,k5_xboole_0(A_176,C_177)),C_177) = C_177 ),
    inference(resolution,[status(thm)],[c_1328,c_8])).

tff(c_10376,plain,(
    ! [B_245,A_246] : k2_xboole_0(B_245,k4_xboole_0(A_246,k5_xboole_0(A_246,B_245))) = B_245 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4317])).

tff(c_10475,plain,(
    ! [A_1,B_2] : k2_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(A_1,k4_xboole_0(B_2,A_1))) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_4710,c_10376])).

tff(c_20670,plain,(
    ! [A_332,B_333] : k2_xboole_0(A_332,k2_xboole_0(A_332,B_333)) = k2_xboole_0(A_332,B_333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10223,c_10475])).

tff(c_20758,plain,(
    ! [A_332,B_333] : k5_xboole_0(k2_xboole_0(A_332,B_333),A_332) = k4_xboole_0(k2_xboole_0(A_332,B_333),A_332) ),
    inference(superposition,[status(thm),theory(equality)],[c_20670,c_6320])).

tff(c_25627,plain,(
    ! [A_362,B_363] : k4_xboole_0(k2_xboole_0(A_362,B_363),A_362) = k4_xboole_0(B_363,A_362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6320,c_20758])).

tff(c_25817,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25627])).

tff(c_38,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_29153,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25817,c_38])).

tff(c_29437,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_29153])).

tff(c_29441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_29437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.42/5.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.46/5.59  
% 11.46/5.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.46/5.59  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.46/5.59  
% 11.46/5.59  %Foreground sorts:
% 11.46/5.59  
% 11.46/5.59  
% 11.46/5.59  %Background operators:
% 11.46/5.59  
% 11.46/5.59  
% 11.46/5.59  %Foreground operators:
% 11.46/5.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.46/5.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.46/5.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.46/5.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.46/5.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.46/5.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.46/5.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.46/5.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.46/5.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.46/5.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.46/5.59  tff('#skF_2', type, '#skF_2': $i).
% 11.46/5.59  tff('#skF_3', type, '#skF_3': $i).
% 11.46/5.59  tff('#skF_1', type, '#skF_1': $i).
% 11.46/5.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.46/5.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.46/5.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.46/5.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.46/5.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.46/5.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.46/5.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.46/5.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.46/5.59  
% 11.46/5.61  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 11.46/5.61  tff(f_71, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 11.46/5.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.46/5.61  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.46/5.61  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 11.46/5.61  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.46/5.61  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.46/5.61  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.46/5.61  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.46/5.61  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.46/5.61  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 11.46/5.61  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.46/5.61  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/5.61  tff(c_40, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/5.61  tff(c_36, plain, (![C_51, A_49, B_50]: (k4_xboole_0(C_51, k2_tarski(A_49, B_50))=C_51 | r2_hidden(B_50, C_51) | r2_hidden(A_49, C_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.46/5.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.46/5.61  tff(c_69, plain, (![B_54, A_55]: (k5_xboole_0(B_54, A_55)=k5_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.46/5.61  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.46/5.61  tff(c_85, plain, (![A_55]: (k5_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_69, c_12])).
% 11.46/5.61  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.46/5.61  tff(c_738, plain, (![A_91, B_92]: (k5_xboole_0(k5_xboole_0(A_91, B_92), k2_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.46/5.61  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/5.61  tff(c_3106, plain, (![A_158, B_159]: (k5_xboole_0(A_158, k5_xboole_0(B_159, k2_xboole_0(A_158, B_159)))=k3_xboole_0(A_158, B_159))), inference(superposition, [status(thm), theory('equality')], [c_738, c_14])).
% 11.46/5.61  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.46/5.61  tff(c_489, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.46/5.61  tff(c_549, plain, (![A_15, C_86]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_86))=k5_xboole_0(k1_xboole_0, C_86))), inference(superposition, [status(thm), theory('equality')], [c_16, c_489])).
% 11.46/5.61  tff(c_567, plain, (![A_15, C_86]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_86))=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_549])).
% 11.46/5.61  tff(c_3151, plain, (![B_159, A_158]: (k5_xboole_0(B_159, k2_xboole_0(A_158, B_159))=k5_xboole_0(A_158, k3_xboole_0(A_158, B_159)))), inference(superposition, [status(thm), theory('equality')], [c_3106, c_567])).
% 11.46/5.61  tff(c_4604, plain, (![B_180, A_181]: (k5_xboole_0(B_180, k2_xboole_0(A_181, B_180))=k4_xboole_0(A_181, B_180))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3151])).
% 11.46/5.61  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.46/5.61  tff(c_2087, plain, (![C_145, A_146, B_147]: (k5_xboole_0(C_145, k5_xboole_0(A_146, B_147))=k5_xboole_0(A_146, k5_xboole_0(B_147, C_145)))), inference(superposition, [status(thm), theory('equality')], [c_489, c_4])).
% 11.46/5.61  tff(c_2380, plain, (![A_55, C_145]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_55, C_145))=k5_xboole_0(C_145, A_55))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2087])).
% 11.46/5.61  tff(c_4619, plain, (![A_181, B_180]: (k5_xboole_0(k2_xboole_0(A_181, B_180), B_180)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_181, B_180)))), inference(superposition, [status(thm), theory('equality')], [c_4604, c_2380])).
% 11.46/5.61  tff(c_6180, plain, (![A_200, B_201]: (k5_xboole_0(k2_xboole_0(A_200, B_201), B_201)=k4_xboole_0(A_200, B_201))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4619])).
% 11.46/5.61  tff(c_6320, plain, (![B_2, A_1]: (k5_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6180])).
% 11.46/5.61  tff(c_3840, plain, (![A_170, B_171]: (k5_xboole_0(k5_xboole_0(A_170, B_171), k2_xboole_0(B_171, A_170))=k3_xboole_0(A_170, B_171))), inference(superposition, [status(thm), theory('equality')], [c_2, c_738])).
% 11.46/5.61  tff(c_826, plain, (![A_3, B_4]: (k5_xboole_0(k5_xboole_0(A_3, B_4), k2_xboole_0(B_4, A_3))=k3_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_738])).
% 11.46/5.61  tff(c_3855, plain, (![B_171, A_170]: (k3_xboole_0(B_171, A_170)=k3_xboole_0(A_170, B_171))), inference(superposition, [status(thm), theory('equality')], [c_3840, c_826])).
% 11.46/5.61  tff(c_4710, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4604])).
% 11.46/5.61  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.46/5.61  tff(c_5451, plain, (![A_190, B_191]: (k5_xboole_0(A_190, k2_xboole_0(A_190, B_191))=k4_xboole_0(B_191, A_190))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4604])).
% 11.46/5.61  tff(c_5567, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k4_xboole_0(k4_xboole_0(B_10, A_9), A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_5451])).
% 11.46/5.61  tff(c_10008, plain, (![B_239, A_240]: (k4_xboole_0(k4_xboole_0(B_239, A_240), A_240)=k4_xboole_0(B_239, A_240))), inference(demodulation, [status(thm), theory('equality')], [c_4710, c_5567])).
% 11.46/5.61  tff(c_570, plain, (![A_87, C_88]: (k5_xboole_0(A_87, k5_xboole_0(A_87, C_88))=C_88)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_549])).
% 11.46/5.61  tff(c_606, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_570])).
% 11.46/5.61  tff(c_4108, plain, (![A_174, C_175]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_174, C_175))=k5_xboole_0(C_175, A_174))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2087])).
% 11.46/5.61  tff(c_4225, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_606, c_4108])).
% 11.46/5.61  tff(c_4303, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4225])).
% 11.46/5.61  tff(c_10054, plain, (![B_239, A_240]: (k5_xboole_0(k4_xboole_0(B_239, A_240), k4_xboole_0(B_239, A_240))=k3_xboole_0(k4_xboole_0(B_239, A_240), A_240))), inference(superposition, [status(thm), theory('equality')], [c_10008, c_4303])).
% 11.46/5.61  tff(c_10154, plain, (![A_241, B_242]: (k3_xboole_0(A_241, k4_xboole_0(B_242, A_241))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_16, c_10054])).
% 11.46/5.61  tff(c_4254, plain, (![A_5, B_6]: (k5_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4108])).
% 11.46/5.61  tff(c_4311, plain, (![A_5, B_6]: (k5_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k4_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4254])).
% 11.46/5.61  tff(c_10168, plain, (![A_241, B_242]: (k4_xboole_0(A_241, k4_xboole_0(B_242, A_241))=k5_xboole_0(k1_xboole_0, A_241))), inference(superposition, [status(thm), theory('equality')], [c_10154, c_4311])).
% 11.46/5.61  tff(c_10223, plain, (![A_241, B_242]: (k4_xboole_0(A_241, k4_xboole_0(B_242, A_241))=A_241)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_10168])).
% 11.46/5.61  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), k5_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.46/5.61  tff(c_1328, plain, (![A_127, C_128]: (r1_tarski(k4_xboole_0(A_127, k5_xboole_0(A_127, C_128)), C_128))), inference(superposition, [status(thm), theory('equality')], [c_570, c_20])).
% 11.46/5.61  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.46/5.61  tff(c_4317, plain, (![A_176, C_177]: (k2_xboole_0(k4_xboole_0(A_176, k5_xboole_0(A_176, C_177)), C_177)=C_177)), inference(resolution, [status(thm)], [c_1328, c_8])).
% 11.46/5.61  tff(c_10376, plain, (![B_245, A_246]: (k2_xboole_0(B_245, k4_xboole_0(A_246, k5_xboole_0(A_246, B_245)))=B_245)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4317])).
% 11.46/5.61  tff(c_10475, plain, (![A_1, B_2]: (k2_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(A_1, k4_xboole_0(B_2, A_1)))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_4710, c_10376])).
% 11.46/5.61  tff(c_20670, plain, (![A_332, B_333]: (k2_xboole_0(A_332, k2_xboole_0(A_332, B_333))=k2_xboole_0(A_332, B_333))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10223, c_10475])).
% 11.46/5.61  tff(c_20758, plain, (![A_332, B_333]: (k5_xboole_0(k2_xboole_0(A_332, B_333), A_332)=k4_xboole_0(k2_xboole_0(A_332, B_333), A_332))), inference(superposition, [status(thm), theory('equality')], [c_20670, c_6320])).
% 11.46/5.61  tff(c_25627, plain, (![A_362, B_363]: (k4_xboole_0(k2_xboole_0(A_362, B_363), A_362)=k4_xboole_0(B_363, A_362))), inference(demodulation, [status(thm), theory('equality')], [c_6320, c_20758])).
% 11.46/5.61  tff(c_25817, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_25627])).
% 11.46/5.61  tff(c_38, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/5.61  tff(c_29153, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25817, c_38])).
% 11.46/5.61  tff(c_29437, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_29153])).
% 11.46/5.61  tff(c_29441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_29437])).
% 11.46/5.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.46/5.61  
% 11.46/5.61  Inference rules
% 11.46/5.61  ----------------------
% 11.46/5.61  #Ref     : 0
% 11.46/5.61  #Sup     : 7637
% 11.46/5.61  #Fact    : 0
% 11.46/5.61  #Define  : 0
% 11.46/5.61  #Split   : 1
% 11.46/5.61  #Chain   : 0
% 11.46/5.61  #Close   : 0
% 11.46/5.61  
% 11.46/5.61  Ordering : KBO
% 11.46/5.61  
% 11.46/5.61  Simplification rules
% 11.46/5.61  ----------------------
% 11.46/5.61  #Subsume      : 193
% 11.46/5.61  #Demod        : 10355
% 11.46/5.61  #Tautology    : 3751
% 11.46/5.61  #SimpNegUnit  : 1
% 11.46/5.61  #BackRed      : 27
% 11.46/5.61  
% 11.46/5.61  #Partial instantiations: 0
% 11.46/5.61  #Strategies tried      : 1
% 11.46/5.61  
% 11.46/5.61  Timing (in seconds)
% 11.46/5.61  ----------------------
% 11.46/5.61  Preprocessing        : 0.34
% 11.46/5.61  Parsing              : 0.18
% 11.46/5.61  CNF conversion       : 0.02
% 11.46/5.61  Main loop            : 4.46
% 11.46/5.61  Inferencing          : 0.73
% 11.46/5.61  Reduction            : 2.82
% 11.46/5.61  Demodulation         : 2.59
% 11.46/5.61  BG Simplification    : 0.12
% 11.46/5.61  Subsumption          : 0.59
% 11.46/5.61  Abstraction          : 0.18
% 11.46/5.61  MUC search           : 0.00
% 11.46/5.61  Cooper               : 0.00
% 11.46/5.61  Total                : 4.83
% 11.46/5.61  Index Insertion      : 0.00
% 11.46/5.61  Index Deletion       : 0.00
% 11.46/5.61  Index Matching       : 0.00
% 11.46/5.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
