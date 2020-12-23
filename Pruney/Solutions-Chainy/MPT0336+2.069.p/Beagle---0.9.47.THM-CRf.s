%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 197 expanded)
%              Number of leaves         :   32 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 291 expanded)
%              Number of equality atoms :   50 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_81,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
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

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_30,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_791,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_xboole_0(A_88,B_89)
      | ~ r1_xboole_0(A_88,k2_xboole_0(B_89,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1855,plain,(
    ! [A_125,B_126,C_127] : r1_xboole_0(k4_xboole_0(A_125,k2_xboole_0(B_126,C_127)),B_126) ),
    inference(resolution,[status(thm)],[c_30,c_791])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4261,plain,(
    ! [A_195,B_196,C_197] : k3_xboole_0(k4_xboole_0(A_195,k2_xboole_0(B_196,C_197)),B_196) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1855,c_4])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_132,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_140,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k4_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_4417,plain,(
    ! [B_198,C_199] : k4_xboole_0(B_198,k2_xboole_0(B_198,C_199)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4261,c_140])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_643,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_xboole_0(A_81,C_82)
      | ~ r1_xboole_0(A_81,k2_xboole_0(B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_671,plain,(
    ! [A_26,C_82,B_83] :
      ( r1_xboole_0(A_26,C_82)
      | k4_xboole_0(A_26,k2_xboole_0(B_83,C_82)) != A_26 ) ),
    inference(resolution,[status(thm)],[c_34,c_643])).

tff(c_4568,plain,(
    ! [B_200,C_201] :
      ( r1_xboole_0(B_200,C_201)
      | k1_xboole_0 != B_200 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4417,c_671])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4599,plain,(
    ! [C_202,B_203] :
      ( r1_xboole_0(C_202,B_203)
      | k1_xboole_0 != B_203 ) ),
    inference(resolution,[status(thm)],[c_4568,c_8])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6280,plain,(
    ! [C_202] : k4_xboole_0(C_202,k1_xboole_0) = C_202 ),
    inference(resolution,[status(thm)],[c_4599,c_32])).

tff(c_98,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,A_44)
      | ~ r1_xboole_0(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_25,A_24] : r1_xboole_0(B_25,k4_xboole_0(A_24,B_25)) ),
    inference(resolution,[status(thm)],[c_30,c_98])).

tff(c_141,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [B_25,A_24] : k3_xboole_0(B_25,k4_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_141])).

tff(c_246,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = A_61
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,(
    ! [B_25,A_24] : k4_xboole_0(B_25,k4_xboole_0(A_24,B_25)) = B_25 ),
    inference(resolution,[status(thm)],[c_103,c_246])).

tff(c_478,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_518,plain,(
    ! [B_25,A_24] : k3_xboole_0(B_25,k4_xboole_0(A_24,B_25)) = k4_xboole_0(B_25,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_478])).

tff(c_681,plain,(
    ! [B_84] : k4_xboole_0(B_84,B_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_518])).

tff(c_160,plain,(
    ! [A_24,B_25] : k3_xboole_0(k4_xboole_0(A_24,B_25),B_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_699,plain,(
    ! [B_84] : k3_xboole_0(k1_xboole_0,B_84) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_160])).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_161,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_1291,plain,(
    ! [A_107,B_108,C_109] : k3_xboole_0(k3_xboole_0(A_107,B_108),C_109) = k3_xboole_0(A_107,k3_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1366,plain,(
    ! [C_109] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_109)) = k3_xboole_0(k1_xboole_0,C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_1291])).

tff(c_1394,plain,(
    ! [C_109] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_109)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_1366])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_139,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_132])).

tff(c_532,plain,(
    ! [B_25] : k4_xboole_0(B_25,B_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_518])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,k1_tarski(B_35)) = A_34
      | r2_hidden(B_35,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_515,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,A_34) = k3_xboole_0(A_34,k1_tarski(B_35))
      | r2_hidden(B_35,A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_478])).

tff(c_12099,plain,(
    ! [A_274,B_275] :
      ( k3_xboole_0(A_274,k1_tarski(B_275)) = k1_xboole_0
      | r2_hidden(B_275,A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_515])).

tff(c_12296,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_12099])).

tff(c_12372,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12296])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1117,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,B_99)
      | ~ r2_hidden(C_100,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12417,plain,(
    ! [C_278,B_279,A_280] :
      ( ~ r2_hidden(C_278,B_279)
      | ~ r2_hidden(C_278,A_280)
      | k3_xboole_0(A_280,B_279) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1117])).

tff(c_12664,plain,(
    ! [A_282] :
      ( ~ r2_hidden('#skF_5',A_282)
      | k3_xboole_0(A_282,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_12417])).

tff(c_12667,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12372,c_12664])).

tff(c_12678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_2,c_12667])).

tff(c_12679,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12296])).

tff(c_3037,plain,(
    ! [A_163,B_164] : k3_xboole_0(k4_xboole_0(A_163,B_164),A_163) = k4_xboole_0(A_163,B_164) ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_3101,plain,(
    ! [A_163,B_164] : k3_xboole_0(A_163,k4_xboole_0(A_163,B_164)) = k4_xboole_0(A_163,B_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_3037,c_2])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_509,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_478])).

tff(c_6771,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3101,c_509])).

tff(c_12725,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12679,c_6771])).

tff(c_12799,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6280,c_12725])).

tff(c_12900,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12799,c_30])).

tff(c_104,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_1598,plain,(
    ! [A_117,C_118,B_119] :
      ( ~ r1_xboole_0(A_117,C_118)
      | ~ r1_xboole_0(A_117,B_119)
      | r1_xboole_0(A_117,k2_xboole_0(B_119,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14312,plain,(
    ! [B_293,C_294,A_295] :
      ( r1_xboole_0(k2_xboole_0(B_293,C_294),A_295)
      | ~ r1_xboole_0(A_295,C_294)
      | ~ r1_xboole_0(A_295,B_293) ) ),
    inference(resolution,[status(thm)],[c_1598,c_8])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14333,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_14312,c_46])).

tff(c_14343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12900,c_104,c_14333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:29:27 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.01/2.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.81  
% 8.01/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.01/2.82  
% 8.01/2.82  %Foreground sorts:
% 8.01/2.82  
% 8.01/2.82  
% 8.01/2.82  %Background operators:
% 8.01/2.82  
% 8.01/2.82  
% 8.01/2.82  %Foreground operators:
% 8.01/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.01/2.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.01/2.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.01/2.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.01/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.01/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.01/2.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.01/2.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.01/2.82  tff('#skF_5', type, '#skF_5': $i).
% 8.01/2.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.01/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.01/2.82  tff('#skF_2', type, '#skF_2': $i).
% 8.01/2.82  tff('#skF_3', type, '#skF_3': $i).
% 8.01/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.01/2.82  tff('#skF_4', type, '#skF_4': $i).
% 8.01/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.01/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.01/2.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.01/2.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.01/2.82  
% 8.01/2.83  tff(f_81, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.01/2.83  tff(f_79, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.01/2.83  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.01/2.83  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.01/2.83  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.01/2.83  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.01/2.83  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.01/2.83  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.01/2.83  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.01/2.83  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 8.01/2.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.01/2.83  tff(f_96, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 8.01/2.83  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.01/2.83  tff(c_30, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.01/2.83  tff(c_791, plain, (![A_88, B_89, C_90]: (r1_xboole_0(A_88, B_89) | ~r1_xboole_0(A_88, k2_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.01/2.83  tff(c_1855, plain, (![A_125, B_126, C_127]: (r1_xboole_0(k4_xboole_0(A_125, k2_xboole_0(B_126, C_127)), B_126))), inference(resolution, [status(thm)], [c_30, c_791])).
% 8.01/2.83  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.83  tff(c_4261, plain, (![A_195, B_196, C_197]: (k3_xboole_0(k4_xboole_0(A_195, k2_xboole_0(B_196, C_197)), B_196)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1855, c_4])).
% 8.01/2.83  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.01/2.83  tff(c_132, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.01/2.83  tff(c_140, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k4_xboole_0(A_17, B_18))), inference(resolution, [status(thm)], [c_20, c_132])).
% 8.01/2.83  tff(c_4417, plain, (![B_198, C_199]: (k4_xboole_0(B_198, k2_xboole_0(B_198, C_199))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4261, c_140])).
% 8.01/2.83  tff(c_34, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k4_xboole_0(A_26, B_27)!=A_26)), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.83  tff(c_643, plain, (![A_81, C_82, B_83]: (r1_xboole_0(A_81, C_82) | ~r1_xboole_0(A_81, k2_xboole_0(B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.01/2.83  tff(c_671, plain, (![A_26, C_82, B_83]: (r1_xboole_0(A_26, C_82) | k4_xboole_0(A_26, k2_xboole_0(B_83, C_82))!=A_26)), inference(resolution, [status(thm)], [c_34, c_643])).
% 8.01/2.83  tff(c_4568, plain, (![B_200, C_201]: (r1_xboole_0(B_200, C_201) | k1_xboole_0!=B_200)), inference(superposition, [status(thm), theory('equality')], [c_4417, c_671])).
% 8.01/2.83  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.01/2.83  tff(c_4599, plain, (![C_202, B_203]: (r1_xboole_0(C_202, B_203) | k1_xboole_0!=B_203)), inference(resolution, [status(thm)], [c_4568, c_8])).
% 8.01/2.83  tff(c_32, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.83  tff(c_6280, plain, (![C_202]: (k4_xboole_0(C_202, k1_xboole_0)=C_202)), inference(resolution, [status(thm)], [c_4599, c_32])).
% 8.01/2.83  tff(c_98, plain, (![B_43, A_44]: (r1_xboole_0(B_43, A_44) | ~r1_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.01/2.83  tff(c_103, plain, (![B_25, A_24]: (r1_xboole_0(B_25, k4_xboole_0(A_24, B_25)))), inference(resolution, [status(thm)], [c_30, c_98])).
% 8.01/2.83  tff(c_141, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.83  tff(c_158, plain, (![B_25, A_24]: (k3_xboole_0(B_25, k4_xboole_0(A_24, B_25))=k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_141])).
% 8.01/2.83  tff(c_246, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=A_61 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.83  tff(c_267, plain, (![B_25, A_24]: (k4_xboole_0(B_25, k4_xboole_0(A_24, B_25))=B_25)), inference(resolution, [status(thm)], [c_103, c_246])).
% 8.01/2.83  tff(c_478, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.01/2.83  tff(c_518, plain, (![B_25, A_24]: (k3_xboole_0(B_25, k4_xboole_0(A_24, B_25))=k4_xboole_0(B_25, B_25))), inference(superposition, [status(thm), theory('equality')], [c_267, c_478])).
% 8.01/2.83  tff(c_681, plain, (![B_84]: (k4_xboole_0(B_84, B_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_518])).
% 8.01/2.83  tff(c_160, plain, (![A_24, B_25]: (k3_xboole_0(k4_xboole_0(A_24, B_25), B_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_141])).
% 8.01/2.83  tff(c_699, plain, (![B_84]: (k3_xboole_0(k1_xboole_0, B_84)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_681, c_160])).
% 8.01/2.83  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.01/2.83  tff(c_161, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_141])).
% 8.01/2.83  tff(c_1291, plain, (![A_107, B_108, C_109]: (k3_xboole_0(k3_xboole_0(A_107, B_108), C_109)=k3_xboole_0(A_107, k3_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.01/2.83  tff(c_1366, plain, (![C_109]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_109))=k3_xboole_0(k1_xboole_0, C_109))), inference(superposition, [status(thm), theory('equality')], [c_161, c_1291])).
% 8.01/2.83  tff(c_1394, plain, (![C_109]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_109))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_699, c_1366])).
% 8.01/2.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.01/2.83  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.01/2.83  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 8.01/2.83  tff(c_139, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_132])).
% 8.01/2.83  tff(c_532, plain, (![B_25]: (k4_xboole_0(B_25, B_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_518])).
% 8.01/2.83  tff(c_44, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k1_tarski(B_35))=A_34 | r2_hidden(B_35, A_34))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.01/2.83  tff(c_515, plain, (![A_34, B_35]: (k4_xboole_0(A_34, A_34)=k3_xboole_0(A_34, k1_tarski(B_35)) | r2_hidden(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_44, c_478])).
% 8.01/2.83  tff(c_12099, plain, (![A_274, B_275]: (k3_xboole_0(A_274, k1_tarski(B_275))=k1_xboole_0 | r2_hidden(B_275, A_274))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_515])).
% 8.01/2.83  tff(c_12296, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_12099])).
% 8.01/2.83  tff(c_12372, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_12296])).
% 8.01/2.83  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.01/2.83  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.83  tff(c_1117, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, B_99) | ~r2_hidden(C_100, A_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.01/2.83  tff(c_12417, plain, (![C_278, B_279, A_280]: (~r2_hidden(C_278, B_279) | ~r2_hidden(C_278, A_280) | k3_xboole_0(A_280, B_279)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1117])).
% 8.01/2.83  tff(c_12664, plain, (![A_282]: (~r2_hidden('#skF_5', A_282) | k3_xboole_0(A_282, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_12417])).
% 8.01/2.83  tff(c_12667, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12372, c_12664])).
% 8.01/2.83  tff(c_12678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1394, c_2, c_12667])).
% 8.01/2.83  tff(c_12679, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12296])).
% 8.01/2.83  tff(c_3037, plain, (![A_163, B_164]: (k3_xboole_0(k4_xboole_0(A_163, B_164), A_163)=k4_xboole_0(A_163, B_164))), inference(resolution, [status(thm)], [c_20, c_132])).
% 8.01/2.83  tff(c_3101, plain, (![A_163, B_164]: (k3_xboole_0(A_163, k4_xboole_0(A_163, B_164))=k4_xboole_0(A_163, B_164))), inference(superposition, [status(thm), theory('equality')], [c_3037, c_2])).
% 8.01/2.83  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.01/2.83  tff(c_509, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k3_xboole_0(A_19, k4_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_478])).
% 8.01/2.83  tff(c_6771, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_3101, c_509])).
% 8.01/2.83  tff(c_12725, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12679, c_6771])).
% 8.01/2.83  tff(c_12799, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6280, c_12725])).
% 8.01/2.83  tff(c_12900, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12799, c_30])).
% 8.01/2.83  tff(c_104, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_98])).
% 8.01/2.83  tff(c_1598, plain, (![A_117, C_118, B_119]: (~r1_xboole_0(A_117, C_118) | ~r1_xboole_0(A_117, B_119) | r1_xboole_0(A_117, k2_xboole_0(B_119, C_118)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.01/2.83  tff(c_14312, plain, (![B_293, C_294, A_295]: (r1_xboole_0(k2_xboole_0(B_293, C_294), A_295) | ~r1_xboole_0(A_295, C_294) | ~r1_xboole_0(A_295, B_293))), inference(resolution, [status(thm)], [c_1598, c_8])).
% 8.01/2.83  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.01/2.83  tff(c_14333, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_14312, c_46])).
% 8.01/2.83  tff(c_14343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12900, c_104, c_14333])).
% 8.01/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.83  
% 8.01/2.83  Inference rules
% 8.01/2.83  ----------------------
% 8.01/2.83  #Ref     : 0
% 8.01/2.83  #Sup     : 3625
% 8.01/2.83  #Fact    : 0
% 8.01/2.83  #Define  : 0
% 8.01/2.83  #Split   : 3
% 8.01/2.83  #Chain   : 0
% 8.01/2.83  #Close   : 0
% 8.01/2.83  
% 8.01/2.83  Ordering : KBO
% 8.01/2.83  
% 8.01/2.83  Simplification rules
% 8.01/2.83  ----------------------
% 8.01/2.83  #Subsume      : 500
% 8.01/2.83  #Demod        : 2761
% 8.01/2.83  #Tautology    : 2250
% 8.01/2.83  #SimpNegUnit  : 71
% 8.01/2.83  #BackRed      : 12
% 8.01/2.83  
% 8.01/2.83  #Partial instantiations: 0
% 8.01/2.83  #Strategies tried      : 1
% 8.01/2.83  
% 8.01/2.83  Timing (in seconds)
% 8.01/2.83  ----------------------
% 8.01/2.84  Preprocessing        : 0.32
% 8.01/2.84  Parsing              : 0.17
% 8.01/2.84  CNF conversion       : 0.02
% 8.01/2.84  Main loop            : 1.73
% 8.01/2.84  Inferencing          : 0.43
% 8.01/2.84  Reduction            : 0.87
% 8.01/2.84  Demodulation         : 0.71
% 8.01/2.84  BG Simplification    : 0.05
% 8.01/2.84  Subsumption          : 0.28
% 8.01/2.84  Abstraction          : 0.06
% 8.01/2.84  MUC search           : 0.00
% 8.01/2.84  Cooper               : 0.00
% 8.01/2.84  Total                : 2.08
% 8.01/2.84  Index Insertion      : 0.00
% 8.01/2.84  Index Deletion       : 0.00
% 8.01/2.84  Index Matching       : 0.00
% 8.01/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
