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
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 12.66s
% Output     : CNFRefutation 12.66s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 162 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 256 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
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

tff(f_77,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_120,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_50,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_116,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,A_49)
      | ~ r1_xboole_0(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_1085,plain,(
    ! [A_124,C_125,B_126] :
      ( ~ r1_xboole_0(A_124,C_125)
      | ~ r1_xboole_0(A_124,B_126)
      | r1_xboole_0(A_124,k2_xboole_0(B_126,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4403,plain,(
    ! [B_216,C_217,A_218] :
      ( r1_xboole_0(k2_xboole_0(B_216,C_217),A_218)
      | ~ r1_xboole_0(A_218,C_217)
      | ~ r1_xboole_0(A_218,B_216) ) ),
    inference(resolution,[status(thm)],[c_1085,c_4])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4439,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4403,c_48])).

tff(c_4457,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_4439])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_647,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_666,plain,(
    ! [C_99] :
      ( ~ r2_hidden(C_99,'#skF_4')
      | ~ r2_hidden(C_99,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_647])).

tff(c_680,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_666])).

tff(c_26,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_288,plain,(
    ! [B_69,A_70] :
      ( ~ r2_hidden(B_69,A_70)
      | k4_xboole_0(A_70,k1_tarski(B_69)) != A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_297,plain,(
    ! [B_69] : ~ r2_hidden(B_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_288])).

tff(c_20,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_141,plain,(
    ! [A_53] : k3_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_53] : k3_xboole_0(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_30,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_443,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(k2_xboole_0(A_84,B_85),B_85) = A_84
      | ~ r1_xboole_0(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_467,plain,(
    ! [A_15] :
      ( k4_xboole_0(A_15,k1_xboole_0) = A_15
      | ~ r1_xboole_0(A_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_443])).

tff(c_473,plain,(
    ! [A_86] : k4_xboole_0(A_86,k1_xboole_0) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_467])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_483,plain,(
    ! [A_86] : k4_xboole_0(A_86,A_86) = k3_xboole_0(A_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_22])).

tff(c_502,plain,(
    ! [A_86] : k4_xboole_0(A_86,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_483])).

tff(c_46,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,k1_tarski(B_40)) = A_39
      | r2_hidden(B_40,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_256,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_275,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,A_39) = k3_xboole_0(A_39,k1_tarski(B_40))
      | r2_hidden(B_40,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_256])).

tff(c_3691,plain,(
    ! [A_203,B_204] :
      ( k3_xboole_0(A_203,k1_tarski(B_204)) = k1_xboole_0
      | r2_hidden(B_204,A_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_275])).

tff(c_3731,plain,(
    ! [A_203,B_204] :
      ( r2_hidden('#skF_2'(A_203,k1_tarski(B_204)),k1_xboole_0)
      | r1_xboole_0(A_203,k1_tarski(B_204))
      | r2_hidden(B_204,A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3691,c_12])).

tff(c_3805,plain,(
    ! [A_203,B_204] :
      ( r1_xboole_0(A_203,k1_tarski(B_204))
      | r2_hidden(B_204,A_203) ) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_3731])).

tff(c_54,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_55,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_139,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_132])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_311,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,k3_xboole_0(A_72,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_348,plain,(
    ! [A_75,B_76,A_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | r1_xboole_0(A_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_8,c_311])).

tff(c_356,plain,(
    ! [A_77] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | r1_xboole_0(A_77,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_348])).

tff(c_19418,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_19434,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3805,c_19418])).

tff(c_944,plain,(
    ! [A_116,B_117,C_118] : k4_xboole_0(k3_xboole_0(A_116,B_117),C_118) = k3_xboole_0(A_116,k4_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [B_40,A_39] :
      ( ~ r2_hidden(B_40,A_39)
      | k4_xboole_0(A_39,k1_tarski(B_40)) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8811,plain,(
    ! [B_289,A_290,B_291] :
      ( ~ r2_hidden(B_289,k3_xboole_0(A_290,B_291))
      | k3_xboole_0(A_290,k4_xboole_0(B_291,k1_tarski(B_289))) != k3_xboole_0(A_290,B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_44])).

tff(c_11773,plain,(
    ! [B_364,A_365,A_366] :
      ( ~ r2_hidden(B_364,k3_xboole_0(A_365,A_366))
      | r2_hidden(B_364,A_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8811])).

tff(c_29338,plain,(
    ! [B_596,B_597,A_598] :
      ( ~ r2_hidden(B_596,k3_xboole_0(B_597,A_598))
      | r2_hidden(B_596,B_597) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11773])).

tff(c_29362,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_19434,c_29338])).

tff(c_29486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_29362])).

tff(c_29489,plain,(
    ! [A_599] : r1_xboole_0(A_599,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_29545,plain,(
    ! [A_600] : r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_600) ),
    inference(resolution,[status(thm)],[c_29489,c_4])).

tff(c_472,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_467])).

tff(c_508,plain,(
    ! [A_87] : k4_xboole_0(A_87,A_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_483])).

tff(c_521,plain,(
    ! [A_87] : k4_xboole_0(A_87,k1_xboole_0) = k3_xboole_0(A_87,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_22])).

tff(c_549,plain,(
    ! [A_88] : k3_xboole_0(A_88,A_88) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_521])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_564,plain,(
    ! [A_88,C_14] :
      ( ~ r1_xboole_0(A_88,A_88)
      | ~ r2_hidden(C_14,A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_14])).

tff(c_29621,plain,(
    ! [C_601] : ~ r2_hidden(C_601,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_29545,c_564])).

tff(c_29633,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_29621])).

tff(c_29648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4457,c_29633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.66/5.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.66/5.61  
% 12.66/5.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.66/5.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 12.66/5.61  
% 12.66/5.61  %Foreground sorts:
% 12.66/5.61  
% 12.66/5.61  
% 12.66/5.61  %Background operators:
% 12.66/5.61  
% 12.66/5.61  
% 12.66/5.61  %Foreground operators:
% 12.66/5.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.66/5.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.66/5.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.66/5.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.66/5.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.66/5.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.66/5.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.66/5.61  tff('#skF_5', type, '#skF_5': $i).
% 12.66/5.61  tff('#skF_6', type, '#skF_6': $i).
% 12.66/5.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.66/5.61  tff('#skF_3', type, '#skF_3': $i).
% 12.66/5.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.66/5.61  tff('#skF_4', type, '#skF_4': $i).
% 12.66/5.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.66/5.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.66/5.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.66/5.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.66/5.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.66/5.61  
% 12.66/5.63  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 12.66/5.63  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.66/5.63  tff(f_101, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 12.66/5.63  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.66/5.63  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 12.66/5.63  tff(f_77, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 12.66/5.63  tff(f_120, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 12.66/5.63  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.66/5.63  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.66/5.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.66/5.63  tff(f_85, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.66/5.63  tff(f_65, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 12.66/5.63  tff(f_113, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 12.66/5.63  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.66/5.63  tff(f_75, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.66/5.63  tff(c_50, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.66/5.63  tff(c_116, plain, (![B_48, A_49]: (r1_xboole_0(B_48, A_49) | ~r1_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.66/5.63  tff(c_122, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_116])).
% 12.66/5.63  tff(c_1085, plain, (![A_124, C_125, B_126]: (~r1_xboole_0(A_124, C_125) | ~r1_xboole_0(A_124, B_126) | r1_xboole_0(A_124, k2_xboole_0(B_126, C_125)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.66/5.63  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.66/5.63  tff(c_4403, plain, (![B_216, C_217, A_218]: (r1_xboole_0(k2_xboole_0(B_216, C_217), A_218) | ~r1_xboole_0(A_218, C_217) | ~r1_xboole_0(A_218, B_216))), inference(resolution, [status(thm)], [c_1085, c_4])).
% 12.66/5.63  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.66/5.63  tff(c_4439, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4403, c_48])).
% 12.66/5.63  tff(c_4457, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_4439])).
% 12.66/5.63  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.66/5.63  tff(c_52, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.66/5.63  tff(c_647, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.66/5.63  tff(c_666, plain, (![C_99]: (~r2_hidden(C_99, '#skF_4') | ~r2_hidden(C_99, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_647])).
% 12.66/5.63  tff(c_680, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_666])).
% 12.66/5.63  tff(c_26, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.66/5.63  tff(c_288, plain, (![B_69, A_70]: (~r2_hidden(B_69, A_70) | k4_xboole_0(A_70, k1_tarski(B_69))!=A_70)), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.66/5.63  tff(c_297, plain, (![B_69]: (~r2_hidden(B_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_288])).
% 12.66/5.63  tff(c_20, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.66/5.63  tff(c_132, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.66/5.63  tff(c_141, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_132])).
% 12.66/5.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.66/5.63  tff(c_146, plain, (![A_53]: (k3_xboole_0(A_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141, c_2])).
% 12.66/5.63  tff(c_30, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.66/5.63  tff(c_16, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.66/5.63  tff(c_443, plain, (![A_84, B_85]: (k4_xboole_0(k2_xboole_0(A_84, B_85), B_85)=A_84 | ~r1_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.66/5.63  tff(c_467, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15 | ~r1_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_443])).
% 12.66/5.63  tff(c_473, plain, (![A_86]: (k4_xboole_0(A_86, k1_xboole_0)=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_467])).
% 12.66/5.63  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.66/5.63  tff(c_483, plain, (![A_86]: (k4_xboole_0(A_86, A_86)=k3_xboole_0(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_473, c_22])).
% 12.66/5.63  tff(c_502, plain, (![A_86]: (k4_xboole_0(A_86, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_483])).
% 12.66/5.63  tff(c_46, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k1_tarski(B_40))=A_39 | r2_hidden(B_40, A_39))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.66/5.63  tff(c_256, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.66/5.63  tff(c_275, plain, (![A_39, B_40]: (k4_xboole_0(A_39, A_39)=k3_xboole_0(A_39, k1_tarski(B_40)) | r2_hidden(B_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_46, c_256])).
% 12.66/5.63  tff(c_3691, plain, (![A_203, B_204]: (k3_xboole_0(A_203, k1_tarski(B_204))=k1_xboole_0 | r2_hidden(B_204, A_203))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_275])).
% 12.66/5.63  tff(c_3731, plain, (![A_203, B_204]: (r2_hidden('#skF_2'(A_203, k1_tarski(B_204)), k1_xboole_0) | r1_xboole_0(A_203, k1_tarski(B_204)) | r2_hidden(B_204, A_203))), inference(superposition, [status(thm), theory('equality')], [c_3691, c_12])).
% 12.66/5.63  tff(c_3805, plain, (![A_203, B_204]: (r1_xboole_0(A_203, k1_tarski(B_204)) | r2_hidden(B_204, A_203))), inference(negUnitSimplification, [status(thm)], [c_297, c_3731])).
% 12.66/5.63  tff(c_54, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.66/5.63  tff(c_55, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_54])).
% 12.66/5.63  tff(c_139, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_55, c_132])).
% 12.66/5.63  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.66/5.63  tff(c_311, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, k3_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.66/5.63  tff(c_348, plain, (![A_75, B_76, A_77]: (~r1_xboole_0(A_75, B_76) | r1_xboole_0(A_77, k3_xboole_0(A_75, B_76)))), inference(resolution, [status(thm)], [c_8, c_311])).
% 12.66/5.63  tff(c_356, plain, (![A_77]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | r1_xboole_0(A_77, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_348])).
% 12.66/5.63  tff(c_19418, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_356])).
% 12.66/5.63  tff(c_19434, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_3805, c_19418])).
% 12.66/5.63  tff(c_944, plain, (![A_116, B_117, C_118]: (k4_xboole_0(k3_xboole_0(A_116, B_117), C_118)=k3_xboole_0(A_116, k4_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.66/5.63  tff(c_44, plain, (![B_40, A_39]: (~r2_hidden(B_40, A_39) | k4_xboole_0(A_39, k1_tarski(B_40))!=A_39)), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.66/5.63  tff(c_8811, plain, (![B_289, A_290, B_291]: (~r2_hidden(B_289, k3_xboole_0(A_290, B_291)) | k3_xboole_0(A_290, k4_xboole_0(B_291, k1_tarski(B_289)))!=k3_xboole_0(A_290, B_291))), inference(superposition, [status(thm), theory('equality')], [c_944, c_44])).
% 12.66/5.63  tff(c_11773, plain, (![B_364, A_365, A_366]: (~r2_hidden(B_364, k3_xboole_0(A_365, A_366)) | r2_hidden(B_364, A_366))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8811])).
% 12.66/5.63  tff(c_29338, plain, (![B_596, B_597, A_598]: (~r2_hidden(B_596, k3_xboole_0(B_597, A_598)) | r2_hidden(B_596, B_597))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11773])).
% 12.66/5.63  tff(c_29362, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_19434, c_29338])).
% 12.66/5.63  tff(c_29486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_680, c_29362])).
% 12.66/5.63  tff(c_29489, plain, (![A_599]: (r1_xboole_0(A_599, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_356])).
% 12.66/5.63  tff(c_29545, plain, (![A_600]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_600))), inference(resolution, [status(thm)], [c_29489, c_4])).
% 12.66/5.63  tff(c_472, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_467])).
% 12.66/5.63  tff(c_508, plain, (![A_87]: (k4_xboole_0(A_87, A_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_483])).
% 12.66/5.63  tff(c_521, plain, (![A_87]: (k4_xboole_0(A_87, k1_xboole_0)=k3_xboole_0(A_87, A_87))), inference(superposition, [status(thm), theory('equality')], [c_508, c_22])).
% 12.66/5.63  tff(c_549, plain, (![A_88]: (k3_xboole_0(A_88, A_88)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_472, c_521])).
% 12.66/5.63  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.66/5.63  tff(c_564, plain, (![A_88, C_14]: (~r1_xboole_0(A_88, A_88) | ~r2_hidden(C_14, A_88))), inference(superposition, [status(thm), theory('equality')], [c_549, c_14])).
% 12.66/5.63  tff(c_29621, plain, (![C_601]: (~r2_hidden(C_601, k3_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_29545, c_564])).
% 12.66/5.63  tff(c_29633, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_29621])).
% 12.66/5.63  tff(c_29648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4457, c_29633])).
% 12.66/5.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.66/5.63  
% 12.66/5.63  Inference rules
% 12.66/5.63  ----------------------
% 12.66/5.63  #Ref     : 3
% 12.66/5.63  #Sup     : 7497
% 12.66/5.63  #Fact    : 0
% 12.66/5.63  #Define  : 0
% 12.66/5.63  #Split   : 12
% 12.66/5.63  #Chain   : 0
% 12.66/5.63  #Close   : 0
% 12.66/5.63  
% 12.66/5.63  Ordering : KBO
% 12.66/5.63  
% 12.66/5.63  Simplification rules
% 12.66/5.63  ----------------------
% 12.66/5.63  #Subsume      : 754
% 12.66/5.63  #Demod        : 5969
% 12.66/5.63  #Tautology    : 3514
% 12.66/5.63  #SimpNegUnit  : 182
% 12.66/5.63  #BackRed      : 22
% 12.66/5.63  
% 12.66/5.63  #Partial instantiations: 0
% 12.66/5.63  #Strategies tried      : 1
% 12.66/5.63  
% 12.66/5.63  Timing (in seconds)
% 12.66/5.63  ----------------------
% 12.66/5.63  Preprocessing        : 0.32
% 12.66/5.63  Parsing              : 0.18
% 12.66/5.63  CNF conversion       : 0.02
% 12.66/5.63  Main loop            : 4.52
% 12.66/5.63  Inferencing          : 0.81
% 12.66/5.63  Reduction            : 2.30
% 12.66/5.63  Demodulation         : 1.93
% 12.66/5.63  BG Simplification    : 0.10
% 12.66/5.63  Subsumption          : 1.03
% 12.66/5.63  Abstraction          : 0.15
% 12.66/5.63  MUC search           : 0.00
% 12.66/5.63  Cooper               : 0.00
% 12.66/5.63  Total                : 4.88
% 12.66/5.63  Index Insertion      : 0.00
% 12.66/5.63  Index Deletion       : 0.00
% 12.66/5.63  Index Matching       : 0.00
% 12.66/5.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
