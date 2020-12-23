%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:59 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   54 (  94 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 160 expanded)
%              Number of equality atoms :   64 ( 157 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_mcart_1 > k4_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_41,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
       => ( A = D
          & B = E
          & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_8,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_3') = k3_mcart_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] : k4_tarski(k4_tarski(A_16,B_17),C_18) = k3_mcart_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [D_7,B_5,C_6,A_4] :
      ( D_7 = B_5
      | k4_tarski(C_6,D_7) != k4_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_21,C_22,A_23,B_20,B_19] :
      ( C_22 = B_19
      | k4_tarski(A_23,B_19) != k3_mcart_1(A_21,B_20,C_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_60,plain,(
    ! [B_24,A_25] :
      ( B_24 = '#skF_3'
      | k4_tarski(A_25,B_24) != k3_mcart_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_63,plain,(
    ! [C_3,A_1,B_2] :
      ( C_3 = '#skF_3'
      | k3_mcart_1(A_1,B_2,C_3) != k3_mcart_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_66,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_63])).

tff(c_75,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_3') = k3_mcart_1('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_6,plain,(
    ! [C_6,A_4,D_7,B_5] :
      ( C_6 = A_4
      | k4_tarski(C_6,D_7) != k4_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [B_36,A_37,B_35,A_39,C_38] :
      ( k4_tarski(A_37,B_36) = A_39
      | k4_tarski(A_39,B_35) != k3_mcart_1(A_37,B_36,C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_105,plain,(
    ! [A_40,B_41] :
      ( k4_tarski('#skF_1','#skF_2') = A_40
      | k4_tarski(A_40,B_41) != k3_mcart_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_98])).

tff(c_108,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski(A_1,B_2) = k4_tarski('#skF_1','#skF_2')
      | k3_mcart_1(A_1,B_2,C_3) != k3_mcart_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_138,plain,(
    k4_tarski('#skF_1','#skF_2') = k4_tarski('#skF_4','#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_108])).

tff(c_160,plain,(
    ! [A_4,B_5] :
      ( A_4 = '#skF_1'
      | k4_tarski(A_4,B_5) != k4_tarski('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_6])).

tff(c_200,plain,(
    '#skF_1' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_160])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11,c_200])).

tff(c_203,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_209,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_204,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_215,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_6') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_10])).

tff(c_225,plain,(
    ! [A_58,B_59,C_60] : k4_tarski(k4_tarski(A_58,B_59),C_60) = k3_mcart_1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_252,plain,(
    ! [B_63,A_65,B_61,C_64,A_62] :
      ( C_64 = B_63
      | k4_tarski(A_65,B_63) != k3_mcart_1(A_62,B_61,C_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_4])).

tff(c_259,plain,(
    ! [B_66,A_67] :
      ( B_66 = '#skF_6'
      | k4_tarski(A_67,B_66) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_252])).

tff(c_262,plain,(
    ! [C_3,A_1,B_2] :
      ( C_3 = '#skF_6'
      | k3_mcart_1(A_1,B_2,C_3) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_276,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_262])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_276])).

tff(c_279,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_280,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_285,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_3') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_204,c_10])).

tff(c_300,plain,(
    ! [A_82,B_83,C_84] : k4_tarski(k4_tarski(A_82,B_83),C_84) = k3_mcart_1(A_82,B_83,C_84) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_345,plain,(
    ! [C_96,B_99,C_97,A_100,D_98] :
      ( k4_tarski(A_100,B_99) = C_96
      | k4_tarski(C_96,D_98) != k3_mcart_1(A_100,B_99,C_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_6])).

tff(c_352,plain,(
    ! [C_101,D_102] :
      ( k4_tarski('#skF_4','#skF_5') = C_101
      | k4_tarski(C_101,D_102) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_345])).

tff(c_355,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski(A_1,B_2) = k4_tarski('#skF_4','#skF_5')
      | k3_mcart_1(A_1,B_2,C_3) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_352])).

tff(c_385,plain,(
    k4_tarski('#skF_4','#skF_5') = k4_tarski('#skF_4','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_355])).

tff(c_407,plain,(
    ! [B_5,A_4] :
      ( B_5 = '#skF_5'
      | k4_tarski(A_4,B_5) != k4_tarski('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_4])).

tff(c_447,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_407])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_447])).

%------------------------------------------------------------------------------
