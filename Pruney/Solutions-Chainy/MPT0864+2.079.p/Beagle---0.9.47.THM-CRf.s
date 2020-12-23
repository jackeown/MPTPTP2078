%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:19 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 117 expanded)
%              Number of leaves         :   38 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 129 expanded)
%              Number of equality atoms :   54 ( 103 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_556,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k3_xboole_0(A_129,B_130)) = k4_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_571,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_556])).

tff(c_575,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_571])).

tff(c_584,plain,(
    ! [A_132,B_133] : k3_xboole_0(k1_tarski(A_132),k2_tarski(A_132,B_133)) = k1_tarski(A_132) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_590,plain,(
    ! [A_132,B_133] : k5_xboole_0(k1_tarski(A_132),k1_tarski(A_132)) = k4_xboole_0(k1_tarski(A_132),k2_tarski(A_132,B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_2])).

tff(c_600,plain,(
    ! [A_134,B_135] : k4_xboole_0(k1_tarski(A_134),k2_tarski(A_134,B_135)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_590])).

tff(c_607,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_600])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_610,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_34])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_482,plain,(
    ! [A_120,B_121] :
      ( ~ r1_tarski(A_120,k2_zfmisc_1(B_121,A_120))
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_487,plain,(
    ! [A_35,B_121] :
      ( k1_tarski(A_35) = k1_xboole_0
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_121,k1_tarski(A_35))) ) ),
    inference(resolution,[status(thm)],[c_24,c_482])).

tff(c_710,plain,(
    ! [A_35,B_121] : ~ r2_hidden(A_35,k2_zfmisc_1(B_121,k1_tarski(A_35))) ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_487])).

tff(c_254,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_269,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_254])).

tff(c_273,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_269])).

tff(c_274,plain,(
    ! [A_85,B_86] : k3_xboole_0(k1_tarski(A_85),k2_tarski(A_85,B_86)) = k1_tarski(A_85) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_297,plain,(
    ! [A_88] : k3_xboole_0(k1_tarski(A_88),k1_tarski(A_88)) = k1_tarski(A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_274])).

tff(c_303,plain,(
    ! [A_88] : k5_xboole_0(k1_tarski(A_88),k1_tarski(A_88)) = k4_xboole_0(k1_tarski(A_88),k1_tarski(A_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_2])).

tff(c_314,plain,(
    ! [A_88] : k4_xboole_0(k1_tarski(A_88),k1_tarski(A_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_303])).

tff(c_320,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_34])).

tff(c_170,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_tarski(A_72),B_73)
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( ~ r1_tarski(A_39,k2_zfmisc_1(A_39,B_40))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_179,plain,(
    ! [A_72,B_40] :
      ( k1_tarski(A_72) = k1_xboole_0
      | ~ r2_hidden(A_72,k2_zfmisc_1(k1_tarski(A_72),B_40)) ) ),
    inference(resolution,[status(thm)],[c_170,c_30])).

tff(c_397,plain,(
    ! [A_72,B_40] : ~ r2_hidden(A_72,k2_zfmisc_1(k1_tarski(A_72),B_40)) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_179])).

tff(c_52,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_57,plain,(
    ! [A_55,B_56] : k1_mcart_1(k4_tarski(A_55,B_56)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_57])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_50])).

tff(c_95,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_97,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_52])).

tff(c_316,plain,(
    ! [C_89,D_90] : r2_hidden(k4_tarski(C_89,D_90),k2_zfmisc_1(k1_tarski(C_89),k1_tarski(D_90))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_319,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_316])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_319])).

tff(c_400,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_82,plain,(
    ! [A_58,B_59] : k2_mcart_1(k4_tarski(A_58,B_59)) = B_59 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_91,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_406,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_91])).

tff(c_407,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_52])).

tff(c_618,plain,(
    ! [C_137,D_138] : r2_hidden(k4_tarski(C_137,D_138),k2_zfmisc_1(k1_tarski(C_137),k1_tarski(D_138))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_621,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_618])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.36  
% 2.35/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.36  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.36  
% 2.35/1.36  %Foreground sorts:
% 2.35/1.36  
% 2.35/1.36  
% 2.35/1.36  %Background operators:
% 2.35/1.36  
% 2.35/1.36  
% 2.35/1.36  %Foreground operators:
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.35/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.35/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.35/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.35/1.36  
% 2.35/1.38  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.35/1.38  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.35/1.38  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.35/1.38  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.35/1.38  tff(f_59, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.35/1.38  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.35/1.38  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.35/1.38  tff(f_57, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.35/1.38  tff(f_86, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.35/1.38  tff(f_76, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.35/1.38  tff(f_70, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.35/1.38  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.38  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.38  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.38  tff(c_556, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k3_xboole_0(A_129, B_130))=k4_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.38  tff(c_571, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_556])).
% 2.35/1.38  tff(c_575, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_571])).
% 2.35/1.38  tff(c_584, plain, (![A_132, B_133]: (k3_xboole_0(k1_tarski(A_132), k2_tarski(A_132, B_133))=k1_tarski(A_132))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.35/1.38  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.38  tff(c_590, plain, (![A_132, B_133]: (k5_xboole_0(k1_tarski(A_132), k1_tarski(A_132))=k4_xboole_0(k1_tarski(A_132), k2_tarski(A_132, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_584, c_2])).
% 2.35/1.38  tff(c_600, plain, (![A_134, B_135]: (k4_xboole_0(k1_tarski(A_134), k2_tarski(A_134, B_135))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_575, c_590])).
% 2.35/1.38  tff(c_607, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_600])).
% 2.35/1.38  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.35/1.38  tff(c_610, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_34])).
% 2.35/1.38  tff(c_24, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.38  tff(c_482, plain, (![A_120, B_121]: (~r1_tarski(A_120, k2_zfmisc_1(B_121, A_120)) | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.38  tff(c_487, plain, (![A_35, B_121]: (k1_tarski(A_35)=k1_xboole_0 | ~r2_hidden(A_35, k2_zfmisc_1(B_121, k1_tarski(A_35))))), inference(resolution, [status(thm)], [c_24, c_482])).
% 2.35/1.38  tff(c_710, plain, (![A_35, B_121]: (~r2_hidden(A_35, k2_zfmisc_1(B_121, k1_tarski(A_35))))), inference(negUnitSimplification, [status(thm)], [c_610, c_487])).
% 2.35/1.38  tff(c_254, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.38  tff(c_269, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_254])).
% 2.35/1.38  tff(c_273, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_269])).
% 2.35/1.38  tff(c_274, plain, (![A_85, B_86]: (k3_xboole_0(k1_tarski(A_85), k2_tarski(A_85, B_86))=k1_tarski(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.35/1.38  tff(c_297, plain, (![A_88]: (k3_xboole_0(k1_tarski(A_88), k1_tarski(A_88))=k1_tarski(A_88))), inference(superposition, [status(thm), theory('equality')], [c_8, c_274])).
% 2.35/1.38  tff(c_303, plain, (![A_88]: (k5_xboole_0(k1_tarski(A_88), k1_tarski(A_88))=k4_xboole_0(k1_tarski(A_88), k1_tarski(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_297, c_2])).
% 2.35/1.38  tff(c_314, plain, (![A_88]: (k4_xboole_0(k1_tarski(A_88), k1_tarski(A_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_303])).
% 2.35/1.38  tff(c_320, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_314, c_34])).
% 2.35/1.38  tff(c_170, plain, (![A_72, B_73]: (r1_tarski(k1_tarski(A_72), B_73) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.38  tff(c_30, plain, (![A_39, B_40]: (~r1_tarski(A_39, k2_zfmisc_1(A_39, B_40)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.38  tff(c_179, plain, (![A_72, B_40]: (k1_tarski(A_72)=k1_xboole_0 | ~r2_hidden(A_72, k2_zfmisc_1(k1_tarski(A_72), B_40)))), inference(resolution, [status(thm)], [c_170, c_30])).
% 2.35/1.38  tff(c_397, plain, (![A_72, B_40]: (~r2_hidden(A_72, k2_zfmisc_1(k1_tarski(A_72), B_40)))), inference(negUnitSimplification, [status(thm)], [c_320, c_179])).
% 2.35/1.38  tff(c_52, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.35/1.38  tff(c_57, plain, (![A_55, B_56]: (k1_mcart_1(k4_tarski(A_55, B_56))=A_55)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.38  tff(c_66, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_52, c_57])).
% 2.35/1.38  tff(c_50, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.35/1.38  tff(c_94, plain, (k2_mcart_1('#skF_1')='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_50])).
% 2.35/1.38  tff(c_95, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_94])).
% 2.35/1.38  tff(c_97, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_52])).
% 2.35/1.38  tff(c_316, plain, (![C_89, D_90]: (r2_hidden(k4_tarski(C_89, D_90), k2_zfmisc_1(k1_tarski(C_89), k1_tarski(D_90))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.38  tff(c_319, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_97, c_316])).
% 2.35/1.38  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_319])).
% 2.35/1.38  tff(c_400, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_94])).
% 2.35/1.38  tff(c_82, plain, (![A_58, B_59]: (k2_mcart_1(k4_tarski(A_58, B_59))=B_59)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.38  tff(c_91, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_52, c_82])).
% 2.35/1.38  tff(c_406, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_400, c_91])).
% 2.35/1.38  tff(c_407, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_52])).
% 2.35/1.38  tff(c_618, plain, (![C_137, D_138]: (r2_hidden(k4_tarski(C_137, D_138), k2_zfmisc_1(k1_tarski(C_137), k1_tarski(D_138))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.38  tff(c_621, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_407, c_618])).
% 2.35/1.38  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_710, c_621])).
% 2.35/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.38  
% 2.35/1.38  Inference rules
% 2.35/1.38  ----------------------
% 2.35/1.38  #Ref     : 0
% 2.35/1.38  #Sup     : 161
% 2.35/1.38  #Fact    : 0
% 2.35/1.38  #Define  : 0
% 2.35/1.38  #Split   : 1
% 2.35/1.38  #Chain   : 0
% 2.35/1.38  #Close   : 0
% 2.35/1.38  
% 2.35/1.38  Ordering : KBO
% 2.35/1.38  
% 2.35/1.38  Simplification rules
% 2.35/1.38  ----------------------
% 2.35/1.38  #Subsume      : 0
% 2.35/1.38  #Demod        : 33
% 2.35/1.38  #Tautology    : 132
% 2.35/1.38  #SimpNegUnit  : 10
% 2.35/1.38  #BackRed      : 7
% 2.35/1.38  
% 2.35/1.38  #Partial instantiations: 0
% 2.35/1.38  #Strategies tried      : 1
% 2.35/1.38  
% 2.35/1.38  Timing (in seconds)
% 2.35/1.38  ----------------------
% 2.35/1.38  Preprocessing        : 0.31
% 2.35/1.38  Parsing              : 0.16
% 2.35/1.38  CNF conversion       : 0.02
% 2.35/1.38  Main loop            : 0.26
% 2.35/1.38  Inferencing          : 0.10
% 2.35/1.38  Reduction            : 0.08
% 2.35/1.38  Demodulation         : 0.06
% 2.35/1.38  BG Simplification    : 0.02
% 2.35/1.38  Subsumption          : 0.03
% 2.35/1.38  Abstraction          : 0.02
% 2.35/1.38  MUC search           : 0.00
% 2.35/1.38  Cooper               : 0.00
% 2.35/1.38  Total                : 0.60
% 2.35/1.38  Index Insertion      : 0.00
% 2.35/1.38  Index Deletion       : 0.00
% 2.35/1.38  Index Matching       : 0.00
% 2.35/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
