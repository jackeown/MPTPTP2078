%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:58 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 130 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 154 expanded)
%              Number of equality atoms :   51 (  87 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1136,plain,(
    ! [A_133,B_134] :
      ( k3_xboole_0(A_133,B_134) = A_133
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1142,plain,(
    ! [A_137] : k3_xboole_0(k1_xboole_0,A_137) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1136])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1147,plain,(
    ! [A_137] : k3_xboole_0(A_137,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_2])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1319,plain,(
    ! [A_157,B_158] : k5_xboole_0(A_157,k3_xboole_0(A_157,B_158)) = k4_xboole_0(A_157,B_158) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1328,plain,(
    ! [A_137] : k5_xboole_0(A_137,k1_xboole_0) = k4_xboole_0(A_137,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_1319])).

tff(c_1345,plain,(
    ! [A_159] : k4_xboole_0(A_159,k1_xboole_0) = A_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1328])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1351,plain,(
    ! [A_159] : k4_xboole_0(A_159,A_159) = k3_xboole_0(A_159,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1345,c_16])).

tff(c_1364,plain,(
    ! [A_159] : k4_xboole_0(A_159,A_159) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1351])).

tff(c_42,plain,(
    ! [B_43] : k4_xboole_0(k1_tarski(B_43),k1_tarski(B_43)) != k1_tarski(B_43) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1387,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_42])).

tff(c_142,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_163,plain,(
    ! [A_66] : k3_xboole_0(A_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_2])).

tff(c_770,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = k4_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_779,plain,(
    ! [A_66] : k5_xboole_0(A_66,k1_xboole_0) = k4_xboole_0(A_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_770])).

tff(c_815,plain,(
    ! [A_115] : k4_xboole_0(A_115,k1_xboole_0) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_779])).

tff(c_821,plain,(
    ! [A_115] : k4_xboole_0(A_115,A_115) = k3_xboole_0(A_115,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_16])).

tff(c_834,plain,(
    ! [A_115] : k4_xboole_0(A_115,A_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_821])).

tff(c_838,plain,(
    ! [B_43] : k1_tarski(B_43) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_42])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_118,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(k1_tarski(A_55),B_56)
      | r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_621,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(k1_tarski(A_103),B_104) = k1_tarski(A_103)
      | r2_hidden(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_118,c_20])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_232,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_655,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_232])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_655])).

tff(c_689,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_38,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1027,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(k1_tarski(A_129),B_130) = k1_xboole_0
      | ~ r2_hidden(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_691,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_690,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_690])).

tff(c_696,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1061,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_696])).

tff(c_1097,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_1061])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_1097])).

tff(c_1100,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1245,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k1_xboole_0
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1538,plain,(
    ! [A_173,B_174] :
      ( k4_xboole_0(k1_tarski(A_173),B_174) = k1_xboole_0
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_38,c_1245])).

tff(c_1101,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1218,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_52])).

tff(c_1566,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_1218])).

tff(c_1600,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1566])).

tff(c_1602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1387,c_1600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.50  
% 2.98/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.98/1.50  
% 2.98/1.50  %Foreground sorts:
% 2.98/1.50  
% 2.98/1.50  
% 2.98/1.50  %Background operators:
% 2.98/1.50  
% 2.98/1.50  
% 2.98/1.50  %Foreground operators:
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.98/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.50  
% 2.98/1.52  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.98/1.52  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.98/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.98/1.52  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.98/1.52  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.98/1.52  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.98/1.52  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.98/1.52  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.98/1.52  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.98/1.52  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.98/1.52  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.98/1.52  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.98/1.52  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.52  tff(c_1136, plain, (![A_133, B_134]: (k3_xboole_0(A_133, B_134)=A_133 | ~r1_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.52  tff(c_1142, plain, (![A_137]: (k3_xboole_0(k1_xboole_0, A_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1136])).
% 2.98/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.52  tff(c_1147, plain, (![A_137]: (k3_xboole_0(A_137, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1142, c_2])).
% 2.98/1.52  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.52  tff(c_1319, plain, (![A_157, B_158]: (k5_xboole_0(A_157, k3_xboole_0(A_157, B_158))=k4_xboole_0(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.52  tff(c_1328, plain, (![A_137]: (k5_xboole_0(A_137, k1_xboole_0)=k4_xboole_0(A_137, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1147, c_1319])).
% 2.98/1.52  tff(c_1345, plain, (![A_159]: (k4_xboole_0(A_159, k1_xboole_0)=A_159)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1328])).
% 2.98/1.52  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.98/1.52  tff(c_1351, plain, (![A_159]: (k4_xboole_0(A_159, A_159)=k3_xboole_0(A_159, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1345, c_16])).
% 2.98/1.52  tff(c_1364, plain, (![A_159]: (k4_xboole_0(A_159, A_159)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1351])).
% 2.98/1.52  tff(c_42, plain, (![B_43]: (k4_xboole_0(k1_tarski(B_43), k1_tarski(B_43))!=k1_tarski(B_43))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.98/1.52  tff(c_1387, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_42])).
% 2.98/1.52  tff(c_142, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.52  tff(c_158, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_142])).
% 2.98/1.52  tff(c_163, plain, (![A_66]: (k3_xboole_0(A_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_158, c_2])).
% 2.98/1.52  tff(c_770, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k3_xboole_0(A_111, B_112))=k4_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.52  tff(c_779, plain, (![A_66]: (k5_xboole_0(A_66, k1_xboole_0)=k4_xboole_0(A_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_163, c_770])).
% 2.98/1.52  tff(c_815, plain, (![A_115]: (k4_xboole_0(A_115, k1_xboole_0)=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_779])).
% 2.98/1.52  tff(c_821, plain, (![A_115]: (k4_xboole_0(A_115, A_115)=k3_xboole_0(A_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_815, c_16])).
% 2.98/1.52  tff(c_834, plain, (![A_115]: (k4_xboole_0(A_115, A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_821])).
% 2.98/1.52  tff(c_838, plain, (![B_43]: (k1_tarski(B_43)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_834, c_42])).
% 2.98/1.52  tff(c_48, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.52  tff(c_81, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 2.98/1.52  tff(c_118, plain, (![A_55, B_56]: (r1_xboole_0(k1_tarski(A_55), B_56) | r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.98/1.52  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.52  tff(c_621, plain, (![A_103, B_104]: (k4_xboole_0(k1_tarski(A_103), B_104)=k1_tarski(A_103) | r2_hidden(A_103, B_104))), inference(resolution, [status(thm)], [c_118, c_20])).
% 2.98/1.52  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.52  tff(c_232, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 2.98/1.52  tff(c_655, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_621, c_232])).
% 2.98/1.52  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_655])).
% 2.98/1.52  tff(c_689, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 2.98/1.52  tff(c_38, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.98/1.52  tff(c_133, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.52  tff(c_1027, plain, (![A_129, B_130]: (k4_xboole_0(k1_tarski(A_129), B_130)=k1_xboole_0 | ~r2_hidden(A_129, B_130))), inference(resolution, [status(thm)], [c_38, c_133])).
% 2.98/1.52  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.52  tff(c_691, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 2.98/1.52  tff(c_690, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 2.98/1.52  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_691, c_690])).
% 2.98/1.52  tff(c_696, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.98/1.52  tff(c_1061, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1027, c_696])).
% 2.98/1.52  tff(c_1097, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_689, c_1061])).
% 2.98/1.52  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_838, c_1097])).
% 2.98/1.52  tff(c_1100, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.98/1.52  tff(c_1245, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k1_xboole_0 | ~r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.52  tff(c_1538, plain, (![A_173, B_174]: (k4_xboole_0(k1_tarski(A_173), B_174)=k1_xboole_0 | ~r2_hidden(A_173, B_174))), inference(resolution, [status(thm)], [c_38, c_1245])).
% 2.98/1.52  tff(c_1101, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 2.98/1.52  tff(c_52, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.52  tff(c_1218, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_52])).
% 2.98/1.52  tff(c_1566, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1538, c_1218])).
% 2.98/1.52  tff(c_1600, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1566])).
% 2.98/1.52  tff(c_1602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1387, c_1600])).
% 2.98/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.52  
% 2.98/1.52  Inference rules
% 2.98/1.52  ----------------------
% 2.98/1.52  #Ref     : 0
% 2.98/1.52  #Sup     : 357
% 2.98/1.52  #Fact    : 0
% 2.98/1.52  #Define  : 0
% 2.98/1.52  #Split   : 4
% 2.98/1.52  #Chain   : 0
% 2.98/1.52  #Close   : 0
% 2.98/1.52  
% 2.98/1.52  Ordering : KBO
% 2.98/1.52  
% 2.98/1.52  Simplification rules
% 2.98/1.52  ----------------------
% 2.98/1.52  #Subsume      : 28
% 2.98/1.52  #Demod        : 137
% 2.98/1.52  #Tautology    : 247
% 2.98/1.52  #SimpNegUnit  : 23
% 2.98/1.52  #BackRed      : 3
% 2.98/1.52  
% 2.98/1.52  #Partial instantiations: 0
% 2.98/1.52  #Strategies tried      : 1
% 2.98/1.52  
% 2.98/1.52  Timing (in seconds)
% 2.98/1.52  ----------------------
% 2.98/1.52  Preprocessing        : 0.31
% 2.98/1.52  Parsing              : 0.16
% 2.98/1.52  CNF conversion       : 0.02
% 2.98/1.52  Main loop            : 0.39
% 2.98/1.52  Inferencing          : 0.15
% 2.98/1.52  Reduction            : 0.13
% 2.98/1.52  Demodulation         : 0.09
% 2.98/1.52  BG Simplification    : 0.02
% 2.98/1.52  Subsumption          : 0.06
% 2.98/1.52  Abstraction          : 0.02
% 2.98/1.52  MUC search           : 0.00
% 2.98/1.52  Cooper               : 0.00
% 2.98/1.52  Total                : 0.73
% 2.98/1.52  Index Insertion      : 0.00
% 2.98/1.52  Index Deletion       : 0.00
% 2.98/1.52  Index Matching       : 0.00
% 2.98/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
