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
% DateTime   : Thu Dec  3 09:50:11 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 130 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 239 expanded)
%              Number of equality atoms :   68 ( 224 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_48,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_87,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_103,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_103])).

tff(c_479,plain,(
    ! [B_84,A_85] :
      ( k1_tarski(B_84) = A_85
      | k1_xboole_0 = A_85
      | ~ r1_tarski(A_85,k1_tarski(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_486,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_106,c_479])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_87,c_486])).

tff(c_498,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_499,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_501,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_2') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_14])).

tff(c_551,plain,(
    ! [B_92,A_93] : k5_xboole_0(B_92,A_93) = k5_xboole_0(A_93,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_567,plain,(
    ! [A_93] : k5_xboole_0('#skF_2',A_93) = A_93 ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_501])).

tff(c_648,plain,(
    ! [B_95,A_96] : k3_xboole_0(B_95,A_96) = k3_xboole_0(A_96,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_500,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_499,c_12])).

tff(c_664,plain,(
    ! [A_96] : k3_xboole_0('#skF_2',A_96) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_500])).

tff(c_991,plain,(
    ! [A_124,B_125] : k5_xboole_0(k5_xboole_0(A_124,B_125),k3_xboole_0(A_124,B_125)) = k2_xboole_0(A_124,B_125) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1018,plain,(
    ! [A_96] : k5_xboole_0(k5_xboole_0('#skF_2',A_96),'#skF_2') = k2_xboole_0('#skF_2',A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_991])).

tff(c_1053,plain,(
    ! [A_96] : k2_xboole_0('#skF_2',A_96) = A_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_567,c_1018])).

tff(c_1085,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_52])).

tff(c_1087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_1085])).

tff(c_1088,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1089,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1255,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1089,c_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1472,plain,(
    ! [A_153,B_154] : k5_xboole_0(A_153,k3_xboole_0(A_153,B_154)) = k4_xboole_0(A_153,B_154) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1492,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1472])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1743,plain,(
    ! [A_169,B_170,C_171] : k5_xboole_0(k5_xboole_0(A_169,B_170),C_171) = k5_xboole_0(A_169,k5_xboole_0(B_170,C_171)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1790,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k5_xboole_0(B_18,k3_xboole_0(A_17,B_18))) = k2_xboole_0(A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1743])).

tff(c_1842,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_1790])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2818,plain,(
    ! [B_218,A_219,C_220] : k5_xboole_0(k5_xboole_0(B_218,A_219),C_220) = k5_xboole_0(A_219,k5_xboole_0(B_218,C_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1743])).

tff(c_2873,plain,(
    ! [A_219,B_218] : k5_xboole_0(A_219,k5_xboole_0(B_218,k3_xboole_0(B_218,A_219))) = k2_xboole_0(B_218,A_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_2818,c_22])).

tff(c_3025,plain,(
    ! [B_221,A_222] : k2_xboole_0(B_221,A_222) = k2_xboole_0(A_222,B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1842,c_10,c_2873])).

tff(c_1107,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_52])).

tff(c_3080,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3025,c_1107])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3142,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3080,c_16])).

tff(c_1605,plain,(
    ! [B_162,A_163] :
      ( k1_tarski(B_162) = A_163
      | k1_xboole_0 = A_163
      | ~ r1_tarski(A_163,k1_tarski(B_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1615,plain,(
    ! [A_163] :
      ( k1_tarski('#skF_1') = A_163
      | k1_xboole_0 = A_163
      | ~ r1_tarski(A_163,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_1605])).

tff(c_1622,plain,(
    ! [A_163] :
      ( A_163 = '#skF_2'
      | k1_xboole_0 = A_163
      | ~ r1_tarski(A_163,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1615])).

tff(c_3148,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3142,c_1622])).

tff(c_3155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_1255,c_3148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.71  
% 3.73/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.72  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.73/1.72  
% 3.73/1.72  %Foreground sorts:
% 3.73/1.72  
% 3.73/1.72  
% 3.73/1.72  %Background operators:
% 3.73/1.72  
% 3.73/1.72  
% 3.73/1.72  %Foreground operators:
% 3.73/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.73/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.72  
% 3.73/1.73  tff(f_88, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.73/1.73  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.73/1.73  tff(f_67, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.73/1.73  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.73/1.73  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.73/1.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.73/1.73  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.73/1.73  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.73/1.73  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.73/1.73  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.73/1.73  tff(c_48, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.73  tff(c_98, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 3.73/1.73  tff(c_46, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.73  tff(c_87, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 3.73/1.73  tff(c_52, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.73  tff(c_103, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.73  tff(c_106, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_103])).
% 3.73/1.73  tff(c_479, plain, (![B_84, A_85]: (k1_tarski(B_84)=A_85 | k1_xboole_0=A_85 | ~r1_tarski(A_85, k1_tarski(B_84)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.73/1.73  tff(c_486, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_106, c_479])).
% 3.73/1.73  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_87, c_486])).
% 3.73/1.73  tff(c_498, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 3.73/1.73  tff(c_499, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.73/1.73  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.73/1.73  tff(c_501, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_2')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_499, c_14])).
% 3.73/1.73  tff(c_551, plain, (![B_92, A_93]: (k5_xboole_0(B_92, A_93)=k5_xboole_0(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.73  tff(c_567, plain, (![A_93]: (k5_xboole_0('#skF_2', A_93)=A_93)), inference(superposition, [status(thm), theory('equality')], [c_551, c_501])).
% 3.73/1.73  tff(c_648, plain, (![B_95, A_96]: (k3_xboole_0(B_95, A_96)=k3_xboole_0(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.73  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.73/1.73  tff(c_500, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_499, c_12])).
% 3.73/1.73  tff(c_664, plain, (![A_96]: (k3_xboole_0('#skF_2', A_96)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_648, c_500])).
% 3.73/1.73  tff(c_991, plain, (![A_124, B_125]: (k5_xboole_0(k5_xboole_0(A_124, B_125), k3_xboole_0(A_124, B_125))=k2_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.73  tff(c_1018, plain, (![A_96]: (k5_xboole_0(k5_xboole_0('#skF_2', A_96), '#skF_2')=k2_xboole_0('#skF_2', A_96))), inference(superposition, [status(thm), theory('equality')], [c_664, c_991])).
% 3.73/1.73  tff(c_1053, plain, (![A_96]: (k2_xboole_0('#skF_2', A_96)=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_501, c_567, c_1018])).
% 3.73/1.73  tff(c_1085, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_52])).
% 3.73/1.73  tff(c_1087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_1085])).
% 3.73/1.73  tff(c_1088, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 3.73/1.73  tff(c_1089, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 3.73/1.73  tff(c_50, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.73/1.73  tff(c_1255, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1089, c_50])).
% 3.73/1.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.73  tff(c_1472, plain, (![A_153, B_154]: (k5_xboole_0(A_153, k3_xboole_0(A_153, B_154))=k4_xboole_0(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.73  tff(c_1492, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1472])).
% 3.73/1.73  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.73  tff(c_1743, plain, (![A_169, B_170, C_171]: (k5_xboole_0(k5_xboole_0(A_169, B_170), C_171)=k5_xboole_0(A_169, k5_xboole_0(B_170, C_171)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.73/1.73  tff(c_1790, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k5_xboole_0(B_18, k3_xboole_0(A_17, B_18)))=k2_xboole_0(A_17, B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1743])).
% 3.73/1.73  tff(c_1842, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_1492, c_1790])).
% 3.73/1.73  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.73  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.73  tff(c_2818, plain, (![B_218, A_219, C_220]: (k5_xboole_0(k5_xboole_0(B_218, A_219), C_220)=k5_xboole_0(A_219, k5_xboole_0(B_218, C_220)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1743])).
% 3.73/1.73  tff(c_2873, plain, (![A_219, B_218]: (k5_xboole_0(A_219, k5_xboole_0(B_218, k3_xboole_0(B_218, A_219)))=k2_xboole_0(B_218, A_219))), inference(superposition, [status(thm), theory('equality')], [c_2818, c_22])).
% 3.73/1.73  tff(c_3025, plain, (![B_221, A_222]: (k2_xboole_0(B_221, A_222)=k2_xboole_0(A_222, B_221))), inference(demodulation, [status(thm), theory('equality')], [c_1842, c_10, c_2873])).
% 3.73/1.73  tff(c_1107, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_52])).
% 3.73/1.73  tff(c_3080, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3025, c_1107])).
% 3.73/1.73  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.73  tff(c_3142, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3080, c_16])).
% 3.73/1.73  tff(c_1605, plain, (![B_162, A_163]: (k1_tarski(B_162)=A_163 | k1_xboole_0=A_163 | ~r1_tarski(A_163, k1_tarski(B_162)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.73/1.73  tff(c_1615, plain, (![A_163]: (k1_tarski('#skF_1')=A_163 | k1_xboole_0=A_163 | ~r1_tarski(A_163, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1089, c_1605])).
% 3.73/1.73  tff(c_1622, plain, (![A_163]: (A_163='#skF_2' | k1_xboole_0=A_163 | ~r1_tarski(A_163, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1615])).
% 3.73/1.73  tff(c_3148, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3142, c_1622])).
% 3.73/1.73  tff(c_3155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1088, c_1255, c_3148])).
% 3.73/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.73  
% 3.73/1.73  Inference rules
% 3.73/1.73  ----------------------
% 3.73/1.73  #Ref     : 0
% 3.73/1.73  #Sup     : 750
% 3.73/1.73  #Fact    : 0
% 3.73/1.73  #Define  : 0
% 3.73/1.73  #Split   : 3
% 3.73/1.73  #Chain   : 0
% 3.73/1.73  #Close   : 0
% 3.73/1.73  
% 3.73/1.73  Ordering : KBO
% 3.73/1.73  
% 3.73/1.73  Simplification rules
% 3.73/1.73  ----------------------
% 3.73/1.73  #Subsume      : 8
% 3.73/1.73  #Demod        : 365
% 3.73/1.73  #Tautology    : 542
% 3.73/1.73  #SimpNegUnit  : 10
% 3.73/1.73  #BackRed      : 12
% 3.73/1.73  
% 3.73/1.73  #Partial instantiations: 0
% 3.73/1.73  #Strategies tried      : 1
% 3.73/1.73  
% 3.73/1.73  Timing (in seconds)
% 3.73/1.73  ----------------------
% 3.73/1.73  Preprocessing        : 0.35
% 3.73/1.73  Parsing              : 0.19
% 3.73/1.73  CNF conversion       : 0.02
% 3.73/1.73  Main loop            : 0.57
% 3.73/1.73  Inferencing          : 0.19
% 3.73/1.73  Reduction            : 0.23
% 3.73/1.73  Demodulation         : 0.19
% 3.73/1.73  BG Simplification    : 0.03
% 3.73/1.73  Subsumption          : 0.07
% 3.73/1.73  Abstraction          : 0.03
% 3.73/1.73  MUC search           : 0.00
% 3.73/1.73  Cooper               : 0.00
% 3.73/1.73  Total                : 0.95
% 3.73/1.73  Index Insertion      : 0.00
% 3.73/1.73  Index Deletion       : 0.00
% 3.73/1.73  Index Matching       : 0.00
% 3.73/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
