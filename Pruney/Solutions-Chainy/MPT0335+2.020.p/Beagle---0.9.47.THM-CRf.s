%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:56 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.42s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 101 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 124 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(c_36,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_80])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_522,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_528,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,k3_xboole_0(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_22])).

tff(c_569,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_528])).

tff(c_42,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_168,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_192,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_168])).

tff(c_1014,plain,(
    ! [A_77,B_78,C_79] : k4_xboole_0(k3_xboole_0(A_77,B_78),C_79) = k3_xboole_0(A_77,k4_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1097,plain,(
    ! [C_79] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_79)) = k4_xboole_0('#skF_1',C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_1014])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_564,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_522])).

tff(c_1734,plain,(
    ! [C_91] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_91)) = k4_xboole_0('#skF_1',C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_1014])).

tff(c_1780,plain,(
    ! [A_1] : k4_xboole_0('#skF_1',k3_xboole_0(A_1,'#skF_2')) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_1734])).

tff(c_4683,plain,(
    ! [A_129] : k4_xboole_0('#skF_1',k3_xboole_0(A_129,'#skF_2')) = k4_xboole_0('#skF_1',A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_1780])).

tff(c_4714,plain,(
    ! [A_129] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',A_129)) = k3_xboole_0('#skF_1',k3_xboole_0(A_129,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4683,c_22])).

tff(c_4773,plain,(
    ! [A_129] : k3_xboole_0('#skF_1',k3_xboole_0(A_129,'#skF_2')) = k3_xboole_0('#skF_1',A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4714])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [B_40,A_41] : r1_tarski(k3_xboole_0(B_40,A_41),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12])).

tff(c_3782,plain,(
    ! [B_115,A_116] : k3_xboole_0(k3_xboole_0(B_115,A_116),A_116) = k3_xboole_0(B_115,A_116) ),
    inference(resolution,[status(thm)],[c_95,c_168])).

tff(c_5018,plain,(
    ! [B_132,A_133] : k3_xboole_0(k3_xboole_0(B_132,A_133),B_132) = k3_xboole_0(A_133,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3782])).

tff(c_16602,plain,(
    ! [B_242,A_243] : k3_xboole_0(B_242,k3_xboole_0(B_242,A_243)) = k3_xboole_0(A_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_5018,c_2])).

tff(c_16835,plain,(
    ! [A_129] : k3_xboole_0(k3_xboole_0(A_129,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',A_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4773,c_16602])).

tff(c_23260,plain,(
    ! [A_289] : k3_xboole_0(k3_xboole_0(A_289,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',A_289) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_16835])).

tff(c_23482,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_23260])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2140,plain,(
    ! [A_97,C_98,B_99] :
      ( k3_xboole_0(k2_tarski(A_97,C_98),B_99) = k2_tarski(A_97,C_98)
      | ~ r2_hidden(C_98,B_99)
      | ~ r2_hidden(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2211,plain,(
    ! [A_21,B_99] :
      ( k3_xboole_0(k1_tarski(A_21),B_99) = k2_tarski(A_21,A_21)
      | ~ r2_hidden(A_21,B_99)
      | ~ r2_hidden(A_21,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2140])).

tff(c_7790,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(k1_tarski(A_155),B_156) = k1_tarski(A_155)
      | ~ r2_hidden(A_155,B_156)
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2211])).

tff(c_408,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_430,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,k3_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_12,c_408])).

tff(c_7858,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(k1_tarski(A_155),B_156) = k1_tarski(A_155)
      | ~ r1_tarski(k1_tarski(A_155),k1_tarski(A_155))
      | ~ r2_hidden(A_155,B_156)
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7790,c_430])).

tff(c_8006,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(k1_tarski(A_155),B_156) = k1_tarski(A_155)
      | ~ r2_hidden(A_155,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7858])).

tff(c_23565,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23482,c_8006])).

tff(c_23708,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_23565])).

tff(c_23710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_23708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/3.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.95  
% 10.38/3.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.95  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.38/3.95  
% 10.38/3.95  %Foreground sorts:
% 10.38/3.95  
% 10.38/3.95  
% 10.38/3.95  %Background operators:
% 10.38/3.95  
% 10.38/3.95  
% 10.38/3.95  %Foreground operators:
% 10.38/3.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/3.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.38/3.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.38/3.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.38/3.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/3.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.38/3.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.38/3.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.38/3.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.38/3.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.38/3.95  tff('#skF_2', type, '#skF_2': $i).
% 10.38/3.95  tff('#skF_3', type, '#skF_3': $i).
% 10.38/3.95  tff('#skF_1', type, '#skF_1': $i).
% 10.38/3.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/3.95  tff('#skF_4', type, '#skF_4': $i).
% 10.38/3.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/3.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.38/3.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.38/3.95  
% 10.42/3.96  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 10.42/3.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.42/3.96  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.42/3.96  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.42/3.96  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.42/3.96  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.42/3.96  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.42/3.96  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.42/3.96  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.42/3.96  tff(f_67, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 10.42/3.96  tff(c_36, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.42/3.96  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.42/3.96  tff(c_40, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.42/3.96  tff(c_80, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.42/3.96  tff(c_122, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_80])).
% 10.42/3.96  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.42/3.96  tff(c_522, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.42/3.96  tff(c_528, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, k3_xboole_0(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_522, c_22])).
% 10.42/3.96  tff(c_569, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_528])).
% 10.42/3.96  tff(c_42, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.42/3.96  tff(c_168, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.42/3.96  tff(c_192, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_42, c_168])).
% 10.42/3.96  tff(c_1014, plain, (![A_77, B_78, C_79]: (k4_xboole_0(k3_xboole_0(A_77, B_78), C_79)=k3_xboole_0(A_77, k4_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.42/3.96  tff(c_1097, plain, (![C_79]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_79))=k4_xboole_0('#skF_1', C_79))), inference(superposition, [status(thm), theory('equality')], [c_192, c_1014])).
% 10.42/3.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.42/3.96  tff(c_564, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_522])).
% 10.42/3.96  tff(c_1734, plain, (![C_91]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_91))=k4_xboole_0('#skF_1', C_91))), inference(superposition, [status(thm), theory('equality')], [c_192, c_1014])).
% 10.42/3.96  tff(c_1780, plain, (![A_1]: (k4_xboole_0('#skF_1', k3_xboole_0(A_1, '#skF_2'))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_564, c_1734])).
% 10.42/3.96  tff(c_4683, plain, (![A_129]: (k4_xboole_0('#skF_1', k3_xboole_0(A_129, '#skF_2'))=k4_xboole_0('#skF_1', A_129))), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_1780])).
% 10.42/3.96  tff(c_4714, plain, (![A_129]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', A_129))=k3_xboole_0('#skF_1', k3_xboole_0(A_129, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4683, c_22])).
% 10.42/3.96  tff(c_4773, plain, (![A_129]: (k3_xboole_0('#skF_1', k3_xboole_0(A_129, '#skF_2'))=k3_xboole_0('#skF_1', A_129))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4714])).
% 10.42/3.96  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.42/3.96  tff(c_95, plain, (![B_40, A_41]: (r1_tarski(k3_xboole_0(B_40, A_41), A_41))), inference(superposition, [status(thm), theory('equality')], [c_80, c_12])).
% 10.42/3.96  tff(c_3782, plain, (![B_115, A_116]: (k3_xboole_0(k3_xboole_0(B_115, A_116), A_116)=k3_xboole_0(B_115, A_116))), inference(resolution, [status(thm)], [c_95, c_168])).
% 10.42/3.96  tff(c_5018, plain, (![B_132, A_133]: (k3_xboole_0(k3_xboole_0(B_132, A_133), B_132)=k3_xboole_0(A_133, B_132))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3782])).
% 10.42/3.96  tff(c_16602, plain, (![B_242, A_243]: (k3_xboole_0(B_242, k3_xboole_0(B_242, A_243))=k3_xboole_0(A_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_5018, c_2])).
% 10.42/3.96  tff(c_16835, plain, (![A_129]: (k3_xboole_0(k3_xboole_0(A_129, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', A_129)))), inference(superposition, [status(thm), theory('equality')], [c_4773, c_16602])).
% 10.42/3.96  tff(c_23260, plain, (![A_289]: (k3_xboole_0(k3_xboole_0(A_289, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', A_289))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_16835])).
% 10.42/3.96  tff(c_23482, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_122, c_23260])).
% 10.42/3.96  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.42/3.96  tff(c_26, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.42/3.96  tff(c_2140, plain, (![A_97, C_98, B_99]: (k3_xboole_0(k2_tarski(A_97, C_98), B_99)=k2_tarski(A_97, C_98) | ~r2_hidden(C_98, B_99) | ~r2_hidden(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.42/3.96  tff(c_2211, plain, (![A_21, B_99]: (k3_xboole_0(k1_tarski(A_21), B_99)=k2_tarski(A_21, A_21) | ~r2_hidden(A_21, B_99) | ~r2_hidden(A_21, B_99))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2140])).
% 10.42/3.96  tff(c_7790, plain, (![A_155, B_156]: (k3_xboole_0(k1_tarski(A_155), B_156)=k1_tarski(A_155) | ~r2_hidden(A_155, B_156) | ~r2_hidden(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2211])).
% 10.42/3.96  tff(c_408, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.42/3.96  tff(c_430, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, k3_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_12, c_408])).
% 10.42/3.96  tff(c_7858, plain, (![A_155, B_156]: (k3_xboole_0(k1_tarski(A_155), B_156)=k1_tarski(A_155) | ~r1_tarski(k1_tarski(A_155), k1_tarski(A_155)) | ~r2_hidden(A_155, B_156) | ~r2_hidden(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_7790, c_430])).
% 10.42/3.96  tff(c_8006, plain, (![A_155, B_156]: (k3_xboole_0(k1_tarski(A_155), B_156)=k1_tarski(A_155) | ~r2_hidden(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7858])).
% 10.42/3.96  tff(c_23565, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23482, c_8006])).
% 10.42/3.96  tff(c_23708, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_23565])).
% 10.42/3.96  tff(c_23710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_23708])).
% 10.42/3.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.42/3.96  
% 10.42/3.96  Inference rules
% 10.42/3.96  ----------------------
% 10.42/3.96  #Ref     : 0
% 10.42/3.96  #Sup     : 5738
% 10.42/3.96  #Fact    : 0
% 10.42/3.96  #Define  : 0
% 10.42/3.96  #Split   : 5
% 10.42/3.96  #Chain   : 0
% 10.42/3.96  #Close   : 0
% 10.42/3.96  
% 10.42/3.96  Ordering : KBO
% 10.42/3.96  
% 10.42/3.96  Simplification rules
% 10.42/3.96  ----------------------
% 10.42/3.96  #Subsume      : 226
% 10.42/3.96  #Demod        : 7021
% 10.42/3.96  #Tautology    : 3894
% 10.42/3.96  #SimpNegUnit  : 4
% 10.42/3.96  #BackRed      : 7
% 10.42/3.96  
% 10.42/3.96  #Partial instantiations: 0
% 10.42/3.96  #Strategies tried      : 1
% 10.42/3.96  
% 10.42/3.96  Timing (in seconds)
% 10.42/3.96  ----------------------
% 10.42/3.96  Preprocessing        : 0.32
% 10.42/3.96  Parsing              : 0.18
% 10.42/3.96  CNF conversion       : 0.02
% 10.42/3.96  Main loop            : 2.85
% 10.42/3.96  Inferencing          : 0.56
% 10.42/3.96  Reduction            : 1.67
% 10.42/3.96  Demodulation         : 1.48
% 10.42/3.96  BG Simplification    : 0.06
% 10.42/3.97  Subsumption          : 0.43
% 10.42/3.97  Abstraction          : 0.10
% 10.42/3.97  MUC search           : 0.00
% 10.42/3.97  Cooper               : 0.00
% 10.42/3.97  Total                : 3.20
% 10.42/3.97  Index Insertion      : 0.00
% 10.42/3.97  Index Deletion       : 0.00
% 10.42/3.97  Index Matching       : 0.00
% 10.42/3.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
