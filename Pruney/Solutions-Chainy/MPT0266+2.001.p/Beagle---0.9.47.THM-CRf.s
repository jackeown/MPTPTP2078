%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:26 EST 2020

% Result     : Theorem 9.21s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 162 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 157 expanded)
%              Number of equality atoms :   42 ( 130 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_430,plain,(
    ! [A_120,B_121] : k5_xboole_0(k5_xboole_0(A_120,B_121),k2_xboole_0(A_120,B_121)) = k3_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_469,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k3_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_430])).

tff(c_477,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_469])).

tff(c_566,plain,(
    ! [A_124,B_125,C_126] : k5_xboole_0(k5_xboole_0(A_124,B_125),C_126) = k5_xboole_0(A_124,k5_xboole_0(B_125,C_126)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_632,plain,(
    ! [A_15,C_126] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_126)) = k5_xboole_0(k1_xboole_0,C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_566])).

tff(c_645,plain,(
    ! [A_15,C_126] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_126)) = C_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_632])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_649,plain,(
    ! [A_127,C_128] : k5_xboole_0(A_127,k5_xboole_0(A_127,C_128)) = C_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_632])).

tff(c_717,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k5_xboole_0(B_130,A_129)) = B_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_649])).

tff(c_753,plain,(
    ! [A_15,C_126] : k5_xboole_0(k5_xboole_0(A_15,C_126),C_126) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_717])).

tff(c_20,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_199,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_219,plain,(
    ! [B_84,A_85] : k3_tarski(k2_tarski(B_84,A_85)) = k2_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_199])).

tff(c_60,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_228,plain,(
    ! [B_84,A_85] : k2_xboole_0(B_84,A_85) = k2_xboole_0(A_85,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_60])).

tff(c_64,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7066,plain,(
    ! [A_13095,B_13096] : k5_xboole_0(k2_xboole_0(A_13095,B_13096),k5_xboole_0(A_13095,B_13096)) = k3_xboole_0(A_13095,B_13096) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_430])).

tff(c_16163,plain,(
    ! [A_19913,B_19914] : k5_xboole_0(k2_xboole_0(A_19913,B_19914),k3_xboole_0(A_19913,B_19914)) = k5_xboole_0(A_19913,B_19914) ),
    inference(superposition,[status(thm),theory(equality)],[c_7066,c_645])).

tff(c_16286,plain,(
    k5_xboole_0(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),k2_tarski('#skF_4','#skF_5')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_16163])).

tff(c_16316,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) = k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_228,c_2,c_16286])).

tff(c_698,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_649])).

tff(c_747,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_717])).

tff(c_16373,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),k2_tarski('#skF_4','#skF_5')) = k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16316,c_747])).

tff(c_16403,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_16373])).

tff(c_163,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_172,plain,(
    ! [B_75,A_74] : r2_hidden(B_75,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_24])).

tff(c_58,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,k3_tarski(B_55))
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [E_26,A_20,C_22] : r2_hidden(E_26,k1_enumset1(A_20,E_26,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_169,plain,(
    ! [A_74,B_75] : r2_hidden(A_74,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_26])).

tff(c_287,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_324,plain,(
    ! [A_99,B_100,B_101] :
      ( r2_hidden(A_99,B_100)
      | ~ r1_tarski(k2_tarski(A_99,B_101),B_100) ) ),
    inference(resolution,[status(thm)],[c_169,c_287])).

tff(c_396,plain,(
    ! [A_117,B_118,B_119] :
      ( r2_hidden(A_117,k3_tarski(B_118))
      | ~ r2_hidden(k2_tarski(A_117,B_119),B_118) ) ),
    inference(resolution,[status(thm)],[c_58,c_324])).

tff(c_400,plain,(
    ! [A_117,A_74,B_119] : r2_hidden(A_117,k3_tarski(k2_tarski(A_74,k2_tarski(A_117,B_119)))) ),
    inference(resolution,[status(thm)],[c_172,c_396])).

tff(c_424,plain,(
    ! [A_117,A_74,B_119] : r2_hidden(A_117,k2_xboole_0(A_74,k2_tarski(A_117,B_119))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_400])).

tff(c_16439,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16403,c_424])).

tff(c_16455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_16439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.21/3.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.64  
% 9.21/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.64  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 9.21/3.64  
% 9.21/3.64  %Foreground sorts:
% 9.21/3.64  
% 9.21/3.64  
% 9.21/3.64  %Background operators:
% 9.21/3.64  
% 9.21/3.64  
% 9.21/3.64  %Foreground operators:
% 9.21/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.21/3.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.21/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.21/3.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.21/3.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.21/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.21/3.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.21/3.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.21/3.64  tff('#skF_5', type, '#skF_5': $i).
% 9.21/3.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.21/3.64  tff('#skF_6', type, '#skF_6': $i).
% 9.21/3.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.21/3.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.21/3.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.21/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.21/3.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.21/3.64  tff('#skF_4', type, '#skF_4': $i).
% 9.21/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.21/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.21/3.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.21/3.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.21/3.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.21/3.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.21/3.64  
% 9.21/3.65  tff(f_84, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 9.21/3.65  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.21/3.65  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.21/3.65  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.21/3.65  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.21/3.65  tff(f_40, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.21/3.65  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.21/3.65  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.21/3.65  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.21/3.65  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.21/3.65  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.21/3.65  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.21/3.65  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.21/3.65  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.21/3.65  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.21/3.65  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.21/3.65  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.21/3.65  tff(c_430, plain, (![A_120, B_121]: (k5_xboole_0(k5_xboole_0(A_120, B_121), k2_xboole_0(A_120, B_121))=k3_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.21/3.65  tff(c_469, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k3_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_430])).
% 9.21/3.65  tff(c_477, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_469])).
% 9.21/3.65  tff(c_566, plain, (![A_124, B_125, C_126]: (k5_xboole_0(k5_xboole_0(A_124, B_125), C_126)=k5_xboole_0(A_124, k5_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.21/3.65  tff(c_632, plain, (![A_15, C_126]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_126))=k5_xboole_0(k1_xboole_0, C_126))), inference(superposition, [status(thm), theory('equality')], [c_16, c_566])).
% 9.21/3.65  tff(c_645, plain, (![A_15, C_126]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_126))=C_126)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_632])).
% 9.21/3.65  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.21/3.65  tff(c_649, plain, (![A_127, C_128]: (k5_xboole_0(A_127, k5_xboole_0(A_127, C_128))=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_632])).
% 9.21/3.65  tff(c_717, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k5_xboole_0(B_130, A_129))=B_130)), inference(superposition, [status(thm), theory('equality')], [c_2, c_649])).
% 9.21/3.65  tff(c_753, plain, (![A_15, C_126]: (k5_xboole_0(k5_xboole_0(A_15, C_126), C_126)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_645, c_717])).
% 9.21/3.65  tff(c_20, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.21/3.65  tff(c_199, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.21/3.65  tff(c_219, plain, (![B_84, A_85]: (k3_tarski(k2_tarski(B_84, A_85))=k2_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_20, c_199])).
% 9.21/3.65  tff(c_60, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.21/3.65  tff(c_228, plain, (![B_84, A_85]: (k2_xboole_0(B_84, A_85)=k2_xboole_0(A_85, B_84))), inference(superposition, [status(thm), theory('equality')], [c_219, c_60])).
% 9.21/3.65  tff(c_64, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.21/3.65  tff(c_7066, plain, (![A_13095, B_13096]: (k5_xboole_0(k2_xboole_0(A_13095, B_13096), k5_xboole_0(A_13095, B_13096))=k3_xboole_0(A_13095, B_13096))), inference(superposition, [status(thm), theory('equality')], [c_2, c_430])).
% 9.21/3.65  tff(c_16163, plain, (![A_19913, B_19914]: (k5_xboole_0(k2_xboole_0(A_19913, B_19914), k3_xboole_0(A_19913, B_19914))=k5_xboole_0(A_19913, B_19914))), inference(superposition, [status(thm), theory('equality')], [c_7066, c_645])).
% 9.21/3.65  tff(c_16286, plain, (k5_xboole_0(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), k2_tarski('#skF_4', '#skF_5'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_64, c_16163])).
% 9.21/3.65  tff(c_16316, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))=k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_228, c_2, c_16286])).
% 9.21/3.65  tff(c_698, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_649])).
% 9.21/3.65  tff(c_747, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_698, c_717])).
% 9.21/3.65  tff(c_16373, plain, (k5_xboole_0(k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), k2_tarski('#skF_4', '#skF_5'))=k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16316, c_747])).
% 9.21/3.65  tff(c_16403, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_16373])).
% 9.21/3.65  tff(c_163, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.21/3.65  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.21/3.65  tff(c_172, plain, (![B_75, A_74]: (r2_hidden(B_75, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_24])).
% 9.21/3.65  tff(c_58, plain, (![A_54, B_55]: (r1_tarski(A_54, k3_tarski(B_55)) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.21/3.65  tff(c_26, plain, (![E_26, A_20, C_22]: (r2_hidden(E_26, k1_enumset1(A_20, E_26, C_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.21/3.65  tff(c_169, plain, (![A_74, B_75]: (r2_hidden(A_74, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_26])).
% 9.21/3.65  tff(c_287, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.21/3.65  tff(c_324, plain, (![A_99, B_100, B_101]: (r2_hidden(A_99, B_100) | ~r1_tarski(k2_tarski(A_99, B_101), B_100))), inference(resolution, [status(thm)], [c_169, c_287])).
% 9.21/3.65  tff(c_396, plain, (![A_117, B_118, B_119]: (r2_hidden(A_117, k3_tarski(B_118)) | ~r2_hidden(k2_tarski(A_117, B_119), B_118))), inference(resolution, [status(thm)], [c_58, c_324])).
% 9.21/3.65  tff(c_400, plain, (![A_117, A_74, B_119]: (r2_hidden(A_117, k3_tarski(k2_tarski(A_74, k2_tarski(A_117, B_119)))))), inference(resolution, [status(thm)], [c_172, c_396])).
% 9.21/3.65  tff(c_424, plain, (![A_117, A_74, B_119]: (r2_hidden(A_117, k2_xboole_0(A_74, k2_tarski(A_117, B_119))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_400])).
% 9.21/3.65  tff(c_16439, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_16403, c_424])).
% 9.21/3.65  tff(c_16455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_16439])).
% 9.21/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.65  
% 9.21/3.65  Inference rules
% 9.21/3.65  ----------------------
% 9.21/3.65  #Ref     : 0
% 9.21/3.65  #Sup     : 3234
% 9.21/3.65  #Fact    : 18
% 9.21/3.65  #Define  : 0
% 9.21/3.65  #Split   : 0
% 9.21/3.65  #Chain   : 0
% 9.21/3.65  #Close   : 0
% 9.21/3.65  
% 9.21/3.65  Ordering : KBO
% 9.21/3.65  
% 9.21/3.65  Simplification rules
% 9.21/3.65  ----------------------
% 9.21/3.65  #Subsume      : 233
% 9.21/3.65  #Demod        : 2614
% 9.21/3.65  #Tautology    : 1306
% 9.21/3.65  #SimpNegUnit  : 1
% 9.21/3.65  #BackRed      : 1
% 9.21/3.65  
% 9.21/3.65  #Partial instantiations: 6912
% 9.21/3.65  #Strategies tried      : 1
% 9.21/3.65  
% 9.21/3.65  Timing (in seconds)
% 9.21/3.65  ----------------------
% 9.21/3.66  Preprocessing        : 0.33
% 9.21/3.66  Parsing              : 0.17
% 9.21/3.66  CNF conversion       : 0.02
% 9.21/3.66  Main loop            : 2.55
% 9.21/3.66  Inferencing          : 0.85
% 9.21/3.66  Reduction            : 1.20
% 9.21/3.66  Demodulation         : 1.08
% 9.21/3.66  BG Simplification    : 0.09
% 9.21/3.66  Subsumption          : 0.32
% 9.21/3.66  Abstraction          : 0.10
% 9.21/3.66  MUC search           : 0.00
% 9.21/3.66  Cooper               : 0.00
% 9.21/3.66  Total                : 2.92
% 9.21/3.66  Index Insertion      : 0.00
% 9.21/3.66  Index Deletion       : 0.00
% 9.21/3.66  Index Matching       : 0.00
% 9.21/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
