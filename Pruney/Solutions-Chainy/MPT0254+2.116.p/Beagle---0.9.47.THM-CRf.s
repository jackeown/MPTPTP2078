%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:34 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 151 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 198 expanded)
%              Number of equality atoms :   35 (  77 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(c_44,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,(
    ! [D_35,B_36] : r2_hidden(D_35,k2_tarski(D_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_69])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),k5_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_315,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(A_77,k2_xboole_0(B_78,C_79))
      | ~ r1_tarski(A_77,k5_xboole_0(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_335,plain,(
    ! [A_80,B_81] : r1_tarski(k4_xboole_0(A_80,B_81),k2_xboole_0(A_80,B_81)) ),
    inference(resolution,[status(thm)],[c_24,c_315])).

tff(c_353,plain,(
    r1_tarski(k4_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_335])).

tff(c_18,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_363,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_353,c_18])).

tff(c_50,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),B_31) = k1_tarski(A_30)
      | r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_383,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_50])).

tff(c_495,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | k4_xboole_0(k1_tarski(A_30),B_31) != k1_tarski(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_380,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k1_tarski('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_48])).

tff(c_503,plain,(
    k1_tarski('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_380])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_45,B_46] : r1_tarski(k4_xboole_0(A_45,B_46),k5_xboole_0(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_121,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_603,plain,(
    ! [A_98,B_99] : r1_tarski(k4_xboole_0(A_98,B_99),k2_xboole_0(B_99,A_98)) ),
    inference(resolution,[status(thm)],[c_121,c_315])).

tff(c_627,plain,(
    r1_tarski(k4_xboole_0('#skF_4',k1_tarski('#skF_3')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_603])).

tff(c_636,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_627,c_18])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_660,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_16])).

tff(c_674,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_660])).

tff(c_334,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),k2_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_24,c_315])).

tff(c_687,plain,(
    r1_tarski(k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_334])).

tff(c_741,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_687,c_18])).

tff(c_22,plain,(
    ! [A_18] :
      ( r2_xboole_0(k1_xboole_0,A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_112,plain,(
    ! [B_42,A_43] :
      ( k4_xboole_0(B_42,A_43) != k1_xboole_0
      | ~ r2_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    ! [A_18] :
      ( k4_xboole_0(A_18,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_18 ) ),
    inference(resolution,[status(thm)],[c_22,c_112])).

tff(c_780,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_116])).

tff(c_798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_503,c_780])).

tff(c_799,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_364,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_353])).

tff(c_144,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(k4_xboole_0(A_51,C_52),B_53)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_149,plain,(
    ! [A_51,C_52] :
      ( k4_xboole_0(A_51,C_52) = k1_xboole_0
      | ~ r1_tarski(A_51,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_410,plain,(
    ! [C_52] : k4_xboole_0(k1_xboole_0,C_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_364,c_149])).

tff(c_808,plain,(
    ! [B_31] :
      ( ~ r2_hidden('#skF_3',B_31)
      | k4_xboole_0(k1_xboole_0,B_31) != k1_tarski('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_48])).

tff(c_824,plain,(
    ! [B_104] : ~ r2_hidden('#skF_3',B_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_410,c_808])).

tff(c_835,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_72,c_824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.84/1.43  
% 2.84/1.43  %Foreground sorts:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Background operators:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Foreground operators:
% 2.84/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.84/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.43  
% 2.84/1.45  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.45  tff(f_68, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.84/1.45  tff(f_81, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.84/1.45  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 2.84/1.45  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 2.84/1.45  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.84/1.45  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.84/1.45  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.84/1.45  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.84/1.45  tff(f_57, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.84/1.45  tff(f_34, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.84/1.45  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.84/1.45  tff(c_44, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.84/1.45  tff(c_69, plain, (![D_35, B_36]: (r2_hidden(D_35, k2_tarski(D_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.84/1.45  tff(c_72, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_69])).
% 2.84/1.45  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.84/1.45  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), k5_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.45  tff(c_315, plain, (![A_77, B_78, C_79]: (r1_tarski(A_77, k2_xboole_0(B_78, C_79)) | ~r1_tarski(A_77, k5_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.84/1.45  tff(c_335, plain, (![A_80, B_81]: (r1_tarski(k4_xboole_0(A_80, B_81), k2_xboole_0(A_80, B_81)))), inference(resolution, [status(thm)], [c_24, c_315])).
% 2.84/1.45  tff(c_353, plain, (r1_tarski(k4_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_335])).
% 2.84/1.45  tff(c_18, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.45  tff(c_363, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_353, c_18])).
% 2.84/1.45  tff(c_50, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), B_31)=k1_tarski(A_30) | r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_383, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_363, c_50])).
% 2.84/1.45  tff(c_495, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_383])).
% 2.84/1.45  tff(c_48, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | k4_xboole_0(k1_tarski(A_30), B_31)!=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_380, plain, (~r2_hidden('#skF_3', '#skF_4') | k1_tarski('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_363, c_48])).
% 2.84/1.45  tff(c_503, plain, (k1_tarski('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_495, c_380])).
% 2.84/1.45  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.45  tff(c_118, plain, (![A_45, B_46]: (r1_tarski(k4_xboole_0(A_45, B_46), k5_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.45  tff(c_121, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 2.84/1.45  tff(c_603, plain, (![A_98, B_99]: (r1_tarski(k4_xboole_0(A_98, B_99), k2_xboole_0(B_99, A_98)))), inference(resolution, [status(thm)], [c_121, c_315])).
% 2.84/1.45  tff(c_627, plain, (r1_tarski(k4_xboole_0('#skF_4', k1_tarski('#skF_3')), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_603])).
% 2.84/1.45  tff(c_636, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_627, c_18])).
% 2.84/1.45  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.45  tff(c_660, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_636, c_16])).
% 2.84/1.45  tff(c_674, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_660])).
% 2.84/1.45  tff(c_334, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), k2_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_24, c_315])).
% 2.84/1.45  tff(c_687, plain, (r1_tarski(k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_674, c_334])).
% 2.84/1.45  tff(c_741, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_687, c_18])).
% 2.84/1.45  tff(c_22, plain, (![A_18]: (r2_xboole_0(k1_xboole_0, A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_112, plain, (![B_42, A_43]: (k4_xboole_0(B_42, A_43)!=k1_xboole_0 | ~r2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.84/1.45  tff(c_116, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_18)), inference(resolution, [status(thm)], [c_22, c_112])).
% 2.84/1.45  tff(c_780, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_741, c_116])).
% 2.84/1.45  tff(c_798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_503, c_780])).
% 2.84/1.45  tff(c_799, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_383])).
% 2.84/1.45  tff(c_364, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_363, c_353])).
% 2.84/1.45  tff(c_144, plain, (![A_51, C_52, B_53]: (r1_tarski(k4_xboole_0(A_51, C_52), B_53) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.45  tff(c_149, plain, (![A_51, C_52]: (k4_xboole_0(A_51, C_52)=k1_xboole_0 | ~r1_tarski(A_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_144, c_18])).
% 2.84/1.45  tff(c_410, plain, (![C_52]: (k4_xboole_0(k1_xboole_0, C_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_364, c_149])).
% 2.84/1.45  tff(c_808, plain, (![B_31]: (~r2_hidden('#skF_3', B_31) | k4_xboole_0(k1_xboole_0, B_31)!=k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_799, c_48])).
% 2.84/1.45  tff(c_824, plain, (![B_104]: (~r2_hidden('#skF_3', B_104))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_410, c_808])).
% 2.84/1.45  tff(c_835, plain, $false, inference(resolution, [status(thm)], [c_72, c_824])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 198
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 1
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 4
% 2.84/1.45  #Demod        : 98
% 2.84/1.45  #Tautology    : 108
% 2.84/1.45  #SimpNegUnit  : 2
% 2.84/1.45  #BackRed      : 7
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.33
% 2.84/1.45  Parsing              : 0.16
% 2.84/1.45  CNF conversion       : 0.02
% 2.84/1.45  Main loop            : 0.36
% 2.84/1.45  Inferencing          : 0.12
% 2.84/1.45  Reduction            : 0.13
% 2.84/1.45  Demodulation         : 0.10
% 2.84/1.45  BG Simplification    : 0.02
% 2.84/1.45  Subsumption          : 0.06
% 2.84/1.45  Abstraction          : 0.02
% 2.84/1.45  MUC search           : 0.00
% 2.84/1.45  Cooper               : 0.00
% 2.84/1.45  Total                : 0.72
% 2.84/1.45  Index Insertion      : 0.00
% 2.84/1.45  Index Deletion       : 0.00
% 2.84/1.45  Index Matching       : 0.00
% 2.84/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
