%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:38 EST 2020

% Result     : Theorem 10.43s
% Output     : CNFRefutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 187 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 243 expanded)
%              Number of equality atoms :   61 ( 153 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_18,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_40,B_41] : k3_xboole_0(A_40,k2_xboole_0(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_1536,plain,(
    ! [A_97,B_98,C_99] : k4_xboole_0(k3_xboole_0(A_97,B_98),C_99) = k3_xboole_0(A_97,k4_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1629,plain,(
    ! [A_100,C_101] : k3_xboole_0(A_100,k4_xboole_0(A_100,C_101)) = k4_xboole_0(A_100,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1536])).

tff(c_24,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1668,plain,(
    ! [A_100,C_101] : k2_xboole_0(k4_xboole_0(A_100,C_101),k4_xboole_0(A_100,k4_xboole_0(A_100,C_101))) = A_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_1629,c_24])).

tff(c_5597,plain,(
    ! [A_195,C_196] : k2_xboole_0(k4_xboole_0(A_195,C_196),k3_xboole_0(A_195,C_196)) = A_195 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1668])).

tff(c_26,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k4_xboole_0(A_30,B_31),k3_xboole_0(A_30,C_32)) = k4_xboole_0(A_30,k4_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5639,plain,(
    ! [A_195,C_196] : k4_xboole_0(A_195,k4_xboole_0(C_196,C_196)) = A_195 ),
    inference(superposition,[status(thm),theory(equality)],[c_5597,c_26])).

tff(c_678,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(k1_tarski(A_72),B_73) = k1_tarski(A_72)
      | r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22307,plain,(
    ! [A_363,B_364] :
      ( k4_xboole_0(k1_tarski(A_363),k1_tarski(A_363)) = k3_xboole_0(k1_tarski(A_363),B_364)
      | r2_hidden(A_363,B_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1609,plain,(
    ! [A_3,C_99] : k3_xboole_0(A_3,k4_xboole_0(A_3,C_99)) = k4_xboole_0(A_3,C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1536])).

tff(c_108,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_18])).

tff(c_5045,plain,(
    ! [A_189,B_190] : k4_xboole_0(A_189,k3_xboole_0(A_189,B_190)) = k4_xboole_0(A_189,B_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_111])).

tff(c_5178,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5045])).

tff(c_22453,plain,(
    ! [B_364,A_363] :
      ( k4_xboole_0(B_364,k4_xboole_0(k1_tarski(A_363),k1_tarski(A_363))) = k4_xboole_0(B_364,k1_tarski(A_363))
      | r2_hidden(A_363,B_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22307,c_5178])).

tff(c_22835,plain,(
    ! [B_365,A_366] :
      ( k4_xboole_0(B_365,k1_tarski(A_366)) = B_365
      | r2_hidden(A_366,B_365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5639,c_22453])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_23061,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22835,c_123])).

tff(c_23169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_23061])).

tff(c_23170,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_23402,plain,(
    ! [B_376,A_377] :
      ( k3_xboole_0(B_376,k1_tarski(A_377)) = k1_tarski(A_377)
      | ~ r2_hidden(A_377,B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_23171,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_23305,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23171,c_40])).

tff(c_23312,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23305,c_18])).

tff(c_23415,plain,
    ( k4_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23402,c_23312])).

tff(c_23459,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23170,c_23415])).

tff(c_23309,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3',k1_tarski('#skF_4')),'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_23305,c_24])).

tff(c_23326,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23312,c_23309])).

tff(c_23465,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23459,c_23326])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23489,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23465,c_12])).

tff(c_23501,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23459,c_23489])).

tff(c_23599,plain,(
    ! [A_378,B_379] :
      ( ~ r2_hidden(A_378,B_379)
      | k4_xboole_0(k1_tarski(A_378),B_379) != k1_tarski(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_23605,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23501,c_23599])).

tff(c_23614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23170,c_23605])).

tff(c_23615,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_24539,plain,(
    ! [B_416,A_417] :
      ( k3_xboole_0(B_416,k1_tarski(A_417)) = k1_tarski(A_417)
      | ~ r2_hidden(A_417,B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_23616,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_23706,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23616,c_42])).

tff(c_23710,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23706,c_18])).

tff(c_24582,plain,
    ( k4_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24539,c_23710])).

tff(c_24634,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23615,c_24582])).

tff(c_23743,plain,(
    ! [A_393,B_394] : k2_xboole_0(k3_xboole_0(A_393,B_394),k4_xboole_0(A_393,B_394)) = A_393 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23761,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3',k1_tarski('#skF_4')),'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_23706,c_23743])).

tff(c_23784,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23710,c_23761])).

tff(c_23790,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_3'),'#skF_3') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23784,c_12])).

tff(c_24642,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24634,c_24634,c_23790])).

tff(c_32,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | k4_xboole_0(k1_tarski(A_37),B_38) != k1_tarski(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24764,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24642,c_32])).

tff(c_24785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23615,c_24764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.43/3.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.78  
% 10.43/3.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.78  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.43/3.78  
% 10.43/3.78  %Foreground sorts:
% 10.43/3.78  
% 10.43/3.78  
% 10.43/3.78  %Background operators:
% 10.43/3.78  
% 10.43/3.78  
% 10.43/3.78  %Foreground operators:
% 10.43/3.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.43/3.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.43/3.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.43/3.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.43/3.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.43/3.78  tff('#skF_2', type, '#skF_2': $i).
% 10.43/3.78  tff('#skF_3', type, '#skF_3': $i).
% 10.43/3.78  tff('#skF_1', type, '#skF_1': $i).
% 10.43/3.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.43/3.78  tff('#skF_4', type, '#skF_4': $i).
% 10.43/3.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.43/3.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.43/3.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.43/3.78  
% 10.43/3.80  tff(f_74, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.43/3.80  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.43/3.80  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.43/3.80  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 10.43/3.80  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.43/3.80  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.43/3.80  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 10.43/3.80  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 10.43/3.80  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.43/3.80  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 10.43/3.80  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.43/3.80  tff(c_38, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.43/3.80  tff(c_52, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 10.43/3.80  tff(c_18, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.43/3.80  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.43/3.80  tff(c_53, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k2_xboole_0(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.43/3.80  tff(c_62, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 10.43/3.80  tff(c_1536, plain, (![A_97, B_98, C_99]: (k4_xboole_0(k3_xboole_0(A_97, B_98), C_99)=k3_xboole_0(A_97, k4_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.43/3.80  tff(c_1629, plain, (![A_100, C_101]: (k3_xboole_0(A_100, k4_xboole_0(A_100, C_101))=k4_xboole_0(A_100, C_101))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1536])).
% 10.43/3.80  tff(c_24, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.43/3.80  tff(c_1668, plain, (![A_100, C_101]: (k2_xboole_0(k4_xboole_0(A_100, C_101), k4_xboole_0(A_100, k4_xboole_0(A_100, C_101)))=A_100)), inference(superposition, [status(thm), theory('equality')], [c_1629, c_24])).
% 10.43/3.80  tff(c_5597, plain, (![A_195, C_196]: (k2_xboole_0(k4_xboole_0(A_195, C_196), k3_xboole_0(A_195, C_196))=A_195)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1668])).
% 10.43/3.80  tff(c_26, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k4_xboole_0(A_30, B_31), k3_xboole_0(A_30, C_32))=k4_xboole_0(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.43/3.80  tff(c_5639, plain, (![A_195, C_196]: (k4_xboole_0(A_195, k4_xboole_0(C_196, C_196))=A_195)), inference(superposition, [status(thm), theory('equality')], [c_5597, c_26])).
% 10.43/3.80  tff(c_678, plain, (![A_72, B_73]: (k4_xboole_0(k1_tarski(A_72), B_73)=k1_tarski(A_72) | r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.43/3.80  tff(c_22307, plain, (![A_363, B_364]: (k4_xboole_0(k1_tarski(A_363), k1_tarski(A_363))=k3_xboole_0(k1_tarski(A_363), B_364) | r2_hidden(A_363, B_364))), inference(superposition, [status(thm), theory('equality')], [c_678, c_18])).
% 10.43/3.80  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.43/3.80  tff(c_1609, plain, (![A_3, C_99]: (k3_xboole_0(A_3, k4_xboole_0(A_3, C_99))=k4_xboole_0(A_3, C_99))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1536])).
% 10.43/3.80  tff(c_108, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.43/3.80  tff(c_111, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_18])).
% 10.43/3.80  tff(c_5045, plain, (![A_189, B_190]: (k4_xboole_0(A_189, k3_xboole_0(A_189, B_190))=k4_xboole_0(A_189, B_190))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_111])).
% 10.43/3.80  tff(c_5178, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5045])).
% 10.43/3.80  tff(c_22453, plain, (![B_364, A_363]: (k4_xboole_0(B_364, k4_xboole_0(k1_tarski(A_363), k1_tarski(A_363)))=k4_xboole_0(B_364, k1_tarski(A_363)) | r2_hidden(A_363, B_364))), inference(superposition, [status(thm), theory('equality')], [c_22307, c_5178])).
% 10.43/3.80  tff(c_22835, plain, (![B_365, A_366]: (k4_xboole_0(B_365, k1_tarski(A_366))=B_365 | r2_hidden(A_366, B_365))), inference(demodulation, [status(thm), theory('equality')], [c_5639, c_22453])).
% 10.43/3.80  tff(c_36, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.43/3.80  tff(c_123, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_36])).
% 10.43/3.80  tff(c_23061, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22835, c_123])).
% 10.43/3.80  tff(c_23169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_23061])).
% 10.43/3.80  tff(c_23170, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 10.43/3.80  tff(c_23402, plain, (![B_376, A_377]: (k3_xboole_0(B_376, k1_tarski(A_377))=k1_tarski(A_377) | ~r2_hidden(A_377, B_376))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.43/3.80  tff(c_23171, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 10.43/3.80  tff(c_40, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.43/3.80  tff(c_23305, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23171, c_40])).
% 10.43/3.80  tff(c_23312, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23305, c_18])).
% 10.43/3.80  tff(c_23415, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23402, c_23312])).
% 10.43/3.80  tff(c_23459, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23170, c_23415])).
% 10.43/3.80  tff(c_23309, plain, (k2_xboole_0(k3_xboole_0('#skF_3', k1_tarski('#skF_4')), '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_23305, c_24])).
% 10.43/3.80  tff(c_23326, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23312, c_23309])).
% 10.43/3.80  tff(c_23465, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23459, c_23326])).
% 10.43/3.80  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.43/3.80  tff(c_23489, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23465, c_12])).
% 10.43/3.80  tff(c_23501, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23459, c_23489])).
% 10.43/3.80  tff(c_23599, plain, (![A_378, B_379]: (~r2_hidden(A_378, B_379) | k4_xboole_0(k1_tarski(A_378), B_379)!=k1_tarski(A_378))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.43/3.80  tff(c_23605, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23501, c_23599])).
% 10.43/3.80  tff(c_23614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23170, c_23605])).
% 10.43/3.80  tff(c_23615, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 10.43/3.80  tff(c_24539, plain, (![B_416, A_417]: (k3_xboole_0(B_416, k1_tarski(A_417))=k1_tarski(A_417) | ~r2_hidden(A_417, B_416))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.43/3.80  tff(c_23616, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 10.43/3.80  tff(c_42, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.43/3.80  tff(c_23706, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23616, c_42])).
% 10.43/3.80  tff(c_23710, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23706, c_18])).
% 10.43/3.80  tff(c_24582, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24539, c_23710])).
% 10.43/3.80  tff(c_24634, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23615, c_24582])).
% 10.43/3.80  tff(c_23743, plain, (![A_393, B_394]: (k2_xboole_0(k3_xboole_0(A_393, B_394), k4_xboole_0(A_393, B_394))=A_393)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.43/3.80  tff(c_23761, plain, (k2_xboole_0(k3_xboole_0('#skF_3', k1_tarski('#skF_4')), '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_23706, c_23743])).
% 10.43/3.80  tff(c_23784, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23710, c_23761])).
% 10.43/3.80  tff(c_23790, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_3'), '#skF_3')=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23784, c_12])).
% 10.43/3.80  tff(c_24642, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24634, c_24634, c_23790])).
% 10.43/3.80  tff(c_32, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | k4_xboole_0(k1_tarski(A_37), B_38)!=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.43/3.80  tff(c_24764, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24642, c_32])).
% 10.43/3.80  tff(c_24785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23615, c_24764])).
% 10.43/3.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.80  
% 10.43/3.80  Inference rules
% 10.43/3.80  ----------------------
% 10.43/3.80  #Ref     : 0
% 10.43/3.80  #Sup     : 6302
% 10.43/3.80  #Fact    : 0
% 10.43/3.80  #Define  : 0
% 10.43/3.80  #Split   : 2
% 10.43/3.80  #Chain   : 0
% 10.43/3.80  #Close   : 0
% 10.43/3.80  
% 10.43/3.80  Ordering : KBO
% 10.43/3.80  
% 10.43/3.80  Simplification rules
% 10.43/3.80  ----------------------
% 10.43/3.80  #Subsume      : 562
% 10.43/3.80  #Demod        : 5998
% 10.43/3.80  #Tautology    : 3355
% 10.43/3.80  #SimpNegUnit  : 7
% 10.43/3.80  #BackRed      : 22
% 10.43/3.80  
% 10.43/3.80  #Partial instantiations: 0
% 10.43/3.80  #Strategies tried      : 1
% 10.43/3.80  
% 10.43/3.80  Timing (in seconds)
% 10.43/3.80  ----------------------
% 10.43/3.80  Preprocessing        : 0.30
% 10.43/3.80  Parsing              : 0.16
% 10.43/3.80  CNF conversion       : 0.02
% 10.43/3.80  Main loop            : 2.73
% 10.43/3.80  Inferencing          : 0.61
% 10.43/3.80  Reduction            : 1.44
% 10.43/3.80  Demodulation         : 1.26
% 10.43/3.80  BG Simplification    : 0.08
% 10.43/3.80  Subsumption          : 0.45
% 10.43/3.80  Abstraction          : 0.13
% 10.43/3.80  MUC search           : 0.00
% 10.43/3.80  Cooper               : 0.00
% 10.43/3.80  Total                : 3.07
% 10.43/3.80  Index Insertion      : 0.00
% 10.43/3.80  Index Deletion       : 0.00
% 10.43/3.80  Index Matching       : 0.00
% 10.43/3.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
