%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 13.47s
% Output     : CNFRefutation 13.47s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 120 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 130 expanded)
%              Number of equality atoms :   41 (  82 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_242,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_249,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_242])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1154,plain,(
    ! [A_75,B_76] : k3_xboole_0(k4_xboole_0(A_75,B_76),A_75) = k4_xboole_0(A_75,B_76) ),
    inference(resolution,[status(thm)],[c_14,c_242])).

tff(c_946,plain,(
    ! [A_65,B_66,C_67] : k3_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k3_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_991,plain,(
    ! [C_67] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_67)) = k3_xboole_0('#skF_1',C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_946])).

tff(c_1161,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_991])).

tff(c_1219,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_1161])).

tff(c_148,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_36] : k5_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_258,plain,(
    ! [A_40,B_41] : k5_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1384,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(B_83,A_82)) = k4_xboole_0(A_82,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_24,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_340,plain,(
    ! [A_46,B_47,C_48] : k5_xboole_0(k5_xboole_0(A_46,B_47),C_48) = k5_xboole_0(A_46,k5_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_404,plain,(
    ! [A_24,C_48] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_48)) = k5_xboole_0(k1_xboole_0,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_340])).

tff(c_417,plain,(
    ! [A_24,C_48] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_48)) = C_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_404])).

tff(c_1399,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(B_83,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_417])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5360,plain,(
    ! [A_143,A_141,B_142] : k5_xboole_0(A_143,k5_xboole_0(A_141,B_142)) = k5_xboole_0(A_141,k5_xboole_0(B_142,A_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_340])).

tff(c_5838,plain,(
    ! [A_144,A_145] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_144,A_145)) = k5_xboole_0(A_145,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_5360])).

tff(c_5926,plain,(
    ! [A_82,B_83] : k5_xboole_0(k4_xboole_0(A_82,B_83),A_82) = k5_xboole_0(k1_xboole_0,k3_xboole_0(B_83,A_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_5838])).

tff(c_6026,plain,(
    ! [A_82,B_83] : k5_xboole_0(k4_xboole_0(A_82,B_83),A_82) = k3_xboole_0(B_83,A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_5926])).

tff(c_1180,plain,(
    ! [A_75,B_76] : k3_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5985,plain,(
    ! [A_5,B_6] : k5_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5838])).

tff(c_6622,plain,(
    ! [A_150,B_151] : k5_xboole_0(k3_xboole_0(A_150,B_151),A_150) = k4_xboole_0(A_150,B_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_5985])).

tff(c_6731,plain,(
    ! [A_75,B_76] : k5_xboole_0(k4_xboole_0(A_75,B_76),A_75) = k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_6622])).

tff(c_40904,plain,(
    ! [A_416,B_417] : k4_xboole_0(A_416,k4_xboole_0(A_416,B_417)) = k3_xboole_0(B_417,A_416) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6026,c_6731])).

tff(c_41523,plain,(
    ! [B_418,A_419] : r1_tarski(k3_xboole_0(B_418,A_419),A_419) ),
    inference(superposition,[status(thm),theory(equality)],[c_40904,c_14])).

tff(c_41712,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_41523])).

tff(c_41784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_41712])).

tff(c_41785,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_41885,plain,(
    ! [A_423,B_424] :
      ( k3_xboole_0(A_423,B_424) = A_423
      | ~ r1_tarski(A_423,B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41896,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_41885])).

tff(c_42174,plain,(
    ! [A_438,B_439,C_440] : k4_xboole_0(k3_xboole_0(A_438,B_439),C_440) = k3_xboole_0(A_438,k4_xboole_0(B_439,C_440)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42697,plain,(
    ! [A_453,B_454,C_455] : r1_xboole_0(k3_xboole_0(A_453,k4_xboole_0(B_454,C_455)),C_455) ),
    inference(superposition,[status(thm),theory(equality)],[c_42174,c_20])).

tff(c_42729,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_41896,c_42697])).

tff(c_42749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41785,c_42729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:22:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.47/7.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.47/7.06  
% 13.47/7.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.47/7.06  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.47/7.06  
% 13.47/7.06  %Foreground sorts:
% 13.47/7.06  
% 13.47/7.06  
% 13.47/7.06  %Background operators:
% 13.47/7.06  
% 13.47/7.06  
% 13.47/7.06  %Foreground operators:
% 13.47/7.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.47/7.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.47/7.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.47/7.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.47/7.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.47/7.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.47/7.06  tff('#skF_2', type, '#skF_2': $i).
% 13.47/7.06  tff('#skF_3', type, '#skF_3': $i).
% 13.47/7.06  tff('#skF_1', type, '#skF_1': $i).
% 13.47/7.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.47/7.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.47/7.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.47/7.06  
% 13.47/7.07  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.47/7.07  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.47/7.07  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.47/7.07  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.47/7.07  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.47/7.07  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.47/7.07  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.47/7.07  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.47/7.07  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.47/7.07  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.47/7.07  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.47/7.07  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.47/7.07  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.47/7.07  tff(c_145, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 13.47/7.07  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.47/7.07  tff(c_242, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.47/7.07  tff(c_249, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_242])).
% 13.47/7.07  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.47/7.07  tff(c_1154, plain, (![A_75, B_76]: (k3_xboole_0(k4_xboole_0(A_75, B_76), A_75)=k4_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_14, c_242])).
% 13.47/7.07  tff(c_946, plain, (![A_65, B_66, C_67]: (k3_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k3_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.47/7.07  tff(c_991, plain, (![C_67]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_67))=k3_xboole_0('#skF_1', C_67))), inference(superposition, [status(thm), theory('equality')], [c_249, c_946])).
% 13.47/7.07  tff(c_1161, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1154, c_991])).
% 13.47/7.07  tff(c_1219, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_1161])).
% 13.47/7.07  tff(c_148, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.47/7.07  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.47/7.07  tff(c_164, plain, (![A_36]: (k5_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_148, c_18])).
% 13.47/7.07  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.47/7.07  tff(c_258, plain, (![A_40, B_41]: (k5_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.47/7.07  tff(c_1384, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(B_83, A_82))=k4_xboole_0(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_258])).
% 13.47/7.07  tff(c_24, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.47/7.07  tff(c_340, plain, (![A_46, B_47, C_48]: (k5_xboole_0(k5_xboole_0(A_46, B_47), C_48)=k5_xboole_0(A_46, k5_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.47/7.07  tff(c_404, plain, (![A_24, C_48]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_48))=k5_xboole_0(k1_xboole_0, C_48))), inference(superposition, [status(thm), theory('equality')], [c_24, c_340])).
% 13.47/7.07  tff(c_417, plain, (![A_24, C_48]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_48))=C_48)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_404])).
% 13.47/7.07  tff(c_1399, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(B_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_1384, c_417])).
% 13.47/7.07  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.47/7.07  tff(c_5360, plain, (![A_143, A_141, B_142]: (k5_xboole_0(A_143, k5_xboole_0(A_141, B_142))=k5_xboole_0(A_141, k5_xboole_0(B_142, A_143)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_340])).
% 13.47/7.07  tff(c_5838, plain, (![A_144, A_145]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_144, A_145))=k5_xboole_0(A_145, A_144))), inference(superposition, [status(thm), theory('equality')], [c_164, c_5360])).
% 13.47/7.07  tff(c_5926, plain, (![A_82, B_83]: (k5_xboole_0(k4_xboole_0(A_82, B_83), A_82)=k5_xboole_0(k1_xboole_0, k3_xboole_0(B_83, A_82)))), inference(superposition, [status(thm), theory('equality')], [c_1399, c_5838])).
% 13.47/7.07  tff(c_6026, plain, (![A_82, B_83]: (k5_xboole_0(k4_xboole_0(A_82, B_83), A_82)=k3_xboole_0(B_83, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_5926])).
% 13.47/7.07  tff(c_1180, plain, (![A_75, B_76]: (k3_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_2])).
% 13.47/7.07  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.47/7.07  tff(c_5985, plain, (![A_5, B_6]: (k5_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5838])).
% 13.47/7.07  tff(c_6622, plain, (![A_150, B_151]: (k5_xboole_0(k3_xboole_0(A_150, B_151), A_150)=k4_xboole_0(A_150, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_5985])).
% 13.47/7.07  tff(c_6731, plain, (![A_75, B_76]: (k5_xboole_0(k4_xboole_0(A_75, B_76), A_75)=k4_xboole_0(A_75, k4_xboole_0(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_1180, c_6622])).
% 13.47/7.07  tff(c_40904, plain, (![A_416, B_417]: (k4_xboole_0(A_416, k4_xboole_0(A_416, B_417))=k3_xboole_0(B_417, A_416))), inference(demodulation, [status(thm), theory('equality')], [c_6026, c_6731])).
% 13.47/7.07  tff(c_41523, plain, (![B_418, A_419]: (r1_tarski(k3_xboole_0(B_418, A_419), A_419))), inference(superposition, [status(thm), theory('equality')], [c_40904, c_14])).
% 13.47/7.07  tff(c_41712, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1219, c_41523])).
% 13.47/7.07  tff(c_41784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_41712])).
% 13.47/7.07  tff(c_41785, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 13.47/7.07  tff(c_41885, plain, (![A_423, B_424]: (k3_xboole_0(A_423, B_424)=A_423 | ~r1_tarski(A_423, B_424))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.47/7.07  tff(c_41896, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_41885])).
% 13.47/7.07  tff(c_42174, plain, (![A_438, B_439, C_440]: (k4_xboole_0(k3_xboole_0(A_438, B_439), C_440)=k3_xboole_0(A_438, k4_xboole_0(B_439, C_440)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.47/7.07  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.47/7.07  tff(c_42697, plain, (![A_453, B_454, C_455]: (r1_xboole_0(k3_xboole_0(A_453, k4_xboole_0(B_454, C_455)), C_455))), inference(superposition, [status(thm), theory('equality')], [c_42174, c_20])).
% 13.47/7.07  tff(c_42729, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_41896, c_42697])).
% 13.47/7.07  tff(c_42749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41785, c_42729])).
% 13.47/7.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.47/7.07  
% 13.47/7.07  Inference rules
% 13.47/7.07  ----------------------
% 13.47/7.07  #Ref     : 0
% 13.47/7.07  #Sup     : 10860
% 13.47/7.07  #Fact    : 0
% 13.47/7.07  #Define  : 0
% 13.47/7.07  #Split   : 1
% 13.47/7.07  #Chain   : 0
% 13.47/7.07  #Close   : 0
% 13.47/7.07  
% 13.47/7.07  Ordering : KBO
% 13.47/7.07  
% 13.47/7.07  Simplification rules
% 13.47/7.07  ----------------------
% 13.47/7.07  #Subsume      : 335
% 13.47/7.07  #Demod        : 11978
% 13.47/7.07  #Tautology    : 6371
% 13.47/7.07  #SimpNegUnit  : 2
% 13.47/7.07  #BackRed      : 2
% 13.47/7.07  
% 13.47/7.07  #Partial instantiations: 0
% 13.47/7.07  #Strategies tried      : 1
% 13.47/7.07  
% 13.47/7.07  Timing (in seconds)
% 13.47/7.07  ----------------------
% 13.47/7.07  Preprocessing        : 0.29
% 13.47/7.07  Parsing              : 0.15
% 13.47/7.08  CNF conversion       : 0.02
% 13.47/7.08  Main loop            : 6.01
% 13.47/7.08  Inferencing          : 0.87
% 13.47/7.08  Reduction            : 3.91
% 13.47/7.08  Demodulation         : 3.61
% 13.47/7.08  BG Simplification    : 0.11
% 13.47/7.08  Subsumption          : 0.88
% 13.47/7.08  Abstraction          : 0.18
% 13.47/7.08  MUC search           : 0.00
% 13.47/7.08  Cooper               : 0.00
% 13.47/7.08  Total                : 6.33
% 13.47/7.08  Index Insertion      : 0.00
% 13.47/7.08  Index Deletion       : 0.00
% 13.47/7.08  Index Matching       : 0.00
% 13.47/7.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
