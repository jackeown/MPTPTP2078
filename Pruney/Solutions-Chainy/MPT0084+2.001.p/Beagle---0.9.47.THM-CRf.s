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
% DateTime   : Thu Dec  3 09:44:04 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   39 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_519,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(A_58,B_59)
      | k3_xboole_0(A_58,B_59) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_525,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_519,c_36])).

tff(c_528,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_525])).

tff(c_22,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_368,plain,(
    ! [B_50,A_51] : r1_tarski(B_50,k2_xboole_0(A_51,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_30])).

tff(c_413,plain,(
    ! [A_52,B_53] : r1_tarski(k3_xboole_0(A_52,B_53),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_368])).

tff(c_425,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_413])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_222,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_234,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_1355,plain,(
    ! [A_102,B_103,C_104] : k2_xboole_0(k3_xboole_0(A_102,B_103),k3_xboole_0(A_102,C_104)) = k3_xboole_0(A_102,k2_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3051,plain,(
    ! [A_127,B_128,C_129] : r1_tarski(k3_xboole_0(A_127,B_128),k3_xboole_0(A_127,k2_xboole_0(B_128,C_129))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1355,c_30])).

tff(c_3215,plain,(
    ! [A_130] : r1_tarski(k3_xboole_0(A_130,'#skF_2'),k3_xboole_0(A_130,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_3051])).

tff(c_3346,plain,(
    ! [A_132] : r1_tarski(k3_xboole_0(A_132,'#skF_2'),k3_xboole_0('#skF_4',A_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3215])).

tff(c_32,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_32])).

tff(c_356,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_363,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_356])).

tff(c_1145,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(A_87,k3_xboole_0(B_88,C_89))
      | ~ r1_tarski(A_87,C_89)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1154,plain,(
    ! [A_87] :
      ( r1_tarski(A_87,k1_xboole_0)
      | ~ r1_tarski(A_87,k3_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_87,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_1145])).

tff(c_3350,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3346,c_1154])).

tff(c_3409,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_3350])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3427,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3409,c_14])).

tff(c_593,plain,(
    ! [A_62,B_63] : k2_xboole_0(k3_xboole_0(A_62,B_63),k4_xboole_0(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_629,plain,(
    ! [A_66] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_66,k1_xboole_0)) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_593])).

tff(c_47,plain,(
    ! [A_34,B_35] : k2_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_47])).

tff(c_185,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_59])).

tff(c_638,plain,(
    ! [A_66] : k4_xboole_0(A_66,k1_xboole_0) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_185])).

tff(c_698,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_723,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k3_xboole_0(A_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_698])).

tff(c_771,plain,(
    ! [A_72] : k4_xboole_0(A_72,A_72) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_723])).

tff(c_24,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_779,plain,(
    ! [A_72] : k4_xboole_0(A_72,k1_xboole_0) = k3_xboole_0(A_72,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_24])).

tff(c_801,plain,(
    ! [A_72] : k3_xboole_0(A_72,A_72) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_779])).

tff(c_1395,plain,(
    ! [A_72,C_104] : k3_xboole_0(A_72,k2_xboole_0(A_72,C_104)) = k2_xboole_0(A_72,k3_xboole_0(A_72,C_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_1355])).

tff(c_1450,plain,(
    ! [A_72,C_104] : k3_xboole_0(A_72,k2_xboole_0(A_72,C_104)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1395])).

tff(c_3449,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3427,c_1450])).

tff(c_3485,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3449])).

tff(c_3487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_3485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.72  
% 3.84/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.84/1.72  
% 3.84/1.72  %Foreground sorts:
% 3.84/1.72  
% 3.84/1.72  
% 3.84/1.72  %Background operators:
% 3.84/1.72  
% 3.84/1.72  
% 3.84/1.72  %Foreground operators:
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.84/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.84/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.84/1.72  
% 3.84/1.74  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.84/1.74  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.84/1.74  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.84/1.74  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.84/1.74  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.84/1.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.84/1.74  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.84/1.74  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.84/1.74  tff(f_61, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.84/1.74  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.84/1.74  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.84/1.74  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.84/1.74  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.84/1.74  tff(c_519, plain, (![A_58, B_59]: (r1_xboole_0(A_58, B_59) | k3_xboole_0(A_58, B_59)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.74  tff(c_36, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.84/1.74  tff(c_525, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_519, c_36])).
% 3.84/1.74  tff(c_528, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_525])).
% 3.84/1.74  tff(c_22, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.84/1.74  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k3_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.84/1.74  tff(c_169, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.84/1.74  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.84/1.74  tff(c_368, plain, (![B_50, A_51]: (r1_tarski(B_50, k2_xboole_0(A_51, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_30])).
% 3.84/1.74  tff(c_413, plain, (![A_52, B_53]: (r1_tarski(k3_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_18, c_368])).
% 3.84/1.74  tff(c_425, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_413])).
% 3.84/1.74  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.84/1.74  tff(c_222, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.84/1.74  tff(c_234, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_222])).
% 3.84/1.74  tff(c_1355, plain, (![A_102, B_103, C_104]: (k2_xboole_0(k3_xboole_0(A_102, B_103), k3_xboole_0(A_102, C_104))=k3_xboole_0(A_102, k2_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.84/1.74  tff(c_3051, plain, (![A_127, B_128, C_129]: (r1_tarski(k3_xboole_0(A_127, B_128), k3_xboole_0(A_127, k2_xboole_0(B_128, C_129))))), inference(superposition, [status(thm), theory('equality')], [c_1355, c_30])).
% 3.84/1.74  tff(c_3215, plain, (![A_130]: (r1_tarski(k3_xboole_0(A_130, '#skF_2'), k3_xboole_0(A_130, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_234, c_3051])).
% 3.84/1.74  tff(c_3346, plain, (![A_132]: (r1_tarski(k3_xboole_0(A_132, '#skF_2'), k3_xboole_0('#skF_4', A_132)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3215])).
% 3.84/1.74  tff(c_32, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.84/1.74  tff(c_37, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_32])).
% 3.84/1.74  tff(c_356, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.74  tff(c_363, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_356])).
% 3.84/1.74  tff(c_1145, plain, (![A_87, B_88, C_89]: (r1_tarski(A_87, k3_xboole_0(B_88, C_89)) | ~r1_tarski(A_87, C_89) | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.84/1.74  tff(c_1154, plain, (![A_87]: (r1_tarski(A_87, k1_xboole_0) | ~r1_tarski(A_87, k3_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_87, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_1145])).
% 3.84/1.74  tff(c_3350, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_xboole_0) | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_3346, c_1154])).
% 3.84/1.74  tff(c_3409, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_425, c_3350])).
% 3.84/1.74  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.84/1.74  tff(c_3427, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3409, c_14])).
% 3.84/1.74  tff(c_593, plain, (![A_62, B_63]: (k2_xboole_0(k3_xboole_0(A_62, B_63), k4_xboole_0(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.84/1.74  tff(c_629, plain, (![A_66]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_66, k1_xboole_0))=A_66)), inference(superposition, [status(thm), theory('equality')], [c_22, c_593])).
% 3.84/1.74  tff(c_47, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k3_xboole_0(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.84/1.74  tff(c_59, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_22, c_47])).
% 3.84/1.74  tff(c_185, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_169, c_59])).
% 3.84/1.74  tff(c_638, plain, (![A_66]: (k4_xboole_0(A_66, k1_xboole_0)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_629, c_185])).
% 3.84/1.74  tff(c_698, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.84/1.74  tff(c_723, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k3_xboole_0(A_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_638, c_698])).
% 3.84/1.74  tff(c_771, plain, (![A_72]: (k4_xboole_0(A_72, A_72)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_723])).
% 3.84/1.74  tff(c_24, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.84/1.74  tff(c_779, plain, (![A_72]: (k4_xboole_0(A_72, k1_xboole_0)=k3_xboole_0(A_72, A_72))), inference(superposition, [status(thm), theory('equality')], [c_771, c_24])).
% 3.84/1.74  tff(c_801, plain, (![A_72]: (k3_xboole_0(A_72, A_72)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_638, c_779])).
% 3.84/1.74  tff(c_1395, plain, (![A_72, C_104]: (k3_xboole_0(A_72, k2_xboole_0(A_72, C_104))=k2_xboole_0(A_72, k3_xboole_0(A_72, C_104)))), inference(superposition, [status(thm), theory('equality')], [c_801, c_1355])).
% 3.84/1.74  tff(c_1450, plain, (![A_72, C_104]: (k3_xboole_0(A_72, k2_xboole_0(A_72, C_104))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1395])).
% 3.84/1.74  tff(c_3449, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3427, c_1450])).
% 3.84/1.74  tff(c_3485, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3449])).
% 3.84/1.74  tff(c_3487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_528, c_3485])).
% 3.84/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.74  
% 3.84/1.74  Inference rules
% 3.84/1.74  ----------------------
% 3.84/1.74  #Ref     : 0
% 3.84/1.74  #Sup     : 855
% 3.84/1.74  #Fact    : 0
% 3.84/1.74  #Define  : 0
% 3.84/1.74  #Split   : 2
% 3.84/1.74  #Chain   : 0
% 3.84/1.74  #Close   : 0
% 3.84/1.74  
% 3.84/1.74  Ordering : KBO
% 3.84/1.74  
% 3.84/1.74  Simplification rules
% 3.84/1.74  ----------------------
% 3.84/1.74  #Subsume      : 31
% 3.84/1.74  #Demod        : 734
% 3.84/1.74  #Tautology    : 612
% 3.84/1.74  #SimpNegUnit  : 6
% 3.84/1.74  #BackRed      : 3
% 3.84/1.74  
% 3.84/1.74  #Partial instantiations: 0
% 3.84/1.74  #Strategies tried      : 1
% 3.84/1.74  
% 3.84/1.74  Timing (in seconds)
% 3.84/1.74  ----------------------
% 3.84/1.75  Preprocessing        : 0.28
% 3.84/1.75  Parsing              : 0.16
% 3.84/1.75  CNF conversion       : 0.02
% 3.84/1.75  Main loop            : 0.68
% 3.84/1.75  Inferencing          : 0.21
% 3.84/1.75  Reduction            : 0.31
% 3.84/1.75  Demodulation         : 0.26
% 3.84/1.75  BG Simplification    : 0.02
% 3.84/1.75  Subsumption          : 0.10
% 3.84/1.75  Abstraction          : 0.03
% 3.84/1.75  MUC search           : 0.00
% 3.84/1.75  Cooper               : 0.00
% 3.84/1.75  Total                : 1.01
% 3.84/1.75  Index Insertion      : 0.00
% 3.84/1.75  Index Deletion       : 0.00
% 3.84/1.75  Index Matching       : 0.00
% 3.84/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
