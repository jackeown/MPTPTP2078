%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 142 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 142 expanded)
%              Number of equality atoms :   60 ( 123 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_30])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_341,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_388,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_341])).

tff(c_401,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_388])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_344,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,k4_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_20])).

tff(c_389,plain,(
    ! [A_45,B_46] : k3_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_344])).

tff(c_107,plain,(
    ! [A_34,B_35] : k2_xboole_0(k3_xboole_0(A_34,B_35),k4_xboole_0(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_144,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_16])).

tff(c_509,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k4_xboole_0(A_49,B_50),k3_xboole_0(A_49,C_51)) = k4_xboole_0(A_49,k4_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_560,plain,(
    ! [A_8,C_51] : k4_xboole_0(A_8,k4_xboole_0(k1_xboole_0,C_51)) = k2_xboole_0(A_8,k3_xboole_0(A_8,C_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_509])).

tff(c_852,plain,(
    ! [A_59,C_60] : k2_xboole_0(A_59,k3_xboole_0(A_59,C_60)) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150,c_560])).

tff(c_871,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_852])).

tff(c_776,plain,(
    ! [A_57,B_58] : k3_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_344])).

tff(c_22,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_258,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k4_xboole_0(B_42,A_41)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,B_12)) = k2_xboole_0(k3_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_258])).

tff(c_304,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_287])).

tff(c_785,plain,(
    ! [A_57,B_58] : k2_xboole_0(k4_xboole_0(A_57,B_58),A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_304])).

tff(c_142,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_72])).

tff(c_548,plain,(
    ! [C_51] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_51)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_509])).

tff(c_972,plain,(
    ! [C_63] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_63)) = k3_xboole_0('#skF_1',C_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_548])).

tff(c_1020,plain,(
    ! [B_10] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',B_10)) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_972])).

tff(c_1219,plain,(
    ! [B_68] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',B_68)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1020])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k4_xboole_0(A_17,B_18),k3_xboole_0(A_17,C_19)) = k4_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1227,plain,(
    ! [B_18,B_68] : k4_xboole_0('#skF_1',k4_xboole_0(B_18,k2_xboole_0('#skF_3',B_68))) = k2_xboole_0(k4_xboole_0('#skF_1',B_18),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_24])).

tff(c_2078,plain,(
    ! [B_82,B_83] : k4_xboole_0('#skF_1',k4_xboole_0(B_82,k2_xboole_0('#skF_3',B_83))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_1227])).

tff(c_2126,plain,(
    ! [B_82] : k4_xboole_0('#skF_1',k4_xboole_0(B_82,'#skF_3')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_2078])).

tff(c_402,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_388])).

tff(c_407,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = k3_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_20])).

tff(c_457,plain,(
    ! [A_48] : k3_xboole_0(A_48,A_48) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_407])).

tff(c_473,plain,(
    ! [A_48] : k2_xboole_0(A_48,k4_xboole_0(A_48,A_48)) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_22])).

tff(c_495,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_473])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_551,plain,(
    ! [B_50] : k4_xboole_0('#skF_1',k4_xboole_0(B_50,k3_xboole_0('#skF_2','#skF_3'))) = k2_xboole_0(k4_xboole_0('#skF_1',B_50),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_509])).

tff(c_642,plain,(
    ! [B_54] : k4_xboole_0('#skF_1',k4_xboole_0(B_54,k3_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0('#skF_1',B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_551])).

tff(c_687,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_642])).

tff(c_2191,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_687])).

tff(c_2302,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2191,c_20])).

tff(c_2318,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_2302])).

tff(c_2320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.52  
% 3.05/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.52  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.05/1.52  
% 3.05/1.52  %Foreground sorts:
% 3.05/1.52  
% 3.05/1.52  
% 3.05/1.52  %Background operators:
% 3.05/1.52  
% 3.05/1.52  
% 3.05/1.52  %Foreground operators:
% 3.05/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.52  
% 3.36/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.36/1.53  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.36/1.53  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.36/1.53  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.36/1.53  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.36/1.53  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.36/1.53  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.36/1.53  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.36/1.53  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.36/1.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.36/1.53  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.36/1.53  tff(c_54, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.53  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.53  tff(c_58, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_30])).
% 3.36/1.53  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.53  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.53  tff(c_341, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.53  tff(c_388, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_341])).
% 3.36/1.53  tff(c_401, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_388])).
% 3.36/1.53  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.53  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.53  tff(c_344, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k3_xboole_0(A_45, k4_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_341, c_20])).
% 3.36/1.53  tff(c_389, plain, (![A_45, B_46]: (k3_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_344])).
% 3.36/1.53  tff(c_107, plain, (![A_34, B_35]: (k2_xboole_0(k3_xboole_0(A_34, B_35), k4_xboole_0(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_134, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_10, c_107])).
% 3.36/1.53  tff(c_144, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_134])).
% 3.36/1.53  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.53  tff(c_150, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_144, c_16])).
% 3.36/1.53  tff(c_509, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k3_xboole_0(A_49, C_51))=k4_xboole_0(A_49, k4_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.53  tff(c_560, plain, (![A_8, C_51]: (k4_xboole_0(A_8, k4_xboole_0(k1_xboole_0, C_51))=k2_xboole_0(A_8, k3_xboole_0(A_8, C_51)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_509])).
% 3.36/1.53  tff(c_852, plain, (![A_59, C_60]: (k2_xboole_0(A_59, k3_xboole_0(A_59, C_60))=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150, c_560])).
% 3.36/1.53  tff(c_871, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k4_xboole_0(A_45, B_46))=A_45)), inference(superposition, [status(thm), theory('equality')], [c_389, c_852])).
% 3.36/1.53  tff(c_776, plain, (![A_57, B_58]: (k3_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_344])).
% 3.36/1.53  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), k4_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_258, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k4_xboole_0(B_42, A_41))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.36/1.53  tff(c_287, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, B_12))=k2_xboole_0(k3_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_258])).
% 3.36/1.53  tff(c_304, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_287])).
% 3.36/1.53  tff(c_785, plain, (![A_57, B_58]: (k2_xboole_0(k4_xboole_0(A_57, B_58), A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_776, c_304])).
% 3.36/1.53  tff(c_142, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_134])).
% 3.36/1.53  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.53  tff(c_72, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.53  tff(c_76, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_72])).
% 3.36/1.53  tff(c_548, plain, (![C_51]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_51))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_51)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_509])).
% 3.36/1.53  tff(c_972, plain, (![C_63]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_63))=k3_xboole_0('#skF_1', C_63))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_548])).
% 3.36/1.53  tff(c_1020, plain, (![B_10]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', B_10))=k4_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_972])).
% 3.36/1.53  tff(c_1219, plain, (![B_68]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', B_68))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1020])).
% 3.36/1.53  tff(c_24, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k4_xboole_0(A_17, B_18), k3_xboole_0(A_17, C_19))=k4_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.53  tff(c_1227, plain, (![B_18, B_68]: (k4_xboole_0('#skF_1', k4_xboole_0(B_18, k2_xboole_0('#skF_3', B_68)))=k2_xboole_0(k4_xboole_0('#skF_1', B_18), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1219, c_24])).
% 3.36/1.53  tff(c_2078, plain, (![B_82, B_83]: (k4_xboole_0('#skF_1', k4_xboole_0(B_82, k2_xboole_0('#skF_3', B_83)))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_785, c_1227])).
% 3.36/1.53  tff(c_2126, plain, (![B_82]: (k4_xboole_0('#skF_1', k4_xboole_0(B_82, '#skF_3'))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_871, c_2078])).
% 3.36/1.53  tff(c_402, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_388])).
% 3.36/1.53  tff(c_407, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=k3_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_402, c_20])).
% 3.36/1.53  tff(c_457, plain, (![A_48]: (k3_xboole_0(A_48, A_48)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_407])).
% 3.36/1.53  tff(c_473, plain, (![A_48]: (k2_xboole_0(A_48, k4_xboole_0(A_48, A_48))=A_48)), inference(superposition, [status(thm), theory('equality')], [c_457, c_22])).
% 3.36/1.53  tff(c_495, plain, (![A_48]: (k2_xboole_0(A_48, k1_xboole_0)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_401, c_473])).
% 3.36/1.53  tff(c_26, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.53  tff(c_59, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.53  tff(c_67, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_59])).
% 3.36/1.53  tff(c_551, plain, (![B_50]: (k4_xboole_0('#skF_1', k4_xboole_0(B_50, k3_xboole_0('#skF_2', '#skF_3')))=k2_xboole_0(k4_xboole_0('#skF_1', B_50), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_67, c_509])).
% 3.36/1.53  tff(c_642, plain, (![B_54]: (k4_xboole_0('#skF_1', k4_xboole_0(B_54, k3_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0('#skF_1', B_54))), inference(demodulation, [status(thm), theory('equality')], [c_495, c_551])).
% 3.36/1.53  tff(c_687, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_642])).
% 3.36/1.53  tff(c_2191, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_687])).
% 3.36/1.53  tff(c_2302, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2191, c_20])).
% 3.36/1.53  tff(c_2318, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_401, c_2302])).
% 3.36/1.53  tff(c_2320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2318])).
% 3.36/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  Inference rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Ref     : 0
% 3.36/1.53  #Sup     : 559
% 3.36/1.53  #Fact    : 0
% 3.36/1.53  #Define  : 0
% 3.36/1.53  #Split   : 0
% 3.36/1.53  #Chain   : 0
% 3.36/1.53  #Close   : 0
% 3.36/1.53  
% 3.36/1.53  Ordering : KBO
% 3.36/1.53  
% 3.36/1.53  Simplification rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Subsume      : 0
% 3.36/1.53  #Demod        : 566
% 3.36/1.53  #Tautology    : 463
% 3.36/1.53  #SimpNegUnit  : 1
% 3.36/1.53  #BackRed      : 4
% 3.36/1.53  
% 3.36/1.53  #Partial instantiations: 0
% 3.36/1.53  #Strategies tried      : 1
% 3.36/1.53  
% 3.36/1.53  Timing (in seconds)
% 3.36/1.53  ----------------------
% 3.36/1.54  Preprocessing        : 0.26
% 3.36/1.54  Parsing              : 0.14
% 3.36/1.54  CNF conversion       : 0.02
% 3.36/1.54  Main loop            : 0.48
% 3.36/1.54  Inferencing          : 0.18
% 3.36/1.54  Reduction            : 0.20
% 3.36/1.54  Demodulation         : 0.16
% 3.36/1.54  BG Simplification    : 0.02
% 3.36/1.54  Subsumption          : 0.06
% 3.36/1.54  Abstraction          : 0.03
% 3.36/1.54  MUC search           : 0.00
% 3.36/1.54  Cooper               : 0.00
% 3.36/1.54  Total                : 0.77
% 3.36/1.54  Index Insertion      : 0.00
% 3.36/1.54  Index Deletion       : 0.00
% 3.36/1.54  Index Matching       : 0.00
% 3.36/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
