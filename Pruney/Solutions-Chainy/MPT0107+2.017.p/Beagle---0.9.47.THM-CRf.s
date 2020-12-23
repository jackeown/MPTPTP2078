%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:55 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  75 expanded)
%              Number of equality atoms :   51 (  70 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_214,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_217,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,k4_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_20])).

tff(c_2947,plain,(
    ! [A_112,B_113] : k3_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k4_xboole_0(A_112,B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_217])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_229,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_214])).

tff(c_255,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_229])).

tff(c_261,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_18])).

tff(c_266,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_261])).

tff(c_236,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_242,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,k3_xboole_0(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_20])).

tff(c_1230,plain,(
    ! [A_76,B_77] : k3_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_242])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_248,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_1239,plain,(
    ! [A_76,B_77] : k4_xboole_0(k3_xboole_0(A_76,B_77),k3_xboole_0(A_76,B_77)) = k4_xboole_0(k3_xboole_0(A_76,B_77),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_248])).

tff(c_1277,plain,(
    ! [A_76,B_77] : k4_xboole_0(k3_xboole_0(A_76,B_77),A_76) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_1239])).

tff(c_3146,plain,(
    ! [A_116,B_117] : k4_xboole_0(k4_xboole_0(A_116,B_117),A_116) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2947,c_1277])).

tff(c_204,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_208,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_204,c_10])).

tff(c_3229,plain,(
    ! [A_116,B_117] : k2_xboole_0(k4_xboole_0(A_116,B_117),A_116) = A_116 ),
    inference(superposition,[status(thm),theory(equality)],[c_3146,c_208])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [B_31,A_32] : k5_xboole_0(B_31,A_32) = k5_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_22])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_462,plain,(
    ! [A_55,B_56,C_57] : k5_xboole_0(k5_xboole_0(A_55,B_56),C_57) = k5_xboole_0(A_55,k5_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_526,plain,(
    ! [A_23,C_57] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_57)) = k5_xboole_0(k1_xboole_0,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_462])).

tff(c_745,plain,(
    ! [A_64,C_65] : k5_xboole_0(A_64,k5_xboole_0(A_64,C_65)) = C_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_526])).

tff(c_811,plain,(
    ! [B_66,A_67] : k5_xboole_0(B_66,k5_xboole_0(A_67,B_66)) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_745])).

tff(c_4307,plain,(
    ! [B_135,A_136] : k5_xboole_0(k4_xboole_0(B_135,A_136),k2_xboole_0(A_136,B_135)) = A_136 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_811])).

tff(c_4427,plain,(
    ! [A_17,B_18] : k5_xboole_0(k3_xboole_0(A_17,B_18),k2_xboole_0(k4_xboole_0(A_17,B_18),A_17)) = k4_xboole_0(A_17,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4307])).

tff(c_4469,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3229,c_4427])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4469,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.06  
% 5.19/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.06  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.19/2.06  
% 5.19/2.06  %Foreground sorts:
% 5.19/2.06  
% 5.19/2.06  
% 5.19/2.06  %Background operators:
% 5.19/2.06  
% 5.19/2.06  
% 5.19/2.06  %Foreground operators:
% 5.19/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.19/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.19/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.19/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/2.06  
% 5.19/2.08  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.19/2.08  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.19/2.08  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.19/2.08  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.19/2.08  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.19/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.19/2.08  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.19/2.08  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.19/2.08  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.19/2.08  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.19/2.08  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.19/2.08  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.19/2.08  tff(f_58, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.19/2.08  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/2.08  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.19/2.08  tff(c_214, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.08  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.08  tff(c_217, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k3_xboole_0(A_42, k4_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_214, c_20])).
% 5.19/2.08  tff(c_2947, plain, (![A_112, B_113]: (k3_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k4_xboole_0(A_112, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_217])).
% 5.19/2.08  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.19/2.08  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.19/2.08  tff(c_229, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_214])).
% 5.19/2.08  tff(c_255, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k2_xboole_0(A_46, B_47))=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_229])).
% 5.19/2.08  tff(c_261, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(A_46, B_47))=k4_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_255, c_18])).
% 5.19/2.08  tff(c_266, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_261])).
% 5.19/2.08  tff(c_236, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.19/2.08  tff(c_242, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, k3_xboole_0(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_236, c_20])).
% 5.19/2.08  tff(c_1230, plain, (![A_76, B_77]: (k3_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_242])).
% 5.19/2.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.19/2.08  tff(c_248, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_236])).
% 5.19/2.08  tff(c_1239, plain, (![A_76, B_77]: (k4_xboole_0(k3_xboole_0(A_76, B_77), k3_xboole_0(A_76, B_77))=k4_xboole_0(k3_xboole_0(A_76, B_77), A_76))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_248])).
% 5.19/2.08  tff(c_1277, plain, (![A_76, B_77]: (k4_xboole_0(k3_xboole_0(A_76, B_77), A_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_1239])).
% 5.19/2.08  tff(c_3146, plain, (![A_116, B_117]: (k4_xboole_0(k4_xboole_0(A_116, B_117), A_116)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2947, c_1277])).
% 5.19/2.08  tff(c_204, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/2.08  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.19/2.08  tff(c_208, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_10])).
% 5.19/2.08  tff(c_3229, plain, (![A_116, B_117]: (k2_xboole_0(k4_xboole_0(A_116, B_117), A_116)=A_116)), inference(superposition, [status(thm), theory('equality')], [c_3146, c_208])).
% 5.19/2.08  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.19/2.08  tff(c_73, plain, (![B_31, A_32]: (k5_xboole_0(B_31, A_32)=k5_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/2.08  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.19/2.08  tff(c_89, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_73, c_22])).
% 5.19/2.08  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.19/2.08  tff(c_462, plain, (![A_55, B_56, C_57]: (k5_xboole_0(k5_xboole_0(A_55, B_56), C_57)=k5_xboole_0(A_55, k5_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.19/2.08  tff(c_526, plain, (![A_23, C_57]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_57))=k5_xboole_0(k1_xboole_0, C_57))), inference(superposition, [status(thm), theory('equality')], [c_26, c_462])).
% 5.19/2.08  tff(c_745, plain, (![A_64, C_65]: (k5_xboole_0(A_64, k5_xboole_0(A_64, C_65))=C_65)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_526])).
% 5.19/2.08  tff(c_811, plain, (![B_66, A_67]: (k5_xboole_0(B_66, k5_xboole_0(A_67, B_66))=A_67)), inference(superposition, [status(thm), theory('equality')], [c_4, c_745])).
% 5.19/2.08  tff(c_4307, plain, (![B_135, A_136]: (k5_xboole_0(k4_xboole_0(B_135, A_136), k2_xboole_0(A_136, B_135))=A_136)), inference(superposition, [status(thm), theory('equality')], [c_28, c_811])).
% 5.19/2.08  tff(c_4427, plain, (![A_17, B_18]: (k5_xboole_0(k3_xboole_0(A_17, B_18), k2_xboole_0(k4_xboole_0(A_17, B_18), A_17))=k4_xboole_0(A_17, B_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4307])).
% 5.19/2.08  tff(c_4469, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_3229, c_4427])).
% 5.19/2.08  tff(c_30, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.19/2.08  tff(c_6826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4469, c_30])).
% 5.19/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.08  
% 5.19/2.08  Inference rules
% 5.19/2.08  ----------------------
% 5.19/2.08  #Ref     : 0
% 5.19/2.08  #Sup     : 1681
% 5.19/2.08  #Fact    : 0
% 5.19/2.08  #Define  : 0
% 5.19/2.08  #Split   : 0
% 5.19/2.08  #Chain   : 0
% 5.19/2.08  #Close   : 0
% 5.19/2.08  
% 5.19/2.08  Ordering : KBO
% 5.19/2.08  
% 5.19/2.08  Simplification rules
% 5.19/2.08  ----------------------
% 5.19/2.08  #Subsume      : 28
% 5.19/2.08  #Demod        : 1660
% 5.19/2.08  #Tautology    : 1202
% 5.19/2.08  #SimpNegUnit  : 0
% 5.19/2.08  #BackRed      : 1
% 5.19/2.08  
% 5.19/2.08  #Partial instantiations: 0
% 5.19/2.08  #Strategies tried      : 1
% 5.19/2.08  
% 5.19/2.08  Timing (in seconds)
% 5.19/2.08  ----------------------
% 5.19/2.08  Preprocessing        : 0.30
% 5.19/2.08  Parsing              : 0.17
% 5.19/2.08  CNF conversion       : 0.02
% 5.19/2.08  Main loop            : 0.95
% 5.19/2.08  Inferencing          : 0.29
% 5.19/2.08  Reduction            : 0.45
% 5.19/2.08  Demodulation         : 0.39
% 5.19/2.08  BG Simplification    : 0.03
% 5.19/2.08  Subsumption          : 0.12
% 5.19/2.08  Abstraction          : 0.05
% 5.19/2.08  MUC search           : 0.00
% 5.19/2.08  Cooper               : 0.00
% 5.19/2.08  Total                : 1.29
% 5.19/2.08  Index Insertion      : 0.00
% 5.19/2.08  Index Deletion       : 0.00
% 5.19/2.08  Index Matching       : 0.00
% 5.19/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
